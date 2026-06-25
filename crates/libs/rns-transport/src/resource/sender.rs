const MAX_AWAITING_PROOF_RETRIES: u8 = 3;

#[derive(Debug, Clone)]
struct ResourceSender {
    link_id: AddressHash,
    resource_hash: Hash,
    parts: Vec<Vec<u8>>,
    sent_parts: Vec<bool>,
    map_hashes: Vec<[u8; MAPHASH_LEN]>,
    hashmap_segment_len: usize,
    /// Hashes carried per `ResourceHashUpdate` packet (segment-aligned multiple of
    /// `hashmap_segment_len`). Lets one update deliver many segments at once.
    hashmap_update_len: usize,
    expected_proof: Hash,
    advertisement_packet: Packet,
    last_activity: Instant,
    adv_sent: Instant,
    last_part_sent: Instant,
    max_retries: u8,
    retries_left: u8,
    status: ResourceStatus,
    /// Minimum time between advertisement retransmits — at least the link RTT so the
    /// receiver has time to respond before the sender retries.
    min_retry_interval: Duration,
}

enum OutboundResourcePoll {
    None,
    Send(Box<Packet>),
    Failed,
}

impl ResourceSender {
    fn new(link: &Link, data: Vec<u8>, metadata: Option<Vec<u8>>) -> Result<Self, RnsError> {
        Self::new_with_mtu(link, data, metadata, DEFAULT_RESOURCE_INTERFACE_MTU)
    }

    fn new_with_mtu(
        link: &Link,
        data: Vec<u8>,
        metadata: Option<Vec<u8>>,
        interface_mtu: usize,
    ) -> Result<Self, RnsError> {
        Self::new_with_options_mtu(link, data, metadata, None, false, interface_mtu)
    }

    pub(super) fn new_with_options(
        link: &Link,
        data: Vec<u8>,
        metadata: Option<Vec<u8>>,
        request_id: Option<Vec<u8>>,
        is_response: bool,
    ) -> Result<Self, RnsError> {
        Self::new_with_options_mtu(
            link,
            data,
            metadata,
            request_id,
            is_response,
            DEFAULT_RESOURCE_INTERFACE_MTU,
        )
    }

    pub(super) fn new_with_options_mtu(
        link: &Link,
        data: Vec<u8>,
        metadata: Option<Vec<u8>>,
        request_id: Option<Vec<u8>>,
        is_response: bool,
        interface_mtu: usize,
    ) -> Result<Self, RnsError> {
        let resource_mdu = resource_packet_mdu_for_mtu(interface_mtu)?;
        let hashmap_segment_len = resource_hashmap_segment_len_for_mtu(interface_mtu)?;
        // Hash-update packets carry many more hashes than the advertisement; round
        // down to a whole number of segments so update blocks stay segment-aligned
        // (the receiver indexes them at `segment * segment_len`).
        let hashmap_update_len = (resource_hashmap_update_len_for_mtu(interface_mtu)?
            / hashmap_segment_len)
            .max(1)
            * hashmap_segment_len;
        let has_metadata = metadata.is_some();
        let has_request_id = request_id.is_some();
        let metadata_prefix = if let Some(payload) = metadata.as_ref() {
            if payload.len() > METADATA_MAX_SIZE {
                return Err(RnsError::InvalidArgument);
            }
            let size = payload.len() as u32;
            let size_bytes = size.to_be_bytes();
            let mut prefix = Vec::with_capacity(3 + payload.len());
            prefix.extend_from_slice(&size_bytes[1..]);
            prefix.extend_from_slice(payload);
            prefix
        } else {
            Vec::new()
        };
        let mut combined = metadata_prefix.clone();
        combined.extend_from_slice(&data);
        let random_hash = random_bytes::<RANDOM_HASH_SIZE>();
        let data_size = combined.len() as u64;
        let mut hasher = sha2::Sha256::new();
        hasher.update(&combined);
        hasher.update(random_hash);
        let resource_hash = Hash::new(copy_hash(&hasher.finalize())?);

        let mut proof_hasher = sha2::Sha256::new();
        proof_hasher.update(&combined);
        proof_hasher.update(resource_hash.as_slice());
        let expected_proof = Hash::new(copy_hash(&proof_hasher.finalize())?);

        let mut prefix = random_bytes::<RANDOM_HASH_SIZE>().to_vec();
        prefix.extend_from_slice(&combined);

        let mut cipher_buf = vec![0u8; prefix.len() + 128];
        let cipher = link.encrypt(&prefix, &mut cipher_buf).map_err(|_| RnsError::CryptoError)?;
        let cipher_text = cipher.to_vec();

        let mut parts = Vec::new();
        for chunk in cipher_text.chunks(resource_mdu) {
            parts.push(chunk.to_vec());
        }

        let mut map_hashes = Vec::with_capacity(parts.len());
        for part in &parts {
            map_hashes.push(map_hash(part, &random_hash));
        }

        let advertisement = ResourceAdvertisement {
            transfer_size: parts.iter().map(|part| part.len() as u64).sum(),
            data_size,
            parts: parts.len() as u32,
            hash: resource_hash,
            random_hash,
            original_hash: resource_hash,
            segment_index: 1,
            total_segments: 1,
            request_id: request_id.map(ByteBuf::from),
            flags: {
                let mut flags = FLAG_ENCRYPTED;
                if has_metadata {
                    flags |= FLAG_METADATA;
                }
                if has_request_id {
                    flags |= if is_response { FLAG_RESPONSE } else { FLAG_REQUEST };
                }
                flags
            },
            hashmap: slice_hashmap_segment(&map_hashes, 0, hashmap_segment_len),
        };
        let advertisement_packet = build_link_packet(
            link,
            PacketType::Data,
            PacketContext::ResourceAdvrtisement,
            &advertisement.pack()?,
        )?;
        let now = Instant::now();
        // Python Reticulum uses rtt*2 for the advertisement retry interval, which
        // works when link.rtt() reflects data-packet latency.  Our link.rtt() is
        // the handshake RTT (small packets, no queue delay) and understates the
        // actual round-trip for larger packets on congested links such as LoRa.
        // The link's stale-detection window — rtt × KEEPALIVE_TIMEOUT_FACTOR +
        // STALE_GRACE_SECS — already accounts for link characteristics and
        // represents the "maximum time to wait for any response before declaring
        // the link stale".  Using 2× that window as the minimum retry interval
        // ensures we give the receiver the full stale window to respond before
        // we decide the advertisement was lost.
        //
        // When rtt == 0 the link has not activated yet; stale_timeout() collapses
        // to just STALE_GRACE_SECS (5 s), giving a 10 s floor that is wrong for
        // non-slow links.  In that case we fall back to the default interval.
        let min_retry_interval = if link.rtt() == Duration::ZERO {
            Duration::from_secs(DEFAULT_RESOURCE_RETRY_INTERVAL_SECS)
        } else {
            Duration::from_secs(DEFAULT_RESOURCE_RETRY_INTERVAL_SECS).max(link.stale_timeout() * 2)
        };

        Ok(Self {
            link_id: *link.id(),
            resource_hash,
            parts,
            sent_parts: vec![false; map_hashes.len()],
            map_hashes,
            hashmap_segment_len,
            hashmap_update_len,
            expected_proof,
            advertisement_packet,
            last_activity: now,
            adv_sent: now,
            last_part_sent: now,
            max_retries: 0,
            retries_left: 0,
            status: ResourceStatus::None,
            min_retry_interval,
        })
    }

    fn advertisement_packet(&self) -> Packet {
        self.advertisement_packet.clone()
    }

    /// Build a `ResourceHashUpdate` packet delivering up to `hashmap_update_len`
    /// map-hashes starting at hash index `start`. `start` must be a multiple of
    /// `hashmap_segment_len` so the receiver applies the block at the right offset.
    /// Returns `None` when `start` is past the end or the packet cannot be built.
    fn build_hashmap_update(&self, link: &Link, start: usize) -> Option<Packet> {
        if start >= self.map_hashes.len() {
            return None;
        }
        let hashmap = slice_hashmap_range(&self.map_hashes, start, self.hashmap_update_len);
        if hashmap.is_empty() {
            return None;
        }
        let update = ResourceHashUpdate {
            resource_hash: self.resource_hash,
            segment: (start / self.hashmap_segment_len) as u32,
            hashmap,
        };
        let payload = update.encode().ok()?;
        build_link_packet(link, PacketType::Data, PacketContext::ResourceHashUpdate, &payload).ok()
    }

    fn mark_advertised(&mut self, retry_limit: u8) {
        let now = Instant::now();
        self.last_activity = now;
        self.adv_sent = now;
        self.last_part_sent = now;
        self.max_retries = retry_limit;
        self.retries_left = retry_limit.min(DEFAULT_RESOURCE_MAX_ADV_RETRIES);
        self.status = ResourceStatus::Advertised;
    }

    fn poll(&mut self, now: Instant, retry_interval: Duration) -> OutboundResourcePoll {
        let retry_interval = retry_interval.max(self.min_retry_interval);
        match self.status {
            ResourceStatus::Advertised => {
                if now.duration_since(self.adv_sent) < retry_interval {
                    return OutboundResourcePoll::None;
                }
                if self.retries_left == 0 {
                    log::warn!(
                        "resource sender: advertisement retries exhausted hash={} link={} max_retries={}",
                        self.resource_hash,
                        self.link_id,
                        self.max_retries,
                    );
                    return OutboundResourcePoll::Failed;
                }
                log::debug!(
                    "resource sender: retransmitting advertisement hash={} link={} retries_left={}",
                    self.resource_hash,
                    self.link_id,
                    self.retries_left,
                );
                self.retries_left -= 1;
                self.last_activity = now;
                self.adv_sent = now;
                OutboundResourcePoll::Send(Box::new(self.advertisement_packet()))
            }
            ResourceStatus::Transferring => {
                if now.duration_since(self.last_activity) < retry_interval {
                    return OutboundResourcePoll::None;
                }
                if self.retries_left == 0 {
                    log::warn!(
                        "resource sender: transfer timed out (no request received within {:.0}s) hash={} link={}",
                        retry_interval.as_secs_f32(), self.resource_hash, self.link_id,
                    );
                    return OutboundResourcePoll::Failed;
                }
                log::debug!(
                    "resource sender: transfer idle {:.0}s, retries_left={} hash={} link={}",
                    now.duration_since(self.last_activity).as_secs_f32(),
                    self.retries_left, self.resource_hash, self.link_id,
                );
                self.retries_left -= 1;
                self.last_activity = now;
                OutboundResourcePoll::None
            }
            ResourceStatus::AwaitingProof => {
                if now.duration_since(self.last_part_sent) < retry_interval {
                    return OutboundResourcePoll::None;
                }
                if self.retries_left == 0 {
                    return OutboundResourcePoll::Failed;
                }
                self.retries_left -= 1;
                self.last_part_sent = now;
                OutboundResourcePoll::None
            }
            ResourceStatus::Failed => OutboundResourcePoll::Failed,
            _ => OutboundResourcePoll::None,
        }
    }

    fn handle_request_into(
        &mut self,
        request: &ResourceRequest,
        link: &Link,
        packets: &mut Vec<Packet>,
    ) {
        if request.resource_hash != self.resource_hash {
            return;
        }

        let mut sent_any = false;
        let mut scratch_packet = Packet::default();
        for hash in &request.requested_hashes {
            if let Some(index) = self.map_hashes.iter().position(|entry| entry == hash) {
                if let Some(part) = self.parts.get(index) {
                    if build_link_packet_into(
                        link,
                        PacketType::Data,
                        PacketContext::Resource,
                        part,
                        &mut scratch_packet,
                    )
                    .is_ok()
                    {
                        self.sent_parts[index] = true;
                        sent_any = true;
                        packets.push(scratch_packet.clone());
                    } else {
                        self.status = ResourceStatus::Failed;
                        return;
                    }
                }
            } else {
                log::debug!(
                    "[resource-diag] request_part_miss hash={} requested_map_hash={:02x}{:02x}{:02x}{:02x}",
                    self.resource_hash, hash[0], hash[1], hash[2], hash[3]
                );
            }
        }
        log::debug!(
            "[resource-diag] request_parts_built hash={} requested={} built={} sent_any={}",
            self.resource_hash,
            request.requested_hashes.len(),
            packets.len(),
            sent_any
        );

        if request.hashmap_exhausted {
            if let Some(last_hash) = request.last_map_hash {
                if let Some(last_index) =
                    self.map_hashes.iter().position(|entry| *entry == last_hash)
                {
                    let next_segment = (last_index / self.hashmap_segment_len) + 1;
                    let start = next_segment * self.hashmap_segment_len;
                    if let Some(packet) = self.build_hashmap_update(link, start) {
                        packets.push(packet);
                    }
                }
            }
        }

        if self.status.accepts_transfer_activity() {
            let now = Instant::now();
            let prev_status = self.status;
            self.last_activity = now;
            self.retries_left = self.max_retries;
            if sent_any {
                self.last_part_sent = now;
            }
            if self.sent_parts.iter().all(|sent| *sent) {
                self.status = ResourceStatus::AwaitingProof;
                self.retries_left = self.max_retries.clamp(1, MAX_AWAITING_PROOF_RETRIES);
            } else {
                self.status = ResourceStatus::Transferring;
            }
            if prev_status == ResourceStatus::Advertised && self.status == ResourceStatus::Transferring {
                log::info!(
                    "resource sender: first request received, transfer started hash={} link={} parts={}",
                    self.resource_hash, self.link_id, self.parts.len(),
                );
                // Proactively push the rest of the part hashmap. The advertisement
                // only carried the first segment (a couple of hashes on a small
                // MTU); without this the receiver would have to round-trip once per
                // segment to learn the remaining hashes. Sending them up front lets
                // it request a full window immediately. Lost updates are still
                // recovered reactively via the `hashmap_exhausted` branch above.
                let mut start = self.hashmap_segment_len;
                while start < self.map_hashes.len() {
                    if let Some(packet) = self.build_hashmap_update(link, start) {
                        packets.push(packet);
                    }
                    start += self.hashmap_update_len;
                }
            }
        }
    }

    fn handle_proof(&mut self, proof: &ResourceProof) -> bool {
        if proof.resource_hash != self.resource_hash {
            return false;
        }
        if proof.proof == self.expected_proof {
            self.status = ResourceStatus::Complete;
            return true;
        }
        false
    }
}
