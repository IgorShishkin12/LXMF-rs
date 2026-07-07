use std::sync::atomic::{AtomicU64, Ordering};

pub const FEND: u8 = 0xC0;
pub const FESC: u8 = 0xDB;
pub const TFEND: u8 = 0xDC;
pub const TFESC: u8 = 0xDD;

pub const CMD_DATA: u8 = 0x00;
pub const CMD_TXDELAY: u8 = 0x01;
pub const CMD_P: u8 = 0x02;
pub const CMD_SLOTTIME: u8 = 0x03;
pub const CMD_TXTAIL: u8 = 0x04;
pub const CMD_FULLDUPLEX: u8 = 0x05;
pub const CMD_SETHARDWARE: u8 = 0x06;
pub const CMD_READY: u8 = 0x0F;
pub const CMD_RETURN: u8 = 0xFF;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KissCommand {
    Ready,
    Unknown(u8, Vec<u8>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KissFrame {
    Data(Vec<u8>),
    Command(KissCommand),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KissDecodeError {
    MalformedEscape(u8),
    FrameTooLarge { limit: usize, actual: usize },
}

#[must_use]
pub fn encode_data_frame(payload: &[u8]) -> Vec<u8> {
    encode_command_frame(CMD_DATA, payload)
}

#[must_use]
pub fn encode_command_frame(command: u8, payload: &[u8]) -> Vec<u8> {
    let mut frame = Vec::with_capacity(payload.len() + 3);
    frame.push(FEND);
    frame.push(command);
    encode_payload(payload, &mut frame);
    frame.push(FEND);
    frame
}

fn encode_payload(payload: &[u8], frame: &mut Vec<u8>) {
    for byte in payload {
        match *byte {
            FEND => frame.extend_from_slice(&[FESC, TFEND]),
            FESC => frame.extend_from_slice(&[FESC, TFESC]),
            byte => frame.push(byte),
        }
    }
}

pub fn decode_frames(
    input: &[u8],
    max_payload_len: usize,
) -> Result<Vec<KissFrame>, KissDecodeError> {
    let mut decoder = KissStreamDecoder::new(max_payload_len);
    decoder.push_bytes(input)
}

#[derive(Debug, Clone)]
pub struct KissStreamDecoder {
    max_payload_len: usize,
    frame: Vec<u8>,
    strip_command_port_nibble: bool,
}

impl KissStreamDecoder {
    #[must_use]
    pub fn new(max_payload_len: usize) -> Self {
        Self { max_payload_len, frame: Vec::new(), strip_command_port_nibble: false }
    }

    #[must_use]
    pub const fn with_command_port_nibble_stripping(mut self, enabled: bool) -> Self {
        self.strip_command_port_nibble = enabled;
        self
    }

    #[must_use]
    pub fn has_partial_frame(&self) -> bool {
        !self.frame.is_empty()
    }

    pub fn clear_partial_frame(&mut self) {
        self.frame.clear();
    }

    pub fn push_bytes(&mut self, input: &[u8]) -> Result<Vec<KissFrame>, KissDecodeError> {
        let mut frames = Vec::new();
        for byte in input {
            if *byte == FEND {
                if !self.frame.is_empty() {
                    let raw = std::mem::take(&mut self.frame);
                    frames.push(decode_frame(
                        &raw,
                        self.max_payload_len,
                        self.strip_command_port_nibble,
                    ));
                }
                continue;
            }
            // OOM guard: cap the accumulated frame. Warn once, on the byte that
            // hits the cap; further bytes are dropped until the next FEND, so the
            // decoded message comes back truncated rather than growing unbounded.
            if self.frame.len() < MAX_MESSAGE_LEN {
                self.frame.push(*byte);
                if self.frame.len() == MAX_MESSAGE_LEN {
                    log::warn!(
                        "KISS frame reached the {MAX_MESSAGE_LEN} B hard cap; dropping further bytes \
                         and returning the message truncated (out-of-memory guard)"
                    );
                }
            }
        }
        Ok(frames)
    }
}

fn decode_frame(raw: &[u8], max_payload_len: usize, strip_command_port_nibble: bool) -> KissFrame {
    let Some((&command, payload)) = raw.split_first() else {
        unreachable!("empty KISS frames are filtered before decode");
    };
    let command = if strip_command_port_nibble { command & 0x0F } else { command };
    let payload = decode_payload(payload, max_payload_len);
    match command {
        CMD_DATA => KissFrame::Data(payload),
        CMD_READY => KissFrame::Command(KissCommand::Ready),
        command => KissFrame::Command(KissCommand::Unknown(command, payload)),
    }
}

/// Number of decoded KISS payloads observed that exceeded the interface MTU
/// hint. Tracked process-wide purely to escalate a persistent mismatch to a
/// single WARN — it is a diagnostic, not a limit.
static OVERSIZED_PAYLOAD_COUNT: AtomicU64 = AtomicU64::new(0);

/// After this many oversized payloads, emit one WARN: a steady stream of them
/// means the two link endpoints almost certainly disagree on their interface MTU.
const OVERSIZED_WARN_THRESHOLD: u64 = 100;

/// Hard upper bound on a single accumulated KISS frame. Unlike the interface MTU
/// (a hint we no longer enforce), this is an absolute limit: a malicious peer
/// that never sends FEND would otherwise grow the frame buffer without bound and
/// exhaust memory. Bytes past this are dropped so a frame stays O(this) in size.
/// Legitimate Reticulum packets are well under 1 KiB, so this never trims real
/// traffic.
const MAX_MESSAGE_LEN: usize = 65_535;

fn decode_payload(input: &[u8], max_payload_len: usize) -> Vec<u8> {
    let mut output = Vec::with_capacity(input.len());
    let mut index = 0;
    while index < input.len() {
        let byte = input[index];
        if byte == FESC {
            let Some(escaped) = input.get(index + 1).copied() else {
                break;
            };
            let decoded = match escaped {
                TFEND => FEND,
                TFESC => FESC,
                value => value,
            };
            output.push(decoded);
            index += 2;
        } else {
            output.push(byte);
            index += 1;
        }
    }

    // The interface MTU is a host-side hint, not a wire limit. A frame that
    // crossed the link intact must be decoded in full: silently truncating it to
    // our local MTU corrupts otherwise-valid packets (they then fail to
    // decrypt/parse downstream, which is exactly the failure this replaces). We
    // still *check* the MTU and surface the mismatch, but never drop bytes.
    if output.len() > max_payload_len {
        report_oversized_payload(output.len(), max_payload_len);
    }

    output
}

/// Trace every over-MTU payload; once enough have accumulated, warn once that the
/// endpoints' interface MTUs are almost certainly mismatched.
fn report_oversized_payload(actual: usize, mtu: usize) {
    log::trace!(
        "KISS frame payload {actual} B exceeds interface MTU {mtu} B; decoding in full (not truncating)"
    );
    let seen = OVERSIZED_PAYLOAD_COUNT.fetch_add(1, Ordering::Relaxed) + 1;
    if seen == OVERSIZED_WARN_THRESHOLD {
        log::warn!(
            "KISS frame payload has exceeded the interface MTU for {OVERSIZED_WARN_THRESHOLD}+ frames; \
             the two link endpoints likely have mismatched interface MTUs (see earlier TRACE lines)"
        );
    }
}
