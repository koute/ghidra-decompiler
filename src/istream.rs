#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Basefield {
    Auto,
    Dec,
    Hex,
    Oct,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IntegerExtraction {
    pub value: u64,
    pub failed: bool,
    pub consumed: usize,
}

fn is_space(byte: u8) -> bool {
    matches!(byte, b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r')
}

fn digit_value(byte: u8, base: u32) -> Option<u64> {
    let value = match byte {
        b'0'..=b'9' => (byte - b'0') as u32,
        b'a'..=b'f' if base == 16 => (byte - b'a') as u32 + 10,
        b'A'..=b'F' if base == 16 => (byte - b'A') as u32 + 10,
        _ => return None,
    };
    if value < base { Some(value as u64) } else { None }
}

fn extract_integer(text: &[u8], basefield: Basefield, is_signed: bool, type_max: u64) -> Option<IntegerExtraction> {
    let mut pos = 0;
    while pos < text.len() && is_space(text[pos]) {
        pos += 1;
    }
    if pos == text.len() {
        return None;
    }
    let mut negative = false;
    if text[pos] == b'-' || text[pos] == b'+' {
        negative = text[pos] == b'-';
        pos += 1;
    }
    let mut base: u32 = match basefield {
        Basefield::Oct => 8,
        Basefield::Hex => 16,
        _ => 10,
    };
    let mut found_zero = false;
    let mut digit_count = 0usize;
    while pos < text.len() {
        let byte = text[pos];
        if byte == b'.' {
            break;
        } else if byte == b'0' && (!found_zero || base == 10) {
            found_zero = true;
            digit_count += 1;
            if basefield == Basefield::Auto {
                base = 8;
            }
            if base == 8 {
                digit_count = 0;
            }
        } else if found_zero && (byte == b'x' || byte == b'X') {
            if basefield == Basefield::Auto {
                base = 16;
            }
            if base == 16 {
                found_zero = false;
                digit_count = 0;
            } else {
                break;
            }
        } else {
            break;
        }
        pos += 1;
        if pos < text.len() && !found_zero {
            break;
        }
    }
    let max_magnitude = if negative && is_signed {
        type_max.wrapping_add(1)
    } else {
        type_max
    };
    let small_max = max_magnitude / base as u64;
    let mut result: u64 = 0;
    let mut overflow = false;
    while pos < text.len() {
        let Some(digit) = digit_value(text[pos], base) else {
            break;
        };
        if result > small_max {
            overflow = true;
        } else {
            result = result.wrapping_mul(base as u64);
            overflow |= result > max_magnitude.wrapping_sub(digit);
            result = result.wrapping_add(digit);
            digit_count += 1;
        }
        pos += 1;
    }
    if digit_count == 0 && !found_zero {
        return Some(IntegerExtraction {
            value: 0,
            failed: true,
            consumed: pos,
        });
    }
    if overflow {
        let value = if negative && is_signed {
            type_max.wrapping_add(1).wrapping_neg()
        } else {
            type_max
        };
        return Some(IntegerExtraction {
            value,
            failed: true,
            consumed: pos,
        });
    }
    let value = if negative { result.wrapping_neg() } else { result };
    Some(IntegerExtraction {
        value,
        failed: false,
        consumed: pos,
    })
}

pub fn extract_u64(text: &str, basefield: Basefield) -> Option<IntegerExtraction> {
    extract_integer(text.as_bytes(), basefield, false, u64::MAX)
}

pub fn extract_i64(text: &str, basefield: Basefield) -> Option<IntegerExtraction> {
    extract_integer(text.as_bytes(), basefield, true, i64::MAX as u64)
}

pub fn extract_u32(text: &str, basefield: Basefield) -> Option<IntegerExtraction> {
    extract_integer(text.as_bytes(), basefield, false, u32::MAX as u64)
}

pub fn extract_i32(text: &str, basefield: Basefield) -> Option<IntegerExtraction> {
    extract_integer(text.as_bytes(), basefield, true, i32::MAX as u64)
}

pub fn read_u64(text: &str, basefield: Basefield, initial: u64) -> u64 {
    extract_u64(text, basefield).map_or(initial, |extraction| extraction.value)
}

pub fn read_i64(text: &str, basefield: Basefield, initial: i64) -> i64 {
    extract_i64(text, basefield).map_or(initial, |extraction| extraction.value as i64)
}

pub fn read_u32(text: &str, basefield: Basefield, initial: u32) -> u32 {
    extract_u32(text, basefield).map_or(initial, |extraction| extraction.value as u32)
}

pub fn read_i32(text: &str, basefield: Basefield, initial: i32) -> i32 {
    extract_i32(text, basefield).map_or(initial, |extraction| extraction.value as u32 as i32)
}

pub fn strtoul(text: &[u8], base: u32) -> (u64, usize) {
    let mut pos = 0;
    while pos < text.len() && is_space(text[pos]) {
        pos += 1;
    }
    let mut negative = false;
    if pos < text.len() && (text[pos] == b'-' || text[pos] == b'+') {
        negative = text[pos] == b'-';
        pos += 1;
    }
    let mut radix = base;
    let has_hex_prefix = pos + 1 < text.len()
        && text[pos] == b'0'
        && (text[pos + 1] == b'x' || text[pos + 1] == b'X')
        && pos + 2 < text.len()
        && digit_value(text[pos + 2], 16).is_some();
    if (radix == 0 || radix == 16) && has_hex_prefix {
        pos += 2;
        radix = 16;
    } else if radix == 0 {
        radix = if pos < text.len() && text[pos] == b'0' { 8 } else { 10 };
    }
    let start = pos;
    let mut result: u64 = 0;
    let mut overflow = false;
    while pos < text.len() {
        let Some(digit) = digit_value(text[pos], radix) else {
            break;
        };
        match result
            .checked_mul(radix as u64)
            .and_then(|product| product.checked_add(digit))
        {
            Some(next) => result = next,
            None => overflow = true,
        }
        pos += 1;
    }
    if pos == start {
        return (0, 0);
    }
    if overflow {
        return (u64::MAX, pos);
    }
    (if negative { result.wrapping_neg() } else { result }, pos)
}
