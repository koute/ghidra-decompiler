use crate::address::{calc_mask, count_leading_zeros, sign_extend};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FloatClass {
    Normalized = 0,
    Infinity = 1,
    Zero = 2,
    Nan = 3,
    Denormalized = 4,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FloatFormat {
    size: i32,
    signbit_pos: i32,
    frac_pos: i32,
    frac_size: i32,
    exp_pos: i32,
    exp_size: i32,
    bias: i32,
    maxexponent: i32,
    decimal_min_precision: i32,
    decimal_max_precision: i32,
    jbitimplied: bool,
}

pub fn ldexp(value: f64, exponent: i32) -> f64 {
    let two_1023 = f64::from_bits(0x7fe0000000000000);
    let two_53 = f64::from_bits(0x4340000000000000);
    let two_minus_1022 = f64::from_bits(0x0010000000000000);
    let mut scaled = value;
    let mut power = exponent;
    if power > 1023 {
        scaled *= two_1023;
        power -= 1023;
        if power > 1023 {
            scaled *= two_1023;
            power -= 1023;
            if power > 1023 {
                power = 1023;
            }
        }
    } else if power < -1022 {
        scaled *= two_minus_1022 * two_53;
        power += 1022 - 53;
        if power < -1022 {
            scaled *= two_minus_1022 * two_53;
            power += 1022 - 53;
            if power < -1022 {
                power = -1022;
            }
        }
    }
    scaled * f64::from_bits(((0x3ff + power) as u64) << 52)
}

pub fn frexp(value: f64) -> (f64, i32) {
    let bits = value.to_bits();
    let biased = ((bits >> 52) & 0x7ff) as i32;
    if biased == 0 {
        if value != 0.0 {
            let (mantissa, exponent) = frexp(value * f64::from_bits(0x43f0000000000000));
            return (mantissa, exponent - 64);
        }
        return (value, 0);
    }
    if biased == 0x7ff {
        return (value, 0);
    }
    let exponent = biased - 0x3fe;
    let mantissa = f64::from_bits((bits & 0x800fffffffffffff) | 0x3fe0000000000000);
    (mantissa, exponent)
}

fn nonfinite_text(value: f64) -> Option<String> {
    if value.is_nan() {
        return Some(if value.is_sign_negative() {
            "-nan".to_string()
        } else {
            "nan".to_string()
        });
    }
    if value.is_infinite() {
        return Some(if value < 0.0 {
            "-inf".to_string()
        } else {
            "inf".to_string()
        });
    }
    None
}

fn split_exponent(text: &str) -> (&str, i32) {
    let pos = text.find('e').expect("exponent marker in scientific format");
    let exponent: i32 = text[pos + 1..].parse().expect("exponent digits in scientific format");
    (&text[..pos], exponent)
}

fn exponent_suffix(exponent: i32) -> String {
    let sign = if exponent < 0 { '-' } else { '+' };
    format!("e{}{:02}", sign, exponent.unsigned_abs())
}

pub fn format_float_scientific(value: f64, precision: usize) -> String {
    if let Some(text) = nonfinite_text(value) {
        return text;
    }
    let raw = format!("{:.*e}", precision, value);
    let (mantissa, exponent) = split_exponent(&raw);
    format!("{}{}", mantissa, exponent_suffix(exponent))
}

fn strip_trailing_zeros(text: &str) -> &str {
    if !text.contains('.') {
        return text;
    }
    let trimmed = text.trim_end_matches('0');
    trimmed.strip_suffix('.').unwrap_or(trimmed)
}

pub fn format_float_general(value: f64, precision: usize) -> String {
    if let Some(text) = nonfinite_text(value) {
        return text;
    }
    let prec = if precision == 0 { 1 } else { precision };
    let raw = format!("{:.*e}", prec - 1, value);
    let (mantissa, exponent) = split_exponent(&raw);
    if (prec as i64) > exponent as i64 && exponent >= -4 {
        let fixed = format!("{:.*}", (prec as i64 - 1 - exponent as i64) as usize, value);
        return strip_trailing_zeros(&fixed).to_string();
    }
    format!("{}{}", strip_trailing_zeros(mantissa), exponent_suffix(exponent))
}

fn stream_numeric_prefix(text: &str) -> &str {
    let bytes = text.as_bytes();
    let mut pos = 0;
    if pos < bytes.len() && (bytes[pos] == b'-' || bytes[pos] == b'+') {
        pos += 1;
    }
    let mantissa_start = pos;
    while pos < bytes.len() && bytes[pos].is_ascii_digit() {
        pos += 1;
    }
    if pos < bytes.len() && bytes[pos] == b'.' {
        pos += 1;
        while pos < bytes.len() && bytes[pos].is_ascii_digit() {
            pos += 1;
        }
    }
    if pos == mantissa_start || (pos == mantissa_start + 1 && bytes[mantissa_start] == b'.') {
        return "";
    }
    if pos < bytes.len() && (bytes[pos] == b'e' || bytes[pos] == b'E') {
        let mut exp_pos = pos + 1;
        if exp_pos < bytes.len() && (bytes[exp_pos] == b'-' || bytes[exp_pos] == b'+') {
            exp_pos += 1;
        }
        let digits_start = exp_pos;
        while exp_pos < bytes.len() && bytes[exp_pos].is_ascii_digit() {
            exp_pos += 1;
        }
        if exp_pos > digits_start {
            pos = exp_pos;
        } else {
            return "";
        }
    }
    &text[..pos]
}

fn stream_read_float(text: &str) -> f64 {
    let prefix = stream_numeric_prefix(text);
    match prefix.parse::<f32>() {
        Ok(value) if value.is_infinite() => {
            if value < 0.0 {
                -f32::MAX as f64
            } else {
                f32::MAX as f64
            }
        }
        Ok(value) => value as f64,
        Err(_) => 0.0,
    }
}

fn stream_read_double(text: &str) -> f64 {
    let prefix = stream_numeric_prefix(text);
    match prefix.parse::<f64>() {
        Ok(value) if value.is_infinite() => {
            if value < 0.0 {
                -f64::MAX
            } else {
                f64::MAX
            }
        }
        Ok(value) => value,
        Err(_) => 0.0,
    }
}

fn host_binary(val1: f64, val2: f64, operation: fn(f64, f64) -> f64) -> f64 {
    if val1.is_nan() {
        return val1;
    }
    if val2.is_nan() {
        return val2;
    }
    operation(val1, val2)
}

fn truncate_to_i64(val: f64) -> i64 {
    if val.is_nan() || !(-9223372036854775808.0..9223372036854775808.0).contains(&val) {
        return i64::MIN;
    }
    val as i64
}

impl FloatFormat {
    pub fn new(sz: i32) -> FloatFormat {
        let mut format = FloatFormat {
            size: sz,
            signbit_pos: 0,
            frac_pos: 0,
            frac_size: 0,
            exp_pos: 0,
            exp_size: 0,
            bias: 0,
            maxexponent: 0,
            decimal_min_precision: 0,
            decimal_max_precision: 0,
            jbitimplied: false,
        };
        if sz == 4 {
            format.signbit_pos = 31;
            format.exp_pos = 23;
            format.exp_size = 8;
            format.frac_pos = 0;
            format.frac_size = 23;
            format.bias = 127;
            format.jbitimplied = true;
        } else if sz == 8 {
            format.signbit_pos = 63;
            format.exp_pos = 52;
            format.exp_size = 11;
            format.frac_pos = 0;
            format.frac_size = 52;
            format.bias = 1023;
            format.jbitimplied = true;
        }
        format.maxexponent = (1i32 << format.exp_size) - 1;
        format.calc_precision();
        format
    }

    pub fn get_size(&self) -> i32 {
        self.size
    }

    fn create_float(sign: bool, signif: u64, exp: i32) -> f64 {
        let signif = signif >> 1;
        let precis = 63;
        let mut res = signif as f64;
        let expchange = exp - precis + 1;
        res = ldexp(res, expchange);
        if sign {
            res *= -1.0;
        }
        res
    }

    fn extract_exp_sig(host: f64) -> (FloatClass, bool, u64, i32) {
        let sgn = host.is_sign_negative();
        if host == 0.0 {
            return (FloatClass::Zero, sgn, 0, 0);
        }
        if host.is_infinite() {
            return (FloatClass::Infinity, sgn, 0, 0);
        }
        if host.is_nan() {
            return (FloatClass::Nan, sgn, 0, 0);
        }
        let host = if sgn { -host } else { host };
        let (norm, e) = frexp(host);
        let norm = ldexp(norm, 63);
        let signif = (norm as u64) << 1;
        (FloatClass::Normalized, sgn, signif, e - 1)
    }

    fn round_to_nearest_even(signif: &mut u64, lowbitpos: i32) -> bool {
        let lowbitmask: u64 = if (lowbitpos as u32) < 64 { 1u64 << lowbitpos } else { 0 };
        let midbitmask: u64 = 1u64.wrapping_shl((lowbitpos - 1) as u32);
        let epsmask = midbitmask.wrapping_sub(1);
        let odd = (*signif & lowbitmask) != 0;
        if (*signif & midbitmask) != 0 && ((*signif & epsmask) != 0 || odd) {
            *signif = signif.wrapping_add(midbitmask);
            return true;
        }
        false
    }

    pub fn extract_fractional_code(&self, encoding: u64) -> u64 {
        let encoding = encoding.wrapping_shr(self.frac_pos as u32);
        encoding.wrapping_shl((64 - self.frac_size) as u32)
    }

    pub fn extract_sign(&self, encoding: u64) -> bool {
        (encoding.wrapping_shr(self.signbit_pos as u32) & 1) != 0
    }

    pub fn extract_exponent_code(&self, encoding: u64) -> i32 {
        let encoding = encoding.wrapping_shr(self.exp_pos as u32);
        let mask = 1u64.wrapping_shl(self.exp_size as u32).wrapping_sub(1);
        (encoding & mask) as i32
    }

    pub fn get_exponent(&self, encoding: u64) -> i32 {
        self.extract_exponent_code(encoding) - self.bias
    }

    fn set_fractional_code(&self, encoding: u64, code: u64) -> u64 {
        let code = code.wrapping_shr((64 - self.frac_size) as u32);
        let code = code.wrapping_shl(self.frac_pos as u32);
        encoding | code
    }

    fn set_sign(&self, encoding: u64, sign: bool) -> u64 {
        if !sign {
            return encoding;
        }
        encoding | 1u64.wrapping_shl(self.signbit_pos as u32)
    }

    fn set_exponent_code(&self, encoding: u64, code: u64) -> u64 {
        encoding | code.wrapping_shl(self.exp_pos as u32)
    }

    fn get_zero_encoding(&self, sgn: bool) -> u64 {
        let mut res = self.set_fractional_code(0, 0);
        res = self.set_exponent_code(res, 0);
        self.set_sign(res, sgn)
    }

    fn get_infinity_encoding(&self, sgn: bool) -> u64 {
        let mut res = self.set_fractional_code(0, 0);
        res = self.set_exponent_code(res, self.maxexponent as i64 as u64);
        self.set_sign(res, sgn)
    }

    fn get_nan_encoding(&self, sgn: bool) -> u64 {
        let mask = 1u64 << 63;
        let mut res = self.set_fractional_code(0, mask);
        res = self.set_exponent_code(res, self.maxexponent as i64 as u64);
        self.set_sign(res, sgn)
    }

    #[allow(clippy::approx_constant)]
    fn calc_precision(&mut self) {
        self.decimal_min_precision = (self.frac_size as f64 * 0.30103).floor() as i32;
        self.decimal_max_precision = ((self.frac_size + 1) as f64 * 0.30103).ceil() as i32 + 1;
    }

    pub fn get_class(&self, encoding: u64) -> FloatClass {
        let exp = self.extract_exponent_code(encoding);
        if exp == 0 {
            if self.extract_fractional_code(encoding) == 0 {
                return FloatClass::Zero;
            }
            return FloatClass::Denormalized;
        }
        if exp == self.maxexponent {
            if self.extract_fractional_code(encoding) == 0 {
                return FloatClass::Infinity;
            }
            return FloatClass::Nan;
        }
        FloatClass::Normalized
    }

    pub fn get_host_float(&self, encoding: u64) -> (f64, FloatClass) {
        let sgn = self.extract_sign(encoding);
        let mut frac = self.extract_fractional_code(encoding);
        let mut exp = self.extract_exponent_code(encoding);
        let mut normal = true;
        let class;
        if exp == 0 {
            if frac == 0 {
                return (if sgn { -0.0 } else { 0.0 }, FloatClass::Zero);
            }
            class = FloatClass::Denormalized;
            normal = false;
        } else if exp == self.maxexponent {
            if frac == 0 {
                return (
                    if sgn { f64::NEG_INFINITY } else { f64::INFINITY },
                    FloatClass::Infinity,
                );
            }
            let nan = f64::NAN;
            return (if sgn { -nan } else { nan }, FloatClass::Nan);
        } else {
            class = FloatClass::Normalized;
        }
        exp -= self.bias;
        if normal && self.jbitimplied {
            frac >>= 1;
            frac |= 1u64 << 63;
        }
        (FloatFormat::create_float(sgn, frac, exp), class)
    }

    fn encode_rounded(&self, sgn: bool, signif: u64, exp: i32) -> u64 {
        let mut signif = signif;
        let mut exp = exp + self.bias;
        if exp < -self.frac_size {
            return self.get_zero_encoding(sgn);
        }
        if exp < 1 {
            if FloatFormat::round_to_nearest_even(&mut signif, 64 - self.frac_size - exp) && (signif >> 63) == 0 {
                signif = 1u64 << 63;
                exp += 1;
            }
            let res = self.get_zero_encoding(sgn);
            return self.set_fractional_code(res, signif.wrapping_shr((-exp) as u32));
        }
        if FloatFormat::round_to_nearest_even(&mut signif, 64 - self.frac_size - 1) && (signif >> 63) == 0 {
            signif = 1u64 << 63;
            exp += 1;
        }
        if exp >= self.maxexponent {
            return self.get_infinity_encoding(sgn);
        }
        if self.jbitimplied && exp != 0 {
            signif <<= 1;
        }
        let mut res = self.set_fractional_code(0, signif);
        res = self.set_exponent_code(res, exp as i64 as u64);
        self.set_sign(res, sgn)
    }

    pub fn get_encoding(&self, host: f64) -> u64 {
        let (class, sgn, signif, exp) = FloatFormat::extract_exp_sig(host);
        match class {
            FloatClass::Zero => self.get_zero_encoding(sgn),
            FloatClass::Infinity => self.get_infinity_encoding(sgn),
            FloatClass::Nan => self.get_nan_encoding(sgn),
            _ => self.encode_rounded(sgn, signif, exp),
        }
    }

    pub fn convert_encoding(&self, encoding: u64, formin: &FloatFormat) -> u64 {
        let sgn = formin.extract_sign(encoding);
        let mut signif = formin.extract_fractional_code(encoding);
        let mut exp = formin.extract_exponent_code(encoding);
        if exp == formin.maxexponent {
            if signif != 0 {
                return self.get_nan_encoding(sgn);
            }
            return self.get_infinity_encoding(sgn);
        }
        if exp == 0 {
            if signif == 0 {
                return self.get_zero_encoding(sgn);
            }
            let lz = count_leading_zeros(signif);
            signif <<= lz;
            exp = -formin.bias - lz;
        } else {
            exp -= formin.bias;
            if self.jbitimplied {
                signif = (1u64 << 63) | (signif >> 1);
            }
        }
        self.encode_rounded(sgn, signif, exp)
    }

    pub fn print_decimal(&self, host: f64, forcesci: bool) -> String {
        let mut res;
        let mut prec = self.decimal_min_precision;
        loop {
            let text = if forcesci {
                format_float_scientific(host, if prec - 1 < 0 { 6 } else { (prec - 1) as usize })
            } else {
                format_float_general(host, prec.max(0) as usize)
            };
            if prec == self.decimal_max_precision {
                return text;
            }
            res = text;
            let roundtrip = if self.size <= 4 {
                stream_read_float(&res)
            } else {
                stream_read_double(&res)
            };
            if roundtrip == host {
                break;
            }
            prec += 1;
        }
        res
    }

    fn host_pair(&self, first: u64, second: u64) -> (f64, f64) {
        (self.get_host_float(first).0, self.get_host_float(second).0)
    }

    pub fn op_equal(&self, first: u64, second: u64) -> u64 {
        let (val1, val2) = self.host_pair(first, second);
        (val1 == val2) as u64
    }

    pub fn op_not_equal(&self, first: u64, second: u64) -> u64 {
        let (val1, val2) = self.host_pair(first, second);
        (val1 != val2) as u64
    }

    pub fn op_less(&self, first: u64, second: u64) -> u64 {
        let (val1, val2) = self.host_pair(first, second);
        (val1 < val2) as u64
    }

    pub fn op_less_equal(&self, first: u64, second: u64) -> u64 {
        let (val1, val2) = self.host_pair(first, second);
        (val1 <= val2) as u64
    }

    pub fn op_nan(&self, first: u64) -> u64 {
        let (_, class) = self.get_host_float(first);
        (class == FloatClass::Nan) as u64
    }

    pub fn op_add(&self, first: u64, second: u64) -> u64 {
        let (val1, val2) = self.host_pair(first, second);
        self.get_encoding(host_binary(val1, val2, |left, right| left + right))
    }

    pub fn op_div(&self, first: u64, second: u64) -> u64 {
        let (val1, val2) = self.host_pair(first, second);
        self.get_encoding(host_binary(val1, val2, |left, right| left / right))
    }

    pub fn op_mult(&self, first: u64, second: u64) -> u64 {
        let (val1, val2) = self.host_pair(first, second);
        self.get_encoding(host_binary(val1, val2, |left, right| left * right))
    }

    pub fn op_sub(&self, first: u64, second: u64) -> u64 {
        let (val1, val2) = self.host_pair(first, second);
        self.get_encoding(host_binary(val1, val2, |left, right| left - right))
    }

    pub fn op_neg(&self, first: u64) -> u64 {
        let val = self.get_host_float(first).0;
        self.get_encoding(-val)
    }

    pub fn op_abs(&self, first: u64) -> u64 {
        let val = self.get_host_float(first).0;
        self.get_encoding(val.abs())
    }

    pub fn op_sqrt(&self, first: u64) -> u64 {
        let val = self.get_host_float(first).0;
        self.get_encoding(val.sqrt())
    }

    pub fn op_trunc(&self, first: u64, sizeout: i32) -> u64 {
        let val = self.get_host_float(first).0;
        let ival = truncate_to_i64(val);
        (ival as u64) & calc_mask(sizeout)
    }

    pub fn op_ceil(&self, first: u64) -> u64 {
        let val = self.get_host_float(first).0;
        self.get_encoding(val.ceil())
    }

    pub fn op_floor(&self, first: u64) -> u64 {
        let val = self.get_host_float(first).0;
        self.get_encoding(val.floor())
    }

    pub fn op_round(&self, first: u64) -> u64 {
        let val = self.get_host_float(first).0;
        self.get_encoding(val.round())
    }

    pub fn op_int2float(&self, first: u64, sizein: i32) -> u64 {
        let ival = sign_extend(first as i64, 8 * sizein - 1);
        self.get_encoding(ival as f64)
    }

    pub fn op_float2float(&self, first: u64, outformat: &FloatFormat) -> u64 {
        outformat.convert_encoding(first, self)
    }
}
