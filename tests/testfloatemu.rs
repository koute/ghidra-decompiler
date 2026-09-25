use ghidra_decompiler::float::FloatFormat;

fn float_to_raw_bits(value: f32) -> u64 {
    value.to_bits() as u64
}

fn double_to_raw_bits(value: f64) -> u64 {
    value.to_bits()
}

fn assert_float_encoding(value: f64) {
    let format = FloatFormat::new(4);
    assert_eq!(float_to_raw_bits(value as f32), format.get_encoding(value));
}

fn assert_double_encoding(value: f64) {
    let format = FloatFormat::new(8);
    assert_eq!(double_to_raw_bits(value), format.get_encoding(value));
}

fn float_test_values() -> Vec<f32> {
    let denorm_min = f32::from_bits(1);
    let min = f32::MIN_POSITIVE;
    vec![
        -0.0,
        0.0,
        -1.0,
        1.0,
        -1.234,
        1.234,
        -denorm_min,
        denorm_min,
        min - denorm_min,
        min,
        min + denorm_min,
        -min + denorm_min,
        -min,
        -min - denorm_min,
        f32::MAX,
        f32::NAN,
        f32::NEG_INFINITY,
        f32::INFINITY,
    ]
}

const INT_TEST_VALUES: [i32; 7] = [0, -1, 1, 1234, -1234, i32::MIN, i32::MAX];

#[test]
fn float_encoding_normal() {
    assert_float_encoding(1.234);
    assert_float_encoding(-1.234);
}

#[test]
fn double_encoding_normal() {
    assert_double_encoding(1.234);
    assert_double_encoding(-1.234);
}

#[test]
fn float_encoding_nan() {
    assert_float_encoding(f32::NAN as f64);
    assert_float_encoding(-f32::NAN as f64);
}

#[test]
fn double_encoding_nan() {
    assert_double_encoding(f64::NAN);
    assert_double_encoding(-f64::NAN);
}

#[test]
fn float_encoding_subnormal() {
    assert_float_encoding(f32::from_bits(1) as f64);
    assert_float_encoding(-f32::from_bits(1) as f64);
}

#[test]
fn double_encoding_subnormal() {
    assert_double_encoding(f64::from_bits(1));
    assert_double_encoding(-f64::from_bits(1));
}

#[test]
fn float_encoding_min_normal() {
    assert_float_encoding(f32::MIN_POSITIVE as f64);
    assert_float_encoding(-f32::MIN_POSITIVE as f64);
}

#[test]
fn double_encoding_min_normal() {
    assert_double_encoding(f64::MIN_POSITIVE);
    assert_double_encoding(-f64::MIN_POSITIVE);
}

#[test]
fn float_encoding_infinity() {
    assert_float_encoding(f64::INFINITY);
    assert_float_encoding(f64::NEG_INFINITY);
}

#[test]
fn double_encoding_infinity() {
    assert_double_encoding(f64::INFINITY);
    assert_double_encoding(f64::NEG_INFINITY);
}

#[test]
fn float_decimal_precision() {
    let ff = FloatFormat::new(4);
    let cases = [
        (0x34000001u32, "1.192093e-07"),
        (0x34800000, "2.3841858e-07"),
        (0x3eaaaaab, "0.33333334"),
        (0x3e800000, "0.25"),
        (0x3de3ee46, "0.111294314"),
    ];
    for (bits, text) in cases {
        assert_eq!(ff.print_decimal(f32::from_bits(bits) as f64, false), text);
    }
}

#[test]
fn double_decimal_precision() {
    let ff = FloatFormat::new(8);
    let cases = [
        (0x3fc5555555555555u64, false, "0.16666666666666666"),
        (0x7fefffffffffffff, false, "1.79769313486232e+308"),
        (0x3fd555555c7dda4b, false, "0.33333334"),
        (0x3fd0000000000000, false, "0.25"),
        (0x3fb999999999999a, false, "0.1"),
        (0x3fbf7ced916872b0, true, "1.23000000000000e-01"),
    ];
    for (bits, forcesci, text) in cases {
        assert_eq!(ff.print_decimal(f64::from_bits(bits), forcesci), text);
    }
}

#[test]
fn float_midpoint_rounding() {
    let ff = FloatFormat::new(4);
    let doubles = [
        f64::from_bits(0x4010000000000000),
        f64::from_bits(0x4010000010000000),
        f64::from_bits(0x4010000010000001),
        f64::from_bits(0x4010000020000000),
        f64::from_bits(0x4010000030000000),
        f64::from_bits(0x4010000030000001),
    ];
    let encodings: Vec<u64> = doubles.iter().map(|value| ff.get_encoding(*value)).collect();
    for (value, encoding) in doubles.iter().zip(encodings.iter()) {
        assert_eq!(float_to_raw_bits(*value as f32), *encoding);
    }
    assert_eq!(encodings[0], encodings[1]);
    assert_ne!(encodings[1], encodings[2]);
    assert_ne!(encodings[3], encodings[4]);
    assert_eq!(encodings[4], encodings[5]);
}

#[test]
fn float_op_nan() {
    let format = FloatFormat::new(4);
    for value in float_test_values() {
        let encoding = format.get_encoding(value as f64);
        assert_eq!(value.is_nan() as u64, format.op_nan(encoding));
    }
}

#[test]
fn float_op_neg() {
    let format = FloatFormat::new(4);
    for value in float_test_values() {
        let encoding = format.get_encoding(value as f64);
        assert_eq!(float_to_raw_bits(-value), format.op_neg(encoding));
    }
}

#[test]
fn float_op_abs() {
    let format = FloatFormat::new(4);
    for value in float_test_values() {
        let encoding = format.get_encoding(value as f64);
        assert_eq!(float_to_raw_bits(value.abs()), format.op_abs(encoding));
    }
}

#[test]
fn float_op_sqrt() {
    let format = FloatFormat::new(4);
    for value in float_test_values() {
        let encoding = format.get_encoding(value as f64);
        assert_eq!(float_to_raw_bits(value.sqrt()), format.op_sqrt(encoding));
    }
}

#[test]
fn float_op_ceil() {
    let format = FloatFormat::new(4);
    for value in float_test_values() {
        let encoding = format.get_encoding(value as f64);
        assert_eq!(float_to_raw_bits(value.ceil()), format.op_ceil(encoding));
    }
}

#[test]
fn float_op_floor() {
    let format = FloatFormat::new(4);
    for value in float_test_values() {
        let encoding = format.get_encoding(value as f64);
        assert_eq!(float_to_raw_bits(value.floor()), format.op_floor(encoding));
    }
}

#[test]
fn float_op_round() {
    let format = FloatFormat::new(4);
    for value in float_test_values() {
        let encoding = format.get_encoding(value as f64);
        assert_eq!(float_to_raw_bits(value.round()), format.op_round(encoding));
    }
}

#[test]
fn float_op_int2float_size4() {
    let format = FloatFormat::new(4);
    for value in INT_TEST_VALUES {
        assert_eq!(
            float_to_raw_bits(value as f32),
            format.op_int2float(value as i64 as u64, 4)
        );
    }
}

#[test]
fn float_to_double_op_float2float() {
    let format = FloatFormat::new(4);
    let format8 = FloatFormat::new(8);
    for value in float_test_values() {
        let encoding = format.get_encoding(value as f64);
        assert_eq!(
            double_to_raw_bits(value as f64),
            format.op_float2float(encoding, &format8)
        );
    }
}

#[test]
fn float_op_trunc_to_int() {
    let format = FloatFormat::new(4);
    for value in float_test_values() {
        let wide = value as i64;
        if wide > i32::MAX as i64 || wide < i32::MIN as i64 || value.is_nan() {
            continue;
        }
        let expected = (value as i32) as u32 as u64;
        let encoding = format.get_encoding(value as f64);
        assert_eq!(expected, format.op_trunc(encoding, 4));
    }
}

fn check_binary(operation: fn(&FloatFormat, u64, u64) -> u64, host: fn(f32, f32) -> u64) {
    let format = FloatFormat::new(4);
    for first in float_test_values() {
        let encoding1 = format.get_encoding(first as f64);
        for second in float_test_values() {
            let encoding2 = format.get_encoding(second as f64);
            assert_eq!(
                host(first, second),
                operation(&format, encoding1, encoding2),
                "{first} {second}"
            );
        }
    }
}

#[test]
fn float_op_equal() {
    check_binary(FloatFormat::op_equal, |first, second| (first == second) as u64);
}

#[test]
fn float_op_not_equal() {
    check_binary(FloatFormat::op_not_equal, |first, second| (first != second) as u64);
}

#[test]
fn float_op_less() {
    check_binary(FloatFormat::op_less, |first, second| (first < second) as u64);
}

#[test]
fn float_op_less_equal() {
    check_binary(FloatFormat::op_less_equal, |first, second| (first <= second) as u64);
}

#[test]
fn float_op_add() {
    check_binary(FloatFormat::op_add, |first, second| float_to_raw_bits(first + second));
}

#[test]
fn float_op_div() {
    check_binary(FloatFormat::op_div, |first, second| float_to_raw_bits(first / second));
}

#[test]
fn float_op_mult() {
    check_binary(FloatFormat::op_mult, |first, second| float_to_raw_bits(first * second));
}

#[test]
fn float_op_sub() {
    check_binary(FloatFormat::op_sub, |first, second| float_to_raw_bits(first - second));
}
