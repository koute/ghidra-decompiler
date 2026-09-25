use ghidra_decompiler::multiprecision::*;

const NUM1: [u64; 2] = [0xffffffffffffffff, 0xffffffffffffffff];
const DENOM1: [u64; 2] = [1, 0];
const NUM2: [u64; 2] = [0x89a732a9fb157c4d, 0x4eada2039e48443e];
const DENOM2: [u64; 2] = [0xbabf3b71, 0];
const NUM3: [u64; 2] = [0xf7df0315d584ad8d, 0xb9d55c0d1d5cfbbd];
const DENOM3: [u64; 2] = [0x8aa797dbccee6e96, 0x646be9];
const VALUE_A: [u64; 2] = [0x1a309a9df2ce836a, 0xd66f2248906d1bdf];
const VALUE_B: [u64; 2] = [0xf6c190704eb1763e, 0xa05c42212dfba7c6];

#[test]
fn multiprec_udiv() {
    let (quotient, remainder) = udiv128(&NUM1, &DENOM1).expect("divide");
    assert_eq!(quotient, [0xffffffffffffffff, 0xffffffffffffffff]);
    assert_eq!(remainder, [0, 0]);

    let (quotient, remainder) = udiv128(&NUM2, &DENOM2).expect("divide");
    assert_eq!(quotient, [0x2a21eef2058d7e9a, 0x6bdaed99]);
    assert_eq!(remainder, [0x928d1c53, 0]);

    let (quotient, remainder) = udiv128(&NUM2, &NUM1).expect("divide");
    assert_eq!(quotient, [0, 0]);
    assert_eq!(remainder, NUM2);

    let (quotient, remainder) = udiv128(&NUM3, &DENOM3).expect("divide");
    assert_eq!(quotient, [0x1d9bc949e24, 0]);
    assert_eq!(remainder, [0x2e78197dc5048c75, 0x24d9cc]);
}

#[test]
fn multiprec_add() {
    assert_eq!(add128(&VALUE_A, &VALUE_B), [0x10f22b0e417ff9a8, 0x76cb6469be68c3a6]);
}

#[test]
fn multiprec_sub() {
    assert_eq!(
        subtract128(&VALUE_A, &VALUE_B),
        [0x236F0A2DA41D0D2C, 0x3612E02762717418]
    );
}

#[test]
fn multiprec_left() {
    assert_eq!(leftshift128(&NUM2, 51), [0xe268000000000000, 0x21f44d39954fd8ab]);
}

#[test]
fn multiprec_less() {
    assert!(!uless128(&VALUE_A, &VALUE_A));
    assert!(uless128(&NUM2, &NUM3));
    assert!(uless128(&DENOM1, &DENOM2));
    assert!(ulessequal128(&VALUE_A, &VALUE_A));
    assert!(ulessequal128(&NUM2, &NUM3));
    assert!(ulessequal128(&DENOM2, &DENOM2));
}

#[test]
fn multiprec_udiv_matches_native() {
    let mut state: u64 = 0x243f6a8885a308d3;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for round in 0..20000 {
        let shift_numer = next() % 128;
        let shift_denom = next() % 128;
        let numer = ((next() as u128) << 64 | next() as u128) >> shift_numer;
        let mut denom = ((next() as u128) << 64 | next() as u128) >> shift_denom;
        if round % 7 == 0 {
            denom &= 0xffffffff;
        }
        if denom == 0 {
            continue;
        }
        let numer_words = [numer as u64, (numer >> 64) as u64];
        let denom_words = [denom as u64, (denom >> 64) as u64];
        let (quotient, remainder) = udiv128(&numer_words, &denom_words).expect("divide");
        let expected_quotient = numer / denom;
        let expected_remainder = numer % denom;
        assert_eq!(quotient, [expected_quotient as u64, (expected_quotient >> 64) as u64]);
        assert_eq!(
            remainder,
            [expected_remainder as u64, (expected_remainder >> 64) as u64]
        );
    }
}
