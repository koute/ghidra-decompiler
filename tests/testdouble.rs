use ghidra_decompiler::double::SplitVarnode;

#[test]
fn constant_split_varnode_has_no_pieces() {
    let split = SplitVarnode::new_constant(8, 0x1122334455667788);
    assert!(split.is_constant());
    assert!(!split.has_both_pieces());
    assert_eq!(split.get_size(), 8);
    assert_eq!(split.get_value(), 0x1122334455667788);
    assert_eq!(split.get_lo(), None);
    assert_eq!(split.get_hi(), None);
    assert_eq!(split.get_whole(), None);
    assert_eq!(split.get_def_point(), None);
    assert_eq!(split.get_def_block(), None);
}

#[test]
fn constant_precision_limit_is_eight_bytes() {
    assert!(!SplitVarnode::new_constant(4, 1).exceeds_const_precision());
    assert!(!SplitVarnode::new_constant(8, u64::MAX).exceeds_const_precision());
    assert!(SplitVarnode::new_constant(16, 0).exceeds_const_precision());
    assert!(SplitVarnode::new_constant(-1, 0).exceeds_const_precision());
}

#[test]
fn partial_constant_reinitializes_fields() {
    let mut split = SplitVarnode::new_constant(16, 5);
    split.init_partial_constant(4, 0xdeadbeef);
    assert!(split.is_constant());
    assert_eq!(split.get_size(), 4);
    assert_eq!(split.get_value(), 0xdeadbeef);
    assert!(!split.exceeds_const_precision());
}
