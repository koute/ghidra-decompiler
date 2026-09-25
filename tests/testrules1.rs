use ghidra_decompiler::action::Rule;
use ghidra_decompiler::opcodes::OpCode;
use ghidra_decompiler::ruleaction::*;

fn op_list(rule: &dyn Rule) -> Vec<OpCode> {
    let mut oplist = Vec::new();
    rule.get_op_list(&mut oplist);
    oplist
}

#[test]
fn op_list_sizes_match_cpp_tables() {
    assert_eq!(op_list(&RuleEarlyRemoval::new("analysis")).len(), 65);
    assert_eq!(op_list(&RuleTermOrder::new("analysis")).len(), 16);
    assert_eq!(op_list(&RuleTrivialArith::new("analysis")).len(), 16);
    assert_eq!(op_list(&RuleCollapseConstants::new("analysis")).len(), 52);
    assert_eq!(op_list(&RuleIdentityEl::new("analysis")).len(), 6);
    assert_eq!(op_list(&RuleZextEliminate::new("analysis")).len(), 4);
}

#[test]
fn op_list_order_matches_cpp() {
    let early = op_list(&RuleEarlyRemoval::new("analysis"));
    assert_eq!(early.first(), Some(&OpCode::Copy));
    assert_eq!(early.last(), Some(&OpCode::Spull));
    assert!(!early.contains(&OpCode::Indirect));
    assert!(!early.contains(&OpCode::Store));
    assert_eq!(
        op_list(&RuleSelectCse::new("analysis")),
        vec![OpCode::Subpiece, OpCode::IntSright]
    );
    assert_eq!(
        op_list(&RuleShiftBitops::new("analysis")),
        vec![OpCode::IntLeft, OpCode::IntRight, OpCode::Subpiece, OpCode::IntMult]
    );
    assert_eq!(
        op_list(&RuleAliasUpdate::new("analysis")),
        vec![OpCode::Store, OpCode::Call, OpCode::Callind, OpCode::Callother]
    );
    assert_eq!(
        op_list(&RuleShiftAnd::new("analysis")),
        vec![OpCode::IntRight, OpCode::IntLeft, OpCode::IntMult]
    );
    let collapse = op_list(&RuleCollapseConstants::new("analysis"));
    assert_eq!(collapse.first(), Some(&OpCode::IntEqual));
    assert_eq!(collapse.last(), Some(&OpCode::Lzcount));
}

#[test]
fn pullsub_acceptable_sizes() {
    let accepted: Vec<i32> = (0..20)
        .filter(|size| RulePullsubMulti::acceptable_size(*size))
        .collect();
    assert_eq!(accepted, vec![1, 2, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]);
}
