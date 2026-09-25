use std::sync::Arc;

use ghidra_decompiler::address::Address;
use ghidra_decompiler::coreaction::{StackEqn, StackSolver};
use ghidra_decompiler::jumptable::{
    IndexPair, JumpValues, JumpValuesRange, JumpValuesRangeDefault, LoadTable, PathMeld, RootedOp,
};
use ghidra_decompiler::op::OpId;
use ghidra_decompiler::rangeutil::CircleRange;
use ghidra_decompiler::space::AddrSpace;
use ghidra_decompiler::varnode::VarnodeId;

fn solver_with_variables(count: u32) -> StackSolver {
    let mut solver = StackSolver::default();
    for index in 0..count {
        solver.vnlist.push(VarnodeId(index));
        solver.companion.push(-1);
    }
    solver
}

#[test]
fn stack_solver_propagates_known_equations() {
    let mut solver = solver_with_variables(3);
    solver.eqs.push(StackEqn {
        var1: 1,
        var2: 0,
        rhs: -4,
    });
    solver.eqs.push(StackEqn {
        var1: 2,
        var2: 1,
        rhs: 8,
    });
    solver.solve();
    assert_eq!(solver.get_solution(0), 0);
    assert_eq!(solver.get_solution(1), -4);
    assert_eq!(solver.get_solution(2), 4);
}

#[test]
fn stack_solver_uses_guesses_for_unknown_variables() {
    let mut solver = solver_with_variables(4);
    solver.eqs.push(StackEqn {
        var1: 1,
        var2: 0,
        rhs: -4,
    });
    solver.guess.push(StackEqn {
        var1: 2,
        var2: 1,
        rhs: 4,
    });
    solver.solve();
    assert_eq!(solver.get_solution(1), -4);
    assert_eq!(solver.get_solution(2), 0);
    assert_eq!(solver.get_solution(3), 65535);
}

fn unique_space() -> Arc<AddrSpace> {
    Arc::new(AddrSpace::new_unique(false, 3, 0))
}

#[test]
fn load_table_collapses_contiguous_entries() {
    let spc = unique_space();
    let mut table = vec![
        LoadTable::new(&Address::new(spc.clone(), 0x100), 4),
        LoadTable::new(&Address::new(spc.clone(), 0x104), 4),
        LoadTable::new(&Address::new(spc.clone(), 0x108), 4),
    ];
    LoadTable::collapse_table(&mut table);
    assert_eq!(table.len(), 1);
    assert_eq!(table[0].num, 3);
    assert_eq!(table[0].addr.get_offset(), 0x100);
}

#[test]
fn load_table_sorts_and_merges_unordered_entries() {
    let spc = unique_space();
    let mut table = vec![
        LoadTable::new(&Address::new(spc.clone(), 0x108), 4),
        LoadTable::new(&Address::new(spc.clone(), 0x100), 4),
        LoadTable::new(&Address::new(spc.clone(), 0x104), 4),
        LoadTable::new(&Address::new(spc.clone(), 0x200), 2),
        LoadTable::new(&Address::new(spc.clone(), 0x102), 4),
    ];
    LoadTable::collapse_table(&mut table);
    let summary: Vec<(u64, i32, i32)> = table
        .iter()
        .map(|entry| (entry.addr.get_offset(), entry.size, entry.num))
        .collect();
    assert_eq!(summary, vec![(0x100, 4, 3), (0x200, 2, 1)]);
}

fn collect_values(values: &dyn JumpValues) -> Vec<(u64, bool)> {
    let mut res = Vec::new();
    let mut notdone = values.initialize_for_reading();
    while notdone {
        res.push((values.get_value(), values.is_reversible()));
        notdone = values.next();
    }
    res
}

#[test]
fn jump_values_range_iterates_and_truncates() {
    let mut values = JumpValuesRange::new();
    values.set_range(&CircleRange::new_range(0, 8, 4, 2), VarnodeId(1), Some(OpId(2)));
    assert_eq!(values.get_size(), 4);
    assert_eq!(
        collect_values(&values),
        vec![(0, true), (2, true), (4, true), (6, true)]
    );
    assert!(values.contains(4));
    assert!(!values.contains(5));
    values.truncate(2);
    assert_eq!(values.get_size(), 2);
    assert_eq!(collect_values(&values), vec![(0, true), (2, true)]);
}

#[test]
fn jump_values_range_default_appends_extra_value() {
    let mut values = JumpValuesRangeDefault::new();
    values
        .base
        .set_range(&CircleRange::new_range(1, 4, 4, 1), VarnodeId(1), Some(OpId(2)));
    values.set_extra_value(0x55);
    values.set_default_vn(VarnodeId(7));
    values.set_default_op(OpId(9));
    assert_eq!(values.get_size(), 4);
    assert!(values.contains(0x55));
    assert_eq!(
        collect_values(&values),
        vec![(1, true), (2, true), (3, true), (0x55, false)]
    );
    assert_eq!(values.get_start_varnode(), Some(VarnodeId(7)));
    assert_eq!(values.get_start_op(), Some(OpId(9)));
    let copy = values.clone_values();
    assert_eq!(copy.get_size(), 4);
}

#[test]
fn path_meld_append_truncate() {
    let mut meld = PathMeld {
        common_vn: vec![VarnodeId(10), VarnodeId(11)],
        op_meld: vec![RootedOp::new(OpId(1), 0), RootedOp::new(OpId(2), 1)],
    };
    let mut tail = PathMeld::default();
    tail.set_op(OpId(0), VarnodeId(5));
    meld.append(&tail);
    assert_eq!(meld.common_vn, vec![VarnodeId(5), VarnodeId(10), VarnodeId(11)]);
    let roots: Vec<i32> = meld.op_meld.iter().map(|rooted| rooted.root_vn).collect();
    assert_eq!(roots, vec![0, 1, 2]);
    assert_eq!(meld.get_earliest_op(1), Some(OpId(1)));
    meld.truncate_paths(2);
    assert_eq!(meld.num_common_varnode(), 2);
    let ops: Vec<i32> = meld.op_meld.iter().map(|rooted| rooted.root_vn).collect();
    assert_eq!(ops, vec![0, 1]);
}

#[test]
fn index_pair_ordering() {
    let mut pairs = vec![IndexPair::new(2, 0), IndexPair::new(1, 3), IndexPair::new(1, 1)];
    pairs.sort();
    assert_eq!(
        pairs,
        vec![IndexPair::new(1, 1), IndexPair::new(1, 3), IndexPair::new(2, 0)]
    );
    assert!(IndexPair::compare_by_position(&pairs[0], &pairs[2]));
    assert!(!IndexPair::compare_by_position(&pairs[0], &pairs[1]));
}
