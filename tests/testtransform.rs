use std::sync::Arc;

use ghidra_decompiler::op::OpId;
use ghidra_decompiler::opcodes::OpCode;
use ghidra_decompiler::pcoderaw::VarnodeData;
use ghidra_decompiler::prefersplit::{PreferSplitManager, PreferSplitRecord};
use ghidra_decompiler::space::AddrSpace;
use ghidra_decompiler::transform::{LaneDescription, LanedRegister, TransformManager, TransformOp, TransformVar};

fn lanes(description: &LaneDescription) -> Vec<(i32, i32)> {
    (0..description.get_num_lanes())
        .map(|index| (description.get_size(index), description.get_position(index)))
        .collect()
}

#[test]
fn lane_description_uniform() {
    let description = LaneDescription::new(16, 4);
    assert_eq!(description.get_whole_size(), 16);
    assert_eq!(lanes(&description), vec![(4, 0), (4, 4), (4, 8), (4, 12)]);
    assert_eq!(description.get_boundary(0), 0);
    assert_eq!(description.get_boundary(8), 2);
    assert_eq!(description.get_boundary(16), 4);
    assert_eq!(description.get_boundary(6), -1);
    assert_eq!(description.get_boundary(-1), -1);
    assert_eq!(description.get_boundary(17), -1);
}

#[test]
fn lane_description_lo_hi() {
    let description = LaneDescription::new_lo_hi(8, 3, 5);
    assert_eq!(lanes(&description), vec![(3, 0), (5, 3)]);
    assert_eq!(description.get_boundary(3), 1);
    assert_eq!(description.get_boundary(8), 2);
}

#[test]
fn lane_description_subset() {
    let mut description = LaneDescription::new(16, 4);
    assert!(description.subset(0, 16));
    assert_eq!(description.get_num_lanes(), 4);
    assert!(!description.subset(2, 4));
    assert!(description.subset(4, 8));
    assert_eq!(description.get_whole_size(), 8);
    assert_eq!(lanes(&description), vec![(4, 0), (4, 4)]);
}

#[test]
fn lane_description_restriction_extension() {
    let description = LaneDescription::new(16, 4);
    let mut num_lanes = -1;
    let mut skip_lanes = -1;
    assert!(description.restriction(4, 0, 4, 8, &mut num_lanes, &mut skip_lanes));
    assert_eq!((num_lanes, skip_lanes), (2, 1));
    assert!(!description.restriction(4, 1, 0, 0, &mut num_lanes, &mut skip_lanes));
    assert!(!description.restriction(4, 0, 2, 4, &mut num_lanes, &mut skip_lanes));
    assert_eq!(skip_lanes, -1);
    assert!(description.extension(2, 1, 4, 16, &mut num_lanes, &mut skip_lanes));
    assert_eq!((num_lanes, skip_lanes), (4, 0));
    assert!(!description.extension(2, 1, 8, 16, &mut num_lanes, &mut skip_lanes));
}

#[test]
fn laned_register_parse_sizes() {
    let mut register = LanedRegister::new();
    register.parse_sizes(16, "1,2,4,8").expect("valid lane sizes");
    assert_eq!(register.get_whole_size(), 16);
    assert_eq!(register.get_size_bit_mask(), 0x116);
    assert_eq!(register.begin().collect::<Vec<i32>>(), vec![1, 2, 4, 8]);
    assert!(register.allowed_lane(4));
    assert!(!register.allowed_lane(3));

    register.parse_sizes(16, "0x4,").expect("valid lane sizes");
    assert_eq!(register.get_size_bit_mask(), 0x10);

    let err = register
        .parse_sizes(16, "16")
        .expect_err("lane size equal to register size");
    assert_eq!(err.explain(), "Bad lane size: 16");
    let err = register.parse_sizes(16, "").expect_err("empty lane size");
    assert_eq!(err.explain(), "Bad lane size: ");
    let err = register.parse_sizes(32, "4,x").expect_err("non numeric lane size");
    assert_eq!(err.explain(), "Bad lane size: x");
}

#[test]
fn laned_register_empty_iteration() {
    let register = LanedRegister::with_mask(16, 0);
    assert_eq!(register.begin(), register.end());
    assert_eq!(register.begin().count(), 0);
}

#[test]
fn transform_manager_placeholders() {
    let mut manager = TransformManager::new();
    let constant = manager.new_constant(2, 8, 0x123456);
    assert_eq!(manager.var(constant).val, 0x1234);
    assert_eq!(manager.var(constant).var_type, TransformVar::CONSTANT);
    assert_eq!(manager.var(constant).bit_size, 16);
    let unique = manager.new_unique(4);
    assert_eq!(manager.var(unique).var_type, TransformVar::NORMAL_TEMP);
    assert_eq!(manager.var(unique).byte_size, 4);

    let replace = manager.new_op_replace(2, OpCode::IntAdd, OpId(5));
    assert_eq!(manager.op(replace).special, TransformOp::OP_REPLACEMENT);
    assert_eq!(manager.op(replace).input.len(), 2);
    let follow = manager.new_op(1, OpCode::IntZext, replace);
    assert_eq!(manager.op(follow).op, Some(OpId(5)));
    assert_eq!(manager.op(follow).follow, Some(replace));
    assert_eq!(manager.op(follow).special, 0);
    manager.op_set_output(follow, unique);
    manager.op_set_input(replace, unique, 0);
    manager.op_set_input(replace, constant, 1);
    assert_eq!(manager.var(unique).get_def(), Some(follow));
    assert_eq!(manager.op(replace).get_in(1), Some(constant));

    let preexisting = manager.new_preexisting_op(1, OpCode::Copy, OpId(7));
    assert_eq!(manager.op(preexisting).special, TransformOp::OP_PREEXISTING);

    let mut piece = TransformVar::default();
    piece.initialize(TransformVar::PIECE, None, 8, 1, 0);
    assert!(TransformManager::preexisting_guard(0, &piece));
    assert!(!TransformManager::preexisting_guard(1, &piece));
    assert!(TransformManager::preexisting_guard(1, manager.var(constant)));
}

fn record(space: &Arc<AddrSpace>, offset: u64, size: u32, splitoffset: i32) -> PreferSplitRecord {
    PreferSplitRecord {
        storage: VarnodeData {
            space: Some(space.clone()),
            offset,
            size,
        },
        splitoffset,
    }
}

#[test]
fn prefer_split_record_order() {
    let constant_space = Arc::new(AddrSpace::new_constant());
    let unique_space = Arc::new(AddrSpace::new_unique(false, 3, 0));
    let mut records = vec![
        record(&unique_space, 0x10, 4, 2),
        record(&unique_space, 0x10, 8, 4),
        record(&constant_space, 0x20, 4, 2),
        record(&unique_space, 0x8, 4, 2),
    ];
    PreferSplitManager::initialize(&mut records);
    let order: Vec<(i32, u64, u32)> = records
        .iter()
        .map(|rec| {
            (
                rec.storage.space.as_ref().map_or(-1, |spc| spc.get_index()),
                rec.storage.offset,
                rec.storage.size,
            )
        })
        .collect();
    assert_eq!(order, vec![(0, 0x20, 4), (3, 0x10, 8), (3, 0x8, 4), (3, 0x10, 4)]);
    assert!(records[1].less_than(&records[2]));
    assert!(!records[2].less_than(&records[1]));
}
