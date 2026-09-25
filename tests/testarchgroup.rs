use std::sync::Arc;

use ghidra_decompiler::action::{
    Action, ActionBase, ActionDatabase, ActionGroup, ActionGroupList, ActionRestartGroup, RULE_ONCEPERFUNC,
    RULE_REPEATAPPLY, UNIVERSALNAME,
};
use ghidra_decompiler::architecture::Architecture;
use ghidra_decompiler::error::Result;
use ghidra_decompiler::funcdata::Funcdata;
use ghidra_decompiler::loadimage::RawLoadImage;
use ghidra_decompiler::memstate::{MemoryBank, MemoryHashOverlay, MemoryImage, MemoryPageOverlay};
use ghidra_decompiler::options::{OptionSplitDatatypes, on_or_off};
use ghidra_decompiler::space::{AddrSpace, SpaceRef};
use ghidra_decompiler::userop::{UserOpManage, UserPcodeOp};

fn test_space(big_endian: bool) -> SpaceRef {
    Arc::new(AddrSpace::new_processor(
        "ram",
        big_endian,
        4,
        1,
        1,
        AddrSpace::HASPHYSICAL,
        1,
        0,
    ))
}

fn image_bytes() -> Vec<u8> {
    (1u8..=64).collect()
}

#[test]
fn memory_image_reads_little_and_big_endian() {
    let loader = RawLoadImage::from_bytes("test", image_bytes());
    let little = test_space(false);
    let mut bank = MemoryImage::new(little, 4, 16, &loader);
    assert_eq!(bank.get_value(0, 4).expect("read value"), 0x04030201);
    assert_eq!(bank.get_value(3, 4).expect("read spanning value"), 0x07060504);
    assert_eq!(bank.get_value(5, 2).expect("read short"), 0x0706);

    let big = test_space(true);
    let mut bank = MemoryImage::new(big, 4, 16, &loader);
    assert_eq!(bank.get_value(0, 4).expect("read value"), 0x01020304);
    assert_eq!(bank.get_value(3, 4).expect("read spanning value"), 0x04050607);
    assert_eq!(bank.get_value(5, 2).expect("read short"), 0x0607);
    assert!(bank.set_value(0, 4, 1).is_err());
}

#[test]
fn page_overlay_writes_through_underlying_image() {
    let loader = RawLoadImage::from_bytes("test", image_bytes());
    for big_endian in [false, true] {
        let spc = test_space(big_endian);
        let image = MemoryImage::new(spc.clone(), 8, 16, &loader);
        let mut overlay = MemoryPageOverlay::new(spc.clone(), 8, 16, Some(Box::new(image)));
        overlay.set_value(6, 4, 0xaabbccdd).expect("write spanning value");
        assert_eq!(overlay.get_value(6, 4).expect("read back"), 0xaabbccdd);
        let mut chunk = [0u8; 12];
        overlay.get_chunk(2, 12, &mut chunk).expect("read chunk");
        let expected_middle: [u8; 4] = if big_endian {
            [0xaa, 0xbb, 0xcc, 0xdd]
        } else {
            [0xdd, 0xcc, 0xbb, 0xaa]
        };
        assert_eq!(&chunk[0..4], &[3, 4, 5, 6]);
        assert_eq!(&chunk[4..8], &expected_middle);
        assert_eq!(&chunk[8..12], &[11, 12, 13, 14]);
        overlay.set_chunk(30, 4, &[9, 8, 7, 6]).expect("write chunk");
        let mut back = [0u8; 4];
        overlay.get_chunk(30, 4, &mut back).expect("read chunk back");
        assert_eq!(back, [9, 8, 7, 6]);
    }
}

#[test]
fn hash_overlay_stores_words() {
    let spc = test_space(false);
    let mut overlay = MemoryHashOverlay::new(spc, 4, 16, 16, None);
    assert_eq!(overlay.get_value(0x100, 4).expect("read empty"), 0);
    overlay.set_value(0x100, 4, 0x11223344).expect("write word");
    overlay.set_value(0x102, 1, 0x99).expect("write byte");
    assert_eq!(overlay.get_value(0x100, 4).expect("read word"), 0x11993344);
    for index in 0..15u64 {
        overlay.insert(0x1000 + index * 4, index).expect("fill table");
    }
    assert!(overlay.insert(0x9000, 1).is_err());
}

#[test]
fn option_toggles_and_split_bits() {
    assert!(on_or_off("").expect("empty toggle"));
    assert!(on_or_off("on").expect("on toggle"));
    assert!(!on_or_off("off").expect("off toggle"));
    assert!(on_or_off("maybe").is_err());
    assert_eq!(OptionSplitDatatypes::get_option_bit("").expect("empty bit"), 0);
    assert_eq!(
        OptionSplitDatatypes::get_option_bit("array").expect("array bit"),
        OptionSplitDatatypes::OPTION_ARRAY
    );
    assert!(OptionSplitDatatypes::get_option_bit("union").is_err());
}

#[test]
fn userop_registration_rules() {
    assert_eq!(UserPcodeOp::append_size("read", 4), "read_4");
    assert_eq!(UserPcodeOp::append_size("read", 16), "read_16");
    let mut manage = UserOpManage::new();
    manage
        .register_op(UserPcodeOp::new_unspecialized("first", 0))
        .expect("register first");
    manage
        .register_op(UserPcodeOp::new_unspecialized("second", 2))
        .expect("register second");
    assert_eq!(
        manage.get_op(2).map(|op| op.get_name().to_string()),
        Some("second".to_string())
    );
    assert!(manage.get_op(1).is_none());
    assert!(manage.get_op(7).is_none());
    assert_eq!(manage.get_op_by_name("first").map(|op| op.get_index()), Some(0));
    let conflict = manage.register_op(UserPcodeOp::new_unspecialized("first", 2));
    assert!(
        conflict
            .expect_err("conflicting index")
            .to_string()
            .contains("Conflicting indices for userop name first")
    );
    let clash = manage.register_op(UserPcodeOp::new_unspecialized("third", 2));
    assert!(
        clash
            .expect_err("same index")
            .to_string()
            .contains("User op third has same index as second")
    );
}

struct LeafAction {
    base: ActionBase,
}

impl LeafAction {
    fn new(name: &str, group: &str) -> LeafAction {
        LeafAction {
            base: ActionBase::new(0, name, group),
        }
    }
}

impl Action for LeafAction {
    fn base(&self) -> &ActionBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut ActionBase {
        &mut self.base
    }

    fn clone_action(&self, grouplist: &ActionGroupList) -> Option<Box<dyn Action>> {
        if !grouplist.contains(&self.base.basegroup) {
            return None;
        }
        Some(Box::new(LeafAction::new(&self.base.name, &self.base.basegroup)))
    }

    fn apply(&mut self, _data: &mut Funcdata, _glb: &mut Architecture) -> Result<i32> {
        Ok(0)
    }
}

fn build_database() -> ActionDatabase {
    let mut database = ActionDatabase::new();
    let mut universal = ActionRestartGroup::new(RULE_ONCEPERFUNC, "universal", 1);
    universal.add_action(Box::new(LeafAction::new("start", "base")));
    let mut inner = ActionGroup::new(RULE_REPEATAPPLY, "mainloop");
    inner.add_action(Box::new(LeafAction::new("heritage", "base")));
    inner.add_action(Box::new(LeafAction::new("deadcode", "deadcode")));
    universal.add_action(Box::new(inner));
    universal.add_action(Box::new(LeafAction::new("deadcode", "deadcode")));
    database.register_action(UNIVERSALNAME, Box::new(universal));
    database
}

#[test]
fn action_database_derives_groups() {
    let mut database = build_database();
    database.reset_defaults().expect("reset action database");
    assert_eq!(database.get_current_name(), "decompile");
    let current = database.get_current().expect("current action");
    let mut listing = String::new();
    current.print(&mut listing, 0, 0);
    assert_eq!(
        listing,
        action_listing(&[
            (0, "        !  ", 0, "universal"),
            (1, "           ", 1, "start"),
            (2, " repeat    ", 1, "mainloop"),
            (3, "           ", 2, "heritage"),
            (4, "           ", 2, "deadcode"),
            (-1, "", 0, ""),
            (5, "           ", 1, "deadcode")
        ])
    );
    assert!(current.get_sub_action("mainloop:heritage").is_some());
    assert!(current.get_sub_action("deadcode").is_none());
    assert!(current.get_sub_action("universal").is_some());
    assert!(current.set_break_point(4, "universal:mainloop:deadcode"));

    let toggled = database
        .toggle_action("decompile", "deadcode", false)
        .expect("toggle group");
    let toggled = toggled.expect("derived action");
    let mut listing = String::new();
    toggled.print(&mut listing, 0, 0);
    assert_eq!(
        listing,
        action_listing(&[
            (0, "        !  ", 0, "universal"),
            (1, "           ", 1, "start"),
            (2, " repeat    ", 1, "mainloop"),
            (3, "           ", 2, "heritage"),
            (-1, "", 0, "")
        ])
    );

    database.set_group("empty", &["nothing", ""]);
    assert!(database.set_current("empty").expect("derive empty group").is_none());
    assert!(database.set_current("unknowngroup").is_err());
}

fn action_listing(lines: &[(i32, &str, i32, &str)]) -> String {
    let mut res = String::new();
    for (num, flags, depth, name) in lines {
        if *num >= 0 {
            res.push_str(&format!(
                "{:4}{}{}{}",
                num,
                flags,
                " ".repeat((depth * 5 + 2) as usize),
                name
            ));
        }
        res.push('\n');
    }
    res
}

#[test]
fn spanning_write_keeps_cpp_mask_for_short_words() {
    let loader = RawLoadImage::from_bytes("test", image_bytes());
    let spc = test_space(false);
    let image = MemoryImage::new(spc.clone(), 4, 16, &loader);
    let mut overlay = MemoryPageOverlay::new(spc, 4, 16, Some(Box::new(image)));
    overlay.set_value(6, 4, 0xaabbccdd).expect("write spanning value");
    assert_eq!(overlay.get_value(6, 4).expect("read back"), 0xaabbccdf);
}
