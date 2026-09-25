use std::sync::Arc;

use ghidra_decompiler::address::Address;
use ghidra_decompiler::error::Error;
use ghidra_decompiler::fspec::{EffectRecord, ParamActive, ParamEntry, ParamListKind, ParamListStandard, ProtoModel};
use ghidra_decompiler::marshal::{Decoder, XmlDecode};
use ghidra_decompiler::modelrules::SizeRestrictedFilter;
use ghidra_decompiler::opcodes::OpCode;
use ghidra_decompiler::pcoderaw::VarnodeData;
use ghidra_decompiler::space::{AddrSpace, SpaceRef};
use ghidra_decompiler::stdsort::{std_partial_sort_full, std_sort};
use ghidra_decompiler::translate::AddrSpaceManager;

#[derive(Clone, Copy, Debug)]
struct Item {
    key: u32,
    tag: u32,
}

struct Lcg {
    state: u64,
}

impl Lcg {
    fn next_value(&mut self) -> u32 {
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.state >> 33) as u32
    }
}

fn fnv(items: &[Item]) -> u64 {
    let mut hash: u64 = 0xcbf29ce484222325;
    for item in items {
        hash ^= item.tag as u64;
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

fn sort_hashes(items: &[Item]) -> (u64, u64) {
    let mut sorted = items.to_vec();
    std_sort(&mut sorted, |first, second| first.key < second.key);
    let mut heaped = items.to_vec();
    std_partial_sort_full(&mut heaped, |first, second| first.key < second.key);
    (fnv(&sorted), fnv(&heaped))
}

#[test]
fn std_sort_matches_libstdcxx() {
    let expected = include_str!("data/prototypes/std_sort_expected.txt");
    let mut lines = expected.lines();
    let sizes = [
        0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 24, 31, 32, 33, 40, 47, 48, 63,
        64, 65, 100, 127, 128, 129, 200, 255, 256, 257, 500, 1000, 2048,
    ];
    let ranges = [1u32, 2, 3, 7, 100, 1000000];
    let mut rng = Lcg {
        state: 0x853c49e6748fea9b,
    };
    let mut check = |size: usize, range: u32, items: &[Item]| {
        let (sorted, heaped) = sort_hashes(items);
        let line = lines.next().expect("missing reference line");
        let actual = format!("{} {} {:016x} {:016x}", size, range, sorted, heaped);
        assert_eq!(actual, line);
    };
    for size in sizes {
        for range in ranges {
            let items: Vec<Item> = (0..size)
                .map(|index| Item {
                    key: rng.next_value() % range,
                    tag: index as u32,
                })
                .collect();
            check(size, range, &items);
        }
    }
    for size in sizes {
        let items: Vec<Item> = (0..size)
            .map(|index| {
                let key = if index % 2 == 0 {
                    (index / 2) as u32
                } else {
                    (size / 2 + index / 2) as u32
                };
                Item {
                    key: key % 5,
                    tag: index as u32,
                }
            })
            .collect();
        check(size, 0, &items);
    }
}

struct Spaces {
    manager: AddrSpaceManager,
    register: SpaceRef,
    stack: SpaceRef,
}

fn build_spaces() -> Spaces {
    let manager = AddrSpaceManager::new();
    let register = Arc::new(AddrSpace::new_processor(
        "register",
        false,
        4,
        1,
        1,
        AddrSpace::HERITAGED | AddrSpace::DOES_DEADCODE,
        0,
        0,
    ));
    manager.insert_space(register.clone()).expect("insert register space");
    let ram = Arc::new(AddrSpace::new_processor(
        "ram",
        false,
        4,
        1,
        2,
        AddrSpace::HERITAGED | AddrSpace::DOES_DEADCODE | AddrSpace::HASPHYSICAL,
        0,
        0,
    ));
    manager.insert_space(ram.clone()).expect("insert ram space");
    let stack = Arc::new(AddrSpace::new_spacebase("stack", false, 3, 4, &ram, 1, true));
    manager.insert_space(stack.clone()).expect("insert stack space");
    Spaces {
        manager,
        register,
        stack,
    }
}

const INPUT_LIST: &str = "<input>\
<pentry minsize=\"1\" maxsize=\"4\"><addr space=\"register\" offset=\"0x30\"/></pentry>\
<pentry minsize=\"1\" maxsize=\"4\"><addr space=\"register\" offset=\"0x2c\"/></pentry>\
<pentry minsize=\"1\" maxsize=\"4\"><addr space=\"register\" offset=\"0x28\"/></pentry>\
<pentry minsize=\"1\" maxsize=\"500\" align=\"4\"><addr offset=\"0\" space=\"stack\"/></pentry>\
</input>";

fn decode_list(spaces: &Spaces, kind: ParamListKind, text: &str) -> ParamListStandard {
    let mut decoder = XmlDecode::new(Some(&spaces.manager), 0);
    decoder.ingest_stream(text.as_bytes()).expect("parameter list parses");
    let mut list = ParamListStandard::new(kind);
    let mut effects: Vec<EffectRecord> = Vec::new();
    list.decode(&mut decoder, &mut effects, true)
        .expect("parameter list decodes");
    list
}

fn reg(spaces: &Spaces, offset: u64) -> Address {
    Address::new(spaces.register.clone(), offset)
}

fn stk(spaces: &Spaces, offset: u64) -> Address {
    Address::new(spaces.stack.clone(), offset)
}

#[test]
fn param_list_decode_and_queries() {
    let spaces = build_spaces();
    let list = decode_list(&spaces, ParamListKind::Standard, INPUT_LIST);
    assert_eq!(list.get_entry().len(), 4);
    let groups: Vec<i32> = list.get_entry().iter().map(|entry| entry.get_group()).collect();
    assert_eq!(groups, vec![0, 1, 2, 3]);
    assert_eq!(list.get_stack_entry(), Some(3));
    assert_eq!(
        list.get_spacebase().map(|spc| spc.get_index()),
        Some(spaces.stack.get_index())
    );
    assert!(list.get_entry()[0].is_first_in_class());
    assert!(!list.get_entry()[1].is_first_in_class());

    assert!(list.possible_param(&reg(&spaces, 0x30), 4));
    assert!(list.possible_param(&reg(&spaces, 0x30), 1));
    assert!(!list.possible_param(&reg(&spaces, 0x31), 1));
    assert!(!list.possible_param(&reg(&spaces, 0x40), 4));

    assert_eq!(
        list.characterize_as_param(&reg(&spaces, 0x30), 4),
        ParamEntry::CONTAINS_JUSTIFIED
    );
    assert_eq!(
        list.characterize_as_param(&reg(&spaces, 0x31), 1),
        ParamEntry::CONTAINS_UNJUSTIFIED
    );
    assert_eq!(
        list.characterize_as_param(&reg(&spaces, 0x30), 8),
        ParamEntry::CONTAINED_BY
    );
    assert_eq!(
        list.characterize_as_param(&reg(&spaces, 0x50), 4),
        ParamEntry::NO_CONTAINMENT
    );

    let mut slot = 0;
    let mut slotsize = 0;
    assert!(list.possible_param_with_slot(&stk(&spaces, 8), 4, &mut slot, &mut slotsize));
    assert_eq!((slot, slotsize), (5, 1));
    assert!(list.possible_param_with_slot(&reg(&spaces, 0x28), 4, &mut slot, &mut slotsize));
    assert_eq!((slot, slotsize), (2, 1));

    assert!(!list.check_join(&reg(&spaces, 0x2c), 4, &reg(&spaces, 0x30), 4));
    assert!(list.check_join(&stk(&spaces, 4), 4, &stk(&spaces, 0), 4));

    let mut res = VarnodeData::default();
    assert!(list.unjustified_container(&reg(&spaces, 0x31), 1, &mut res));
    assert_eq!(res.get_addr(), reg(&spaces, 0x30));
    assert_eq!(res.size, 4);
    assert!(!list.unjustified_container(&reg(&spaces, 0x30), 2, &mut res));
    assert_eq!(list.assumed_extension(&reg(&spaces, 0x30), 1, &mut res), OpCode::Copy);

    let mut biggest = VarnodeData::default();
    assert!(list.get_biggest_contained_param(&reg(&spaces, 0x28), 12, &mut biggest));
    assert_eq!(biggest.get_addr(), reg(&spaces, 0x28));
    assert_eq!(biggest.size, 4);

    let clone = list.clone_list().expect("parameter list clones");
    assert_eq!(clone.get_entry().len(), 4);
    assert!(clone.possible_param(&reg(&spaces, 0x2c), 4));
}

fn trial_signature(active: &ParamActive) -> Vec<(u64, i32, bool, bool)> {
    (0..active.get_num_trials())
        .map(|index| {
            let trial = active.get_trial(index);
            (
                trial.get_address().get_offset(),
                trial.get_size(),
                trial.is_used(),
                trial.is_unref(),
            )
        })
        .collect()
}

#[test]
fn fillin_map_standard() {
    let spaces = build_spaces();
    let list = decode_list(&spaces, ParamListKind::Standard, INPUT_LIST);

    let mut active = ParamActive::new(false);
    active.register_trial(&reg(&spaces, 0x2c), 4);
    active.register_trial(&stk(&spaces, 4), 4);
    active.get_trial_mut(0).mark_active();
    active.get_trial_mut(1).mark_active();
    list.fillin_map(&mut active, &spaces.manager).expect("fillin succeeds");
    assert_eq!(
        trial_signature(&active),
        vec![
            (0x30, 4, true, true),
            (0x2c, 4, true, false),
            (0x28, 4, true, true),
            (0, 4, true, true),
            (4, 4, true, false),
        ]
    );
    assert_eq!(active.get_num_used(), 5);

    let mut subcall = ParamActive::new(true);
    subcall.register_trial(&reg(&spaces, 0x2c), 4);
    subcall.register_trial(&stk(&spaces, 4), 4);
    subcall.get_trial_mut(0).mark_active();
    subcall.get_trial_mut(1).mark_active();
    list.fillin_map(&mut subcall, &spaces.manager).expect("fillin succeeds");
    assert_eq!(
        trial_signature(&subcall),
        vec![
            (0x30, 4, true, true),
            (0x2c, 4, true, false),
            (0x28, 4, false, true),
            (0, 4, false, true),
            (4, 4, false, false),
        ]
    );
    assert_eq!(subcall.get_num_used(), 2);
}

#[test]
fn fillin_map_register_strategy() {
    let spaces = build_spaces();
    let list = decode_list(&spaces, ParamListKind::Register, INPUT_LIST);
    let mut active = ParamActive::new(false);
    active.register_trial(&reg(&spaces, 0x28), 4);
    active.register_trial(&reg(&spaces, 0x44), 4);
    active.register_trial(&reg(&spaces, 0x30), 4);
    active.get_trial_mut(0).mark_active();
    active.get_trial_mut(2).mark_active();
    list.fillin_map(&mut active, &spaces.manager).expect("fillin succeeds");
    let order: Vec<(u64, bool, bool)> = (0..active.get_num_trials())
        .map(|index| {
            let trial = active.get_trial(index);
            (
                trial.get_address().get_offset(),
                trial.is_used(),
                trial.is_definitely_not_used(),
            )
        })
        .collect();
    assert_eq!(
        order,
        vec![(0x30, true, false), (0x28, true, false), (0x44, false, true)]
    );
}

#[test]
fn output_list_fallback() {
    let spaces = build_spaces();
    let text = "<output>\
<pentry minsize=\"1\" maxsize=\"4\"><addr space=\"register\" offset=\"0x30\"/></pentry>\
</output>";
    let list = decode_list(&spaces, ParamListKind::StandardOut, text);
    assert!(list.is_auto_killed_by_call());
    assert!(list.possible_param(&reg(&spaces, 0x31), 1));
    let mut active = ParamActive::new(true);
    active.register_trial(&reg(&spaces, 0x30), 4);
    active.register_trial(&reg(&spaces, 0x2c), 4);
    active.get_trial_mut(0).mark_active();
    active.get_trial_mut(1).mark_active();
    list.fillin_map(&mut active, &spaces.manager).expect("fillin succeeds");
    assert!(active.get_trial(0).is_used());
    assert_eq!(active.get_trial(0).get_address().get_offset(), 0x30);
    assert!(!active.get_trial(1).is_used());
    assert!(active.get_trial(1).is_definitely_not_used());
}

#[test]
fn param_active_split_and_join() {
    let spaces = build_spaces();
    let mut active = ParamActive::new(false);
    active.register_trial(&reg(&spaces, 0x30), 8);
    active.register_trial(&reg(&spaces, 0x40), 4);
    active.split_trial(0, 4).expect("split succeeds");
    let slots: Vec<(u64, i32, i32)> = (0..active.get_num_trials())
        .map(|index| {
            let trial = active.get_trial(index);
            (trial.get_address().get_offset(), trial.get_size(), trial.get_slot())
        })
        .collect();
    assert_eq!(slots, vec![(0x30, 4, 1), (0x34, 4, 2), (0x40, 4, 3)]);
    active.join_trial(1, &reg(&spaces, 0x30), 8).expect("join succeeds");
    let slots: Vec<(u64, i32, i32, bool)> = (0..active.get_num_trials())
        .map(|index| {
            let trial = active.get_trial(index);
            (
                trial.get_address().get_offset(),
                trial.get_size(),
                trial.get_slot(),
                trial.is_used(),
            )
        })
        .collect();
    assert_eq!(slots, vec![(0x30, 8, 1, true), (0x40, 4, 2, false)]);
    match active.join_trial(1, &reg(&spaces, 0x30), 4) {
        Err(Error::Lowlevel(message)) => assert_eq!(message, "Size mismatch when joining parameters"),
        _ => panic!("join with a size mismatch must fail"),
    }
    assert_eq!(active.which_trial(&reg(&spaces, 0x42), 2), 1);
    assert_eq!(active.which_trial(&reg(&spaces, 0x50), 2), -1);
}

#[test]
fn effect_lookup() {
    let spaces = build_spaces();
    let effects = vec![
        EffectRecord::from_varnode_data(
            &VarnodeData::new(spaces.register.clone(), 0x30, 4),
            EffectRecord::KILLEDBYCALL,
        ),
        EffectRecord::from_varnode_data(
            &VarnodeData::new(spaces.register.clone(), 0x40, 8),
            EffectRecord::UNAFFECTED,
        ),
    ];
    assert_eq!(
        ProtoModel::lookup_effect(&effects, &reg(&spaces, 0x44), 4),
        EffectRecord::UNAFFECTED
    );
    assert_eq!(
        ProtoModel::lookup_effect(&effects, &reg(&spaces, 0x3c), 8),
        EffectRecord::UNKNOWN_EFFECT
    );
    assert_eq!(
        ProtoModel::lookup_effect(&effects, &reg(&spaces, 0x31), 2),
        EffectRecord::KILLEDBYCALL
    );
    assert_eq!(
        ProtoModel::lookup_effect(&effects, &reg(&spaces, 0x10), 2),
        EffectRecord::UNKNOWN_EFFECT
    );
    assert_eq!(ProtoModel::lookup_record(&effects, 2, &reg(&spaces, 0x40), 8), 1);
    assert_eq!(ProtoModel::lookup_record(&effects, 2, &reg(&spaces, 0x42), 2), -2);
    assert_eq!(ProtoModel::lookup_record(&effects, 2, &reg(&spaces, 0x10), 4), -1);
    assert_eq!(ProtoModel::lookup_record(&effects, 2, &reg(&spaces, 0x2e), 4), -2);
    assert_eq!(ProtoModel::lookup_record(&effects, 0, &reg(&spaces, 0x30), 4), -1);
}

#[test]
fn size_list_parsing() {
    let mut filter = SizeRestrictedFilter::new_default();
    filter.init_from_size_list("4,8, 16").expect("size list parses");
    let mut bad = SizeRestrictedFilter::new_default();
    match bad.init_from_size_list("4,0") {
        Err(Error::Decoder(message)) => assert_eq!(message, "Bad filter size"),
        _ => panic!("zero size must be rejected"),
    }
    let mut trailing = SizeRestrictedFilter::new_default();
    assert!(trailing.init_from_size_list("4,").is_err());
    let mut junk = SizeRestrictedFilter::new_default();
    assert!(junk.init_from_size_list("4 x").is_err());
    let mut empty = SizeRestrictedFilter::new_default();
    assert!(empty.init_from_size_list("  ").is_ok());
}
