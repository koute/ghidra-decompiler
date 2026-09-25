mod common;

use common::{AnyEncoder, Format, marshal_manager, new_decoder};
use ghidra_decompiler::address::{Address, Range, RangeList};
use ghidra_decompiler::comment::{Comment, CommentDatabase, CommentDatabaseInternal};
use ghidra_decompiler::database::{Database, Scope, ScopeId, Symbol, SymbolId};
use ghidra_decompiler::error::Error;
use ghidra_decompiler::overrides::OverrideRecord;
use ghidra_decompiler::space::SpaceRef;
use ghidra_decompiler::translate::AddrSpaceManager;
use ghidra_decompiler::varmap::{RangeHint, RangeType};
use ghidra_decompiler::varnode::Varnode;

fn ram(manager: &AddrSpaceManager) -> SpaceRef {
    manager.get_space_by_name("ram").expect("ram space")
}

fn global_database(id_by_name: bool) -> (Database, ScopeId) {
    let mut db = Database::new(id_by_name);
    let global = db.scopes.alloc(Scope::new_internal(0, "", 4));
    db.attach_scope(global, None).expect("attach global scope");
    (db, global)
}

fn add_named(db: &mut Database, scope: ScopeId, name: &str) -> SymbolId {
    let sym = db.symbols.alloc(Symbol::new(scope, name, None));
    db.scope_insert_name_tree(scope, sym).expect("insert name");
    sym
}

#[test]
fn scope_name_hash_matches_reference() {
    assert_eq!(Scope::hash_scope_name(0, "std"), 0x675899352895e486);
    assert_eq!(
        Scope::hash_scope_name(0x1234567890abcdef, "Namespace"),
        0x1744f1b0f6488976
    );
    assert_eq!(Scope::hash_scope_name(0, "caf\u{e9}"), 0x609cf58e2956ad60);
}

#[test]
fn scope_tree_from_symbol_names() {
    let (mut db, global) = global_database(true);
    let mut basename = String::new();
    let vector = db
        .find_create_scope_from_symbol_name("std::vector::size", "::", &mut basename, None, 4)
        .expect("create scopes");
    assert_eq!(basename, "size");
    let std_id = Scope::hash_scope_name(0, "std");
    assert_eq!(std_id, 0x675899352895e486);
    assert_eq!(db.scope(vector).get_id(), Scope::hash_scope_name(std_id, "vector"));
    assert_eq!(db.scope_get_full_name(vector, "::"), "std::vector");
    assert_eq!(db.scope_get_full_name(global, "::"), "");

    let mut resolved_base = String::new();
    let resolved = db.resolve_scope_from_symbol_name("std::vector::size", "::", &mut resolved_base, None);
    assert_eq!(resolved, Some(vector));
    assert_eq!(resolved_base, "size");

    let mut template_base = String::new();
    let std_scope = db.resolve_scope_from_symbol_name("std::map<a::b>::x", "::", &mut template_base, None);
    assert_eq!(std_scope, db.resolve_scope(std_id));
    assert_eq!(template_base, "map<a::b>::x");

    let mut missing = String::new();
    assert_eq!(
        db.resolve_scope_from_symbol_name("nope::x", "::", &mut missing, None),
        None
    );

    let std_scope = std_scope.expect("std scope");
    assert!(db.scope_is_sub_scope(vector, std_scope));
    assert!(!db.scope_is_sub_scope(std_scope, vector));
    assert_eq!(db.scope_find_distinguishing_scope(vector, global), Some(std_scope));
    assert_eq!(db.scope_resolve_scope(std_scope, "vector", true), Some(vector));
    assert_eq!(db.scope_resolve_scope(std_scope, "vector", false), Some(vector));

    db.delete_scope(std_scope).expect("delete std");
    assert_eq!(db.resolve_scope(std_id), None);
    assert!(!db.scopes.contains(vector));
    assert!(db.scope(global).children().is_empty());
}

#[test]
fn scope_attach_errors() {
    let (mut db, _global) = global_database(false);
    let second = db.scopes.alloc(Scope::new_internal(0, "", 4));
    assert_eq!(
        db.attach_scope(second, None),
        Err(Error::Lowlevel("Multiple global scopes".to_string()))
    );
    assert!(!db.scopes.contains(second));

    let mut basename = String::new();
    assert_eq!(
        db.find_create_scope_from_symbol_name("a::b", "::", &mut basename, None, 4),
        Err(Error::Lowlevel("Scope name hashes not allowed".to_string()))
    );

    let global = db.get_global_scope();
    let first = db.find_create_scope(7, "first", global, 4).expect("create first");
    assert_eq!(db.find_create_scope(7, "other", global, 4), Ok(first));
    let unnamed = db.scopes.alloc(Scope::new_internal(8, "", 4));
    assert_eq!(
        db.attach_scope(unnamed, global),
        Err(Error::Lowlevel("Non-global scope has empty name".to_string()))
    );
    let duplicate = db.scopes.alloc(Scope::new_internal(7, "dup", 4));
    assert_eq!(
        db.attach_scope(duplicate, global),
        Err(Error::Recov("Duplicate scope id: ".to_string()))
    );
    assert!(!db.scopes.contains(duplicate));
}

#[test]
fn name_tree_deduplication_and_unique_names() {
    let (mut db, global) = global_database(false);
    let first = add_named(&mut db, global, "foo");
    let second = add_named(&mut db, global, "foo");
    assert_eq!(db.symbol(first).name_dedup, 0);
    assert_eq!(db.symbol(second).name_dedup, 1);
    let mut found = Vec::new();
    db.scope_find_by_name(global, "foo", &mut found);
    assert_eq!(found, vec![first, second]);
    assert!(db.scope_is_name_used(global, "foo", None));
    assert!(!db.scope_is_name_used(global, "fo", None));

    assert_eq!(db.scope_make_name_unique(global, "bar").unwrap(), "bar");
    assert_eq!(db.scope_make_name_unique(global, "foo").unwrap(), "foo_00");
    add_named(&mut db, global, "foo_00");
    assert_eq!(db.scope_make_name_unique(global, "foo").unwrap(), "foo_01");
    add_named(&mut db, global, "foo_99");
    add_named(&mut db, global, "foo_ab");
    assert_eq!(db.scope_make_name_unique(global, "foo").unwrap(), "foo_x00100");
    add_named(&mut db, global, "foo_x00100");
    assert_eq!(db.scope_make_name_unique(global, "foo").unwrap(), "foo_x00101");
}

#[test]
fn undefined_names() {
    let (mut db, global) = global_database(false);
    assert_eq!(db.scope_build_undefined_name(global).unwrap(), "$$undef00000000");
    add_named(&mut db, global, "zeta");
    assert_eq!(db.scope_build_undefined_name(global).unwrap(), "$$undef00000000");
    add_named(&mut db, global, "$$undef0000000a");
    assert_eq!(db.scope_build_undefined_name(global).unwrap(), "$$undef0000000b");
    let sym = add_named(&mut db, global, "$$undef0000000b");
    assert!(db.symbol(sym).is_name_undefined());
    assert_eq!(db.scope_build_undefined_name(global).unwrap(), "$$undef0000000c");
    add_named(&mut db, global, "$$undefffffffff");
    assert_eq!(
        db.scope_build_undefined_name(global),
        Err(Error::Lowlevel("Error creating undefined name".to_string()))
    );
}

#[test]
fn rename_and_categories() {
    let (mut db, global) = global_database(false);
    let sym = add_named(&mut db, global, "alpha");
    add_named(&mut db, global, "beta");
    db.scope_rename_symbol(global, sym, "beta").unwrap();
    assert_eq!(db.symbol(sym).name, "beta");
    assert_eq!(db.symbol(sym).name_dedup, 1);
    assert!(db.scope_find_first_by_name(global, "alpha").is_none());

    db.scope_set_category(global, sym, Symbol::FAKE_INPUT as i32, -1);
    assert_eq!(db.symbol(sym).catindex, 0);
    assert_eq!(db.scope_get_category_size(global, Symbol::FAKE_INPUT as i32), 1);
    assert_eq!(
        db.scope_get_category_symbol(global, Symbol::FAKE_INPUT as i32, 0),
        Some(sym)
    );
    db.scope_set_category(global, sym, Symbol::NO_CATEGORY as i32, 0);
    assert_eq!(db.scope_get_category_size(global, Symbol::FAKE_INPUT as i32), 0);

    db.scope_remove_symbol(global, sym);
    assert!(!db.symbols.contains(sym));
    let mut found = Vec::new();
    db.scope_find_by_name(global, "beta", &mut found);
    assert_eq!(found.len(), 1);
}

#[test]
fn property_ranges() {
    let manager = marshal_manager();
    let spc = ram(&manager);
    let (mut db, _global) = global_database(false);
    let range = Range::new(spc.clone(), 0x100, 0x1ff);
    db.set_property_range(Varnode::READONLY, &range, &manager);
    assert_eq!(db.get_property(&Address::new(spc.clone(), 0xff)), 0);
    assert_eq!(db.get_property(&Address::new(spc.clone(), 0x100)), Varnode::READONLY);
    assert_eq!(db.get_property(&Address::new(spc.clone(), 0x1ff)), Varnode::READONLY);
    assert_eq!(db.get_property(&Address::new(spc.clone(), 0x200)), 0);
    db.set_property_range(Varnode::VOLATIL, &Range::new(spc.clone(), 0x180, 0x27f), &manager);
    db.clear_property_range(Varnode::READONLY, &Range::new(spc.clone(), 0x1c0, 0x1cf), &manager);
    assert_eq!(db.get_property(&Address::new(spc.clone(), 0x17f)), Varnode::READONLY);
    assert_eq!(
        db.get_property(&Address::new(spc.clone(), 0x180)),
        Varnode::READONLY | Varnode::VOLATIL
    );
    assert_eq!(db.get_property(&Address::new(spc.clone(), 0x1c4)), Varnode::VOLATIL);
    assert_eq!(
        db.get_property(&Address::new(spc.clone(), 0x1d0)),
        Varnode::READONLY | Varnode::VOLATIL
    );
    assert_eq!(db.get_property(&Address::new(spc.clone(), 0x27f)), Varnode::VOLATIL);
    assert_eq!(db.get_property(&Address::new(spc, 0x280)), 0);
}

#[test]
fn namespace_ranges_map_scopes() {
    let manager = marshal_manager();
    let spc = ram(&manager);
    let (mut db, global) = global_database(false);
    let sub = db.find_create_scope(5, "sub", Some(global), 4).unwrap();
    let mut rlist = RangeList::new();
    rlist.insert_range(&spc, 0x1000, 0x1fff);
    db.set_range(sub, &rlist);
    let inside = Address::new(spc.clone(), 0x1800);
    let outside = Address::new(spc.clone(), 0x2000);
    assert_eq!(db.map_scope(global, &inside, &Address::invalid()), sub);
    assert_eq!(db.map_scope(global, &outside, &Address::invalid()), global);
    assert_eq!(
        db.scope_discover_scope(global, &inside, 4, &Address::invalid()),
        Some(sub)
    );
    assert_eq!(db.scope_discover_scope(global, &outside, 4, &Address::invalid()), None);
    db.add_range(sub, &spc, 0x3000, 0x3fff);
    assert_eq!(
        db.map_scope(global, &Address::new(spc.clone(), 0x3000), &Address::invalid()),
        sub
    );
    db.remove_range(sub, &spc, 0x1000, 0x1fff);
    assert_eq!(db.map_scope(global, &inside, &Address::invalid()), global);
    db.delete_scope(sub).unwrap();
    assert!(db.resolvemap.empty());
}

#[test]
fn comment_database_ordering() {
    let manager = marshal_manager();
    let spc = ram(&manager);
    let func = Address::new(spc.clone(), 0x1000);
    let other = Address::new(spc.clone(), 0x2000);
    let at = Address::new(spc.clone(), 0x1004);
    let mut db = CommentDatabaseInternal::new();
    db.add_comment(Comment::USER1, &func, &at, "first");
    db.add_comment(Comment::WARNING, &func, &at, "second");
    db.add_comment(Comment::HEADER, &func, &func, "head");
    db.add_comment(Comment::USER2, &other, &other, "elsewhere");
    assert!(!db.add_comment_no_duplicate(Comment::USER1, &func, &at, "first"));
    assert!(db.add_comment_no_duplicate(Comment::USER3, &func, &at, "third"));
    let listed: Vec<(String, i32)> = db
        .function_comments(&func)
        .iter()
        .map(|com| (com.get_text().to_string(), com.get_uniq()))
        .collect();
    assert_eq!(
        listed,
        vec![
            ("head".to_string(), 0),
            ("first".to_string(), 0),
            ("second".to_string(), 1),
            ("third".to_string(), 2),
        ]
    );
    db.clear_type(&func, Comment::WARNING | Comment::HEADER);
    let texts: Vec<String> = db
        .function_comments(&func)
        .iter()
        .map(|com| com.get_text().to_string())
        .collect();
    assert_eq!(texts, vec!["first".to_string(), "third".to_string()]);
    assert_eq!(db.function_comments(&other).len(), 1);
}

fn comment_roundtrip(format: Format) {
    let manager = marshal_manager();
    let spc = ram(&manager);
    let func = Address::new(spc.clone(), 0x1000);
    let at = Address::new(spc.clone(), 0x1008);
    let mut db = CommentDatabaseInternal::new();
    db.add_comment(Comment::USER1, &func, &at, "a comment");
    db.add_comment(Comment::WARNINGHEADER, &func, &func, "warn");
    let mut any = AnyEncoder::new(format);
    db.encode(any.encoder()).expect("encode comments");
    let mut decoder = new_decoder(format, &manager);
    decoder.ingest_stream(&any.bytes()).expect("ingest");
    let mut restored = CommentDatabaseInternal::new();
    restored.decode(decoder.as_mut()).expect("decode comments");
    let original: Vec<(u32, String, Address)> = db
        .function_comments(&func)
        .iter()
        .map(|com| (com.get_type(), com.get_text().to_string(), com.get_addr().clone()))
        .collect();
    let decoded: Vec<(u32, String, Address)> = restored
        .function_comments(&func)
        .iter()
        .map(|com| (com.get_type(), com.get_text().to_string(), com.get_addr().clone()))
        .collect();
    assert_eq!(original, decoded);
}

#[test]
fn comment_roundtrip_xml() {
    comment_roundtrip(Format::Xml);
}

#[test]
fn comment_roundtrip_packed() {
    comment_roundtrip(Format::Packed);
}

#[test]
fn comment_type_names() {
    assert_eq!(
        Comment::encode_comment_type("warningheader").unwrap(),
        Comment::WARNINGHEADER
    );
    assert_eq!(
        Comment::encode_comment_type("bogus"),
        Err(Error::Lowlevel("Unknown comment type: bogus".to_string()))
    );
    assert_eq!(Comment::decode_comment_type(Comment::USER3).unwrap(), "user3");
    assert_eq!(
        Comment::decode_comment_type(3),
        Err(Error::Lowlevel("Unknown comment type".to_string()))
    );
}

#[test]
fn override_records() {
    let manager = marshal_manager();
    let spc = ram(&manager);
    let addr = Address::new(spc.clone(), 0x1234);
    let dest = Address::new(spc, 0x5678);
    let mut text = String::new();
    OverrideRecord::allocate_flow("callreturn")
        .unwrap()
        .print_raw(&mut text, &addr);
    OverrideRecord::allocate_call_dest("callother_branch", &dest)
        .unwrap()
        .print_raw(&mut text, &addr);
    let mut expected = String::new();
    expected.push_str(&format!(
        "override BRANCH, BRANCHIND, or RETURN at {} to a CALL followed by a RETURN\n",
        addr
    ));
    expected.push_str(&format!(
        "override CALLOTHER at {} to BRANCH directly to {}\n",
        addr, dest
    ));
    assert_eq!(text, expected);
    assert!(matches!(
        OverrideRecord::allocate_flow("jump"),
        Err(Error::Lowlevel(message)) if message == "Unknown flow override name: jump"
    ));
    assert!(matches!(
        OverrideRecord::allocate_call_dest("branch", &addr),
        Err(Error::Lowlevel(message)) if message == "Unknown call destination override name: branch"
    ));
}

#[test]
fn range_hint_ordering() {
    let base = RangeHint::new(0x10, 4, 0x10, None, 0, RangeType::Fixed, -1);
    let later = RangeHint::new(0x14, 4, 0x14, None, 0, RangeType::Fixed, -1);
    let wider = RangeHint::new(0x10, 8, 0x10, None, 0, RangeType::Fixed, -1);
    let open = RangeHint::new(0x10, 4, 0x10, None, 0, RangeType::Open, -1);
    assert_eq!(base.compare(&later), -1);
    assert_eq!(later.compare(&base), 1);
    assert_eq!(base.compare(&wider), -1);
    assert_eq!(base.compare(&open), -1);
    assert_eq!(base.compare(&base.clone()), 0);
    assert!(wider.contain(&base));
    assert!(base.contain(&wider));
    assert!(!base.contain(&later));
    assert!(wider.contain(&later));
}
