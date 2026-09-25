mod common;

use std::fmt::Write as _;
use std::sync::Arc;

use common::DummyTranslate;
use ghidra_decompiler::address::*;
use ghidra_decompiler::error::{Error, Result};
use ghidra_decompiler::float::FloatFormat;
use ghidra_decompiler::globalcontext::{ContextCache, ContextDatabase, ContextInternal, TrackedContext};
use ghidra_decompiler::istream::{self, Basefield};
use ghidra_decompiler::marshal::*;
use ghidra_decompiler::opcodes::{OpCode, get_opname};
use ghidra_decompiler::pcoderaw::VarnodeData;
use ghidra_decompiler::space::{AddrSpace, SpaceRef};
use ghidra_decompiler::translate::{AddrSpaceManager, JoinRecord, PcodeEmit, TruncationTag};

const SPACES_XML: &str = concat!(
    "<spaces defaultspace=\"ram\">",
    "<space_other name=\"OTHER\" index=\"1\" size=\"8\" bigendian=\"false\" delay=\"0\" physical=\"true\"/>",
    "<space name=\"ram\" index=\"2\" size=\"8\" bigendian=\"false\" delay=\"1\" deadcodedelay=\"2\" physical=\"true\"/>",
    "<space name=\"register\" index=\"3\" size=\"4\" bigendian=\"false\" delay=\"0\" physical=\"true\"/>",
    "<space_unique name=\"unique\" index=\"4\" size=\"4\" bigendian=\"false\" delay=\"0\" physical=\"true\"/>",
    "<space name=\"bram\" index=\"5\" size=\"4\" bigendian=\"true\" delay=\"1\" physical=\"true\"/>",
    "<space name=\"code16\" index=\"6\" size=\"2\" wordsize=\"2\" bigendian=\"false\" delay=\"1\" physical=\"true\"/>",
    "<space name=\"data4\" index=\"7\" size=\"3\" wordsize=\"4\" bigendian=\"true\" delay=\"1\" physical=\"true\"/>",
    "<space_base name=\"stack\" index=\"8\" size=\"8\" bigendian=\"false\" delay=\"1\" physical=\"true\" contain=\"ram\"/>",
    "<space_overlay name=\"ovl\" index=\"9\" base=\"ram\"/>",
    "<space name=\"Tiny\" index=\"10\" size=\"1\" bigendian=\"false\" delay=\"1\" physical=\"true\"/>",
    "<space name=\"register2\" index=\"11\" size=\"4\" bigendian=\"false\" delay=\"0\" physical=\"true\"/>",
    "<space name=\"rom\" index=\"12\" size=\"6\" bigendian=\"true\" delay=\"1\" physical=\"false\"/>",
    "</spaces>"
);

fn unhex(text: &str) -> Vec<u8> {
    if text == "-" {
        return Vec::new();
    }
    (0..text.len() / 2)
        .map(|index| u8::from_str_radix(&text[index * 2..index * 2 + 2], 16).expect("valid hex digit pair"))
        .collect()
}

fn unhex_string(text: &str) -> String {
    String::from_utf8(unhex(text)).expect("utf8 command text")
}

fn tohex(bytes: &[u8]) -> String {
    let mut out = String::new();
    for byte in bytes {
        let _ = write!(out, "{byte:02x}");
    }
    out
}

fn flag(value: bool) -> u8 {
    value as u8
}

fn setup() -> DummyTranslate {
    let mut trans = DummyTranslate::default();
    {
        let manager = &trans.base.manager;
        let mut decoder = XmlDecode::new(Some(manager), 0);
        decoder
            .ingest_stream(SPACES_XML.as_bytes())
            .expect("spaces document parses");
        manager.decode_spaces(&mut decoder).expect("spaces decode");
        manager
            .insert_space(Arc::new(AddrSpace::new_join(manager, false, 13)))
            .expect("join space");
    }
    let manager = &trans.base.manager;
    let reg = manager.get_space_by_name("register").expect("register space");
    let bram = manager.get_space_by_name("bram").expect("bram space");
    let registers = [
        ("eax", &reg, 0, 4),
        ("ax", &reg, 0, 2),
        ("ebx", &reg, 4, 4),
        ("ecx", &reg, 8, 4),
        ("edx", &reg, 0xc, 4),
        ("rdx", &reg, 8, 8),
        ("sp", &reg, 0x20, 8),
        ("hi", &bram, 0x100, 4),
        ("lo", &bram, 0x104, 4),
        ("hilo", &bram, 0x100, 8),
    ];
    let mut table = std::collections::BTreeMap::new();
    for (name, space, offset, size) in registers {
        table.insert(name.to_string(), VarnodeData::new((*space).clone(), offset, size));
    }
    let stack = manager.get_space_by_name("stack").expect("stack space");
    manager
        .add_spacebase_pointer(&stack, &table["sp"], 8, true)
        .expect("stack pointer");
    trans.registers = table;
    trans
}

struct Probe {
    trans: DummyTranslate,
    rangelist: RangeList,
    context: ContextInternal,
    cache: ContextCache,
    tracked: Option<(Address, Address, Vec<TrackedContext>)>,
}

fn attrib_by_name(nm: &str) -> AttributeId {
    let table = [
        ATTRIB_ALIGN,
        ATTRIB_BIGENDIAN,
        ATTRIB_NAME,
        ATTRIB_SIZE,
        ATTRIB_SPACE,
        ATTRIB_VAL,
        ATTRIB_VALUE,
        ATTRIB_OFFSET,
        ghidra_decompiler::space::ATTRIB_PIECE,
        ATTRIB_FORMAT,
        ATTRIB_ID,
        ATTRIB_CONTENT,
        ATTRIB_STORAGE,
        ATTRIB_UNKNOWN,
        ghidra_decompiler::translate::ATTRIB_CODE,
    ];
    table
        .into_iter()
        .find(|attrib| attrib.get_name() == nm)
        .unwrap_or(ATTRIB_UNKNOWN)
}

struct AttrSpec {
    kind: u8,
    name: String,
    value: String,
}

fn parse_spec(text: &str) -> Vec<AttrSpec> {
    let mut res = Vec::new();
    for item in text.split(';') {
        if item.len() < 3 {
            continue;
        }
        let kind = item.as_bytes()[0];
        let rest = &item[2..];
        let (name, value) = match rest.find('=') {
            Some(eq) => (&rest[..eq], &rest[eq + 1..]),
            None => (rest, ""),
        };
        res.push(AttrSpec {
            kind,
            name: name.to_string(),
            value: value.to_string(),
        });
    }
    res
}

fn encode_spec(encoder: &mut dyn Encoder, specs: &[AttrSpec], manager: &AddrSpaceManager) {
    encoder.open_element(ELEM_DATA);
    for spec in specs {
        let attrib = attrib_by_name(&spec.name);
        match spec.kind {
            b'S' => {
                encoder.write_signed_integer(attrib, u64::from_str_radix(&spec.value, 16).expect("hex value") as i64)
            }
            b'U' => encoder.write_unsigned_integer(attrib, u64::from_str_radix(&spec.value, 16).expect("hex value")),
            b'B' => encoder.write_bool(attrib, spec.value == "1"),
            b'T' => encoder.write_string(attrib, &spec.value),
            b'P' => {
                let spc = manager
                    .get_space(spec.value.parse().expect("space index"))
                    .expect("space exists");
                encoder.write_space(attrib, &spc);
            }
            b'O' => encoder.write_opcode(
                attrib,
                OpCode::from_index(spec.value.parse().expect("opcode")).expect("opcode"),
            ),
            b'I' => {
                encoder.write_string_indexed(attrib, spec.value[..1].parse().expect("index digit"), &spec.value[1..])
            }
            _ => {}
        }
    }
    encoder.open_element(ELEM_VAL);
    encoder.close_element(ELEM_VAL);
    encoder.close_element(ELEM_DATA);
}

fn read_one(decoder: &mut dyn Decoder, kind: u8, attrib: Option<AttributeId>) -> String {
    let result: Result<String> = match kind {
        b'S' => match attrib {
            Some(attrib) => decoder.read_signed_integer_attr(attrib),
            None => decoder.read_signed_integer(),
        }
        .map(|value| format!("{:x}", value as u64)),
        b'U' => match attrib {
            Some(attrib) => decoder.read_unsigned_integer_attr(attrib),
            None => decoder.read_unsigned_integer(),
        }
        .map(|value| format!("{value:x}")),
        b'B' => match attrib {
            Some(attrib) => decoder.read_bool_attr(attrib),
            None => decoder.read_bool(),
        }
        .map(|value| format!("{}", value as u8)),
        b'T' => match attrib {
            Some(attrib) => decoder.read_string_attr(attrib),
            None => decoder.read_string(),
        }
        .map(|value| tohex(value.as_bytes())),
        b'P' => match attrib {
            Some(attrib) => decoder.read_space_attr(attrib),
            None => decoder.read_space(),
        }
        .map(|spc| spc.get_name().to_string()),
        b'O' => match attrib {
            Some(attrib) => decoder.read_opcode_attr(attrib),
            None => decoder.read_opcode(),
        }
        .map(|opc| get_opname(opc).to_string()),
        b'E' => match attrib {
            Some(attrib) => decoder.read_signed_integer_expect_string_attr(attrib, "hello", 0x99),
            None => decoder.read_signed_integer_expect_string("hello", 0x99),
        }
        .map(|value| format!("{:x}", value as u64)),
        b'I' => decoder
            .get_indexed_attribute_id(ghidra_decompiler::space::ATTRIB_PIECE)
            .map(|value| format!("{value}")),
        _ => Ok("skip".to_string()),
    };
    match result {
        Ok(text) => text,
        Err(Error::Decoder(message)) => format!("DERR:{}", tohex(message.as_bytes())),
        Err(err) => format!("LERR:{}", tohex(err.explain().as_bytes())),
    }
}

fn decode_spec(decoder: &mut dyn Decoder, data: &[u8], reads: &[u8], specs: &[AttrSpec]) -> String {
    let mut out = String::new();
    let outcome = (|| -> Result<()> {
        decoder.ingest_stream(data)?;
        let el = decoder.open_element_expect(ELEM_DATA)?;
        let mut index = 0;
        loop {
            let id = decoder.get_next_attribute_id()?;
            if id == 0 {
                break;
            }
            let kind = reads.get(index).copied().unwrap_or(b'X');
            index += 1;
            let text = read_one(decoder, kind, None);
            let _ = write!(out, "{id}={text},");
        }
        out.push('|');
        for (slot, spec) in specs.iter().enumerate() {
            let kind = reads.get(slot).copied().unwrap_or(b'X');
            if kind == b'I' {
                continue;
            }
            let text = read_one(decoder, kind, Some(attrib_by_name(&spec.name)));
            let _ = write!(out, "{text},");
        }
        let _ = write!(out, "|{}", decoder.peek_element()?);
        let child = decoder.open_element()?;
        let _ = write!(out, " {child}");
        decoder.close_element(child)?;
        decoder.close_element(el)?;
        out.push_str(" done");
        Ok(())
    })();
    match outcome {
        Ok(()) => {}
        Err(Error::Decoder(message)) => {
            let _ = write!(out, " DERR:{}", tohex(message.as_bytes()));
        }
        Err(err) => {
            let _ = write!(out, " LERR:{}", tohex(err.explain().as_bytes()));
        }
    }
    out
}

#[derive(Default)]
struct PrintEmit {
    out: String,
}

impl PcodeEmit for PrintEmit {
    fn dump(
        &mut self,
        _addr: &Address,
        opc: OpCode,
        outvar: Option<&VarnodeData>,
        vars: &[VarnodeData],
    ) -> ghidra_decompiler::error::Result<()> {
        self.out.push_str(get_opname(opc));
        if let Some(outvar) = outvar {
            let _ = write!(self.out, " out={}:{}", print_addr(&outvar.get_addr()), outvar.size);
        }
        for var in vars {
            let _ = write!(self.out, " in={}:{}", print_addr(&var.get_addr()), var.size);
        }
        Ok(())
    }
}

struct Args<'a> {
    tokens: std::str::SplitWhitespace<'a>,
}

impl<'a> Args<'a> {
    fn word(&mut self) -> &'a str {
        self.tokens.next().unwrap_or("")
    }

    fn num(&mut self) -> u64 {
        u64::from_str_radix(self.word(), 16).expect("hex argument")
    }

    fn inum(&mut self) -> i32 {
        self.word().parse().expect("decimal argument")
    }
}

fn error_text(err: &Error) -> String {
    match err {
        Error::Decoder(message) => format!("DERROR {message}"),
        other => format!("ERROR {}", other.explain()),
    }
}

fn print_addr(addr: &Address) -> String {
    let mut out = String::new();
    addr.print_raw(&mut out);
    out
}

fn stream_number(addr: &Address, value: i64) -> String {
    if addr.print_raw_leaves_hex() == Some(true) {
        format!("{:x}", value as i32 as u32)
    } else {
        format!("{value}")
    }
}

impl Probe {
    fn new() -> Probe {
        Probe {
            trans: setup(),
            rangelist: RangeList::new(),
            context: ContextInternal::new(),
            cache: ContextCache::new(),
            tracked: None,
        }
    }

    fn manager(&self) -> &AddrSpaceManager {
        &self.trans.base.manager
    }

    fn spc(&self, args: &mut Args) -> SpaceRef {
        self.manager().get_space(args.inum()).expect("space index")
    }

    fn addr(&self, args: &mut Args) -> Address {
        let spc = self.spc(args);
        Address::new(spc, args.num())
    }

    fn run(&mut self, line: &str) -> String {
        let mut args = Args {
            tokens: line.split_whitespace(),
        };
        let cmd = args.word();
        match self.dispatch(cmd, &mut args) {
            Ok(text) => text,
            Err(err) => format!("UNCAUGHT {}", err.explain()),
        }
    }

    fn dispatch(&mut self, cmd: &str, args: &mut Args) -> Result<String> {
        let mut out = String::new();
        match cmd {
            "space" => {
                let sp = self.spc(args);
                let contain = sp
                    .get_contain()
                    .map_or("none".to_string(), |spc| spc.get_name().to_string());
                let _ = write!(
                    out,
                    "{} {} {} {} {} {} {:x} {:x} {:x} {} {} {} {}{}{}{}{}{}{}{}{}{}{}{}{} {} {} {}",
                    sp.get_name(),
                    sp.get_type() as i32,
                    sp.get_shortcut(),
                    sp.get_index(),
                    sp.get_addr_size(),
                    sp.get_word_size(),
                    sp.get_highest(),
                    sp.get_pointer_lower_bound(),
                    sp.get_pointer_upper_bound(),
                    sp.get_delay(),
                    sp.get_deadcode_delay(),
                    sp.get_minimum_ptr_size(),
                    flag(sp.is_big_endian()),
                    flag(sp.is_heritaged()),
                    flag(sp.does_deadcode()),
                    flag(sp.has_physical()),
                    flag(sp.is_reverse_justified()),
                    flag(sp.is_formal_stack_space()),
                    flag(sp.is_overlay()),
                    flag(sp.is_overlay_base()),
                    flag(sp.is_other_space()),
                    flag(sp.is_truncated()),
                    flag(sp.no_high_ptr_possible()),
                    flag(sp.has_near_pointers()),
                    flag(sp.allows_wrapped_range()),
                    sp.num_spacebase(),
                    flag(sp.stack_grows_negative()),
                    contain
                );
            }
            "shortcut" => {
                let code = args.num() as u8;
                let found = self.manager().get_space_by_shortcut(code as char);
                out.push_str(found.as_ref().map_or("none", |spc| spc.get_name()));
            }
            "printraw" => {
                let addr = self.addr(args);
                out = print_addr(&addr);
            }
            "wrap" => {
                let sp = self.spc(args);
                let _ = write!(out, "{:x}", sp.wrap_offset(args.num()));
            }
            "add" => {
                let addr = self.addr(args);
                let off = args.num() as i64;
                out = format!("{} {}", print_addr(&addr.add(off)), print_addr(&addr.sub(off)));
            }
            "read" => {
                let sp = self.spc(args);
                let text = unhex_string(args.word());
                let mut addr = Address::new(sp, 0);
                match addr.read(&text, self.manager(), Some(&self.trans)) {
                    Ok(size) => out = format!("{:x} {}", addr.get_offset(), size),
                    Err(err) => out = format!("ERROR {}", err.explain()),
                }
            }
            "overlap" => {
                let first = self.addr(args);
                let skip = args.inum();
                let second = self.addr(args);
                let sz = args.inum();
                let _ = write!(out, "{}", first.overlap(skip, &second, sz));
                match first.overlap_join(skip, &second, sz) {
                    Ok(value) => {
                        let _ = write!(out, " {value}");
                    }
                    Err(err) => {
                        let _ = write!(out, " ERROR {}", err.explain());
                    }
                }
            }
            "justified" => {
                let first = self.addr(args);
                let sz = args.inum();
                let second = self.addr(args);
                let sz2 = args.inum();
                let force = args.inum();
                let _ = write!(
                    out,
                    "{} {} {} {}{}{}{}",
                    first.justified_contain(sz, &second, sz2, force != 0),
                    flag(first.contained_by(sz, &second, sz2)),
                    flag(first.is_contiguous(sz, &second, sz2)),
                    flag(first < second),
                    flag(first <= second),
                    flag(first == second),
                    flag(first != second)
                );
            }
            "validrange" => {
                let addr = self.addr(args);
                let _ = write!(out, "{}", flag(addr.is_valid_range(args.num())));
            }
            "join" => {
                let count = args.inum();
                let mut pieces = Vec::new();
                for _ in 0..count {
                    let space = self.spc(args);
                    let offset = args.num();
                    let size = args.inum() as u32;
                    pieces.push(VarnodeData::new(space, offset, size));
                }
                let logical = args.inum() as u32;
                match self.manager().find_add_join(&pieces, logical) {
                    Ok(rec) => {
                        let unified = rec.get_unified();
                        let addr = unified.get_addr();
                        out = format!("{:x} {} {}", addr.get_offset(), unified.size, print_addr(&addr));
                    }
                    Err(err) => out = format!("ERROR {}", err.explain()),
                }
            }
            "joinequiv" => {
                let off = args.num();
                let query = args.num();
                match self.manager().find_join(off) {
                    Ok(rec) => {
                        let (addr, pos) = rec.get_equivalent_address(query);
                        out = print_addr(&addr);
                        if !addr.is_invalid() {
                            let _ = write!(out, " {}", stream_number(&addr, pos as i64));
                        }
                    }
                    Err(err) => out = format!("ERROR {}", err.explain()),
                }
            }
            "renorm" => {
                let mut addr = self.addr(args);
                let sz = args.inum();
                match addr.renormalize(sz) {
                    Ok(()) => out = print_addr(&addr),
                    Err(err) => out = format!("ERROR {}", err.explain()),
                }
            }
            "cjoin" => {
                let first = self.addr(args);
                let sz = args.inum();
                let second = self.addr(args);
                let sz2 = args.inum();
                out = match self
                    .manager()
                    .construct_join_address(&self.trans, &first, sz, &second, sz2)
                {
                    Ok(addr) => print_addr(&addr),
                    Err(err) => format!("ERROR {}", err.explain()),
                };
            }
            "cwrap" => {
                let addr = self.addr(args);
                let sz = args.inum();
                out = match self.manager().construct_wrapping_address(&addr, sz) {
                    Ok(addr) => print_addr(&addr),
                    Err(err) => format!("ERROR {}", err.explain()),
                };
            }
            "cfloat" => {
                let addr = self.addr(args);
                let sz = args.inum();
                let lsz = args.inum();
                out = match self.manager().construct_float_extension_address(&addr, sz, lsz) {
                    Ok(addr) => print_addr(&addr),
                    Err(err) => format!("ERROR {}", err.explain()),
                };
            }
            "strip" => {
                let off = args.num();
                let index = args.inum();
                let result = self
                    .manager()
                    .find_join(off)
                    .and_then(|rec| self.manager().strip_join_piece(&rec, index));
                out = match result {
                    Ok(vn) => format!(
                        "{} {}",
                        print_addr(&vn.get_addr()),
                        stream_number(&vn.get_addr(), vn.size as i64)
                    ),
                    Err(err) => format!("ERROR {}", err.explain()),
                };
            }
            "encode" => {
                let addr = self.addr(args);
                let sz = args.inum();
                let mut xml = XmlEncode::new(true);
                let mut packed = PackedEncode::new();
                let result = if sz < 0 {
                    addr.encode(&mut xml).and_then(|_| addr.encode(&mut packed))
                } else {
                    addr.encode_size(&mut xml, sz)
                        .and_then(|_| addr.encode_size(&mut packed, sz))
                };
                out = match result {
                    Ok(()) => format!("{} {}", tohex(xml.as_bytes()), tohex(packed.as_bytes())),
                    Err(err) => format!("ERROR {}", err.explain()),
                };
            }
            "decode" => {
                let packed = args.inum();
                let data = unhex(args.word());
                let manager = self.manager();
                let result = if packed != 0 {
                    let mut decoder = PackedDecode::new(Some(manager));
                    decoder.set_translate(Some(&self.trans));
                    decoder
                        .ingest_stream(&data)
                        .and_then(|_| Address::decode_size(&mut decoder))
                } else {
                    let mut decoder = XmlDecode::new(Some(manager), 0);
                    decoder.set_translate(Some(&self.trans));
                    decoder
                        .ingest_stream(&data)
                        .and_then(|_| Address::decode_size(&mut decoder))
                };
                out = match result {
                    Ok((addr, size)) => format!("{} {}", print_addr(&addr), stream_number(&addr, size as i64)),
                    Err(err) => error_text(&err),
                };
            }
            "parse" => {
                let text = unhex_string(args.word());
                out = match self.manager().parse_address_simple(&text) {
                    Ok(addr) => print_addr(&addr),
                    Err(err) => format!("ERROR {}", err.explain()),
                };
            }
            "truncate" => {
                let name = unhex_string(args.word());
                let sz = args.inum();
                let document = format!("<truncate_space space=\"{name}\" size=\"{sz}\"/>");
                let manager = self.manager();
                let mut decoder = XmlDecode::new(Some(manager), 0);
                decoder.ingest_stream(document.as_bytes())?;
                let mut tag = TruncationTag::default();
                tag.decode(&mut decoder)?;
                out = match manager.truncate_space(&tag) {
                    Ok(()) => "ok".to_string(),
                    Err(err) => format!("ERROR {}", err.explain()),
                };
            }
            "nearptr" => {
                let sp = self.spc(args);
                let sz = args.inum();
                self.manager().mark_near_pointers(&sp, sz);
                out.push_str("ok");
            }
            "nohighptr" => {
                let sp = self.spc(args);
                let first = args.num();
                let last = args.num();
                self.manager().add_no_high_ptr(&Range::new(sp, first, last));
                out.push_str("ok");
            }
            "highptr" => {
                let addr = self.addr(args);
                let sz = args.inum();
                let _ = write!(out, "{}", flag(self.manager().high_ptr_possible(&addr, sz)));
            }
            "nextspace" => {
                let index = args.inum();
                let sp = if index < 0 {
                    None
                } else {
                    self.manager().get_space(index)
                };
                out = match self.manager().get_next_space_in_order(sp.as_ref()) {
                    None => "null".to_string(),
                    Some(res) if res.is_maximal() => "max".to_string(),
                    Some(res) => res.get_name().to_string(),
                };
            }
            "lastopen" => {
                let sp = self.spc(args);
                let first = args.num();
                let last = args.num();
                let addr = Range::new(sp, first, last).get_last_addr_open(self.manager());
                out = if addr.get_space().is_some_and(|spc| spc.is_maximal()) {
                    format!("max {:x}", addr.get_offset())
                } else {
                    print_addr(&addr)
                };
            }
            "rl_insert" | "rl_remove" => {
                let sp = self.spc(args);
                let first = args.num();
                let last = args.num();
                if cmd == "rl_insert" {
                    self.rangelist.insert_range(&sp, first, last);
                } else {
                    self.rangelist.remove_range(&sp, first, last);
                }
                let _ = write!(out, "{}", self.rangelist.num_ranges());
            }
            "rl_print" => {
                let mut text = String::new();
                self.rangelist.print_bounds(&mut text);
                out = tohex(text.as_bytes());
            }
            "rl_query" => {
                let addr = self.addr(args);
                let sz = args.num();
                let sp = addr.get_space().expect("query address space").clone();
                let describe = |range: Option<&Range>| {
                    range.map_or("none".to_string(), |range| {
                        format!("{:x}-{:x}", range.get_first(), range.get_last())
                    })
                };
                let _ = write!(
                    out,
                    "{} {:x} {} {} {} {}",
                    flag(self.rangelist.in_range(&addr, sz)),
                    self.rangelist.longest_fit(&addr, sz),
                    describe(self.rangelist.get_range(&sp, addr.get_offset())),
                    describe(self.rangelist.get_nearest_range(&sp, addr.get_offset())),
                    describe(self.rangelist.get_last_signed_range(&sp)),
                    flag(self.rangelist.in_range_range(&Range::new(
                        sp.clone(),
                        addr.get_offset(),
                        addr.get_offset().wrapping_add(sz)
                    )))
                );
            }
            "rl_encode" => {
                let mut xml = XmlEncode::new(true);
                self.rangelist.encode(&mut xml);
                out = tohex(xml.as_bytes());
            }
            "rl_clear" => {
                self.rangelist.clear();
                out.push_str("ok");
            }
            "helper" => {
                let val = args.num();
                let first = args.inum();
                let second = args.inum();
                let _ = write!(
                    out,
                    "{:x} {:x} {:x} {:x} {:x} {:x} {:x} {:x} {:x} {:x} {:x} {:x} {} {} {} {} {:x} {} {:x}",
                    calc_mask(first),
                    calc_int_min(first),
                    pcode_right(val, first),
                    pcode_left(val, first),
                    minimalmask(val),
                    sign_extend(val as i64, first) as u64,
                    zero_extend(val as i64, first) as u64,
                    flag(signbit_negative(val, first)),
                    uintb_negate(val, first),
                    sign_extend_size(val, first, second),
                    extend_signbit(val, first, second),
                    byte_swap(val, first),
                    leastsigbit_set(val),
                    mostsigbit_set(val),
                    popcount(val),
                    count_leading_zeros(val),
                    coveringmask(val),
                    bit_transitions(val, first),
                    byte_swap_signed(val as i64, first) as u64
                );
            }
            "istream" => {
                let kind = args.word();
                let base = match args.word() {
                    "auto" => Basefield::Auto,
                    "hex" => Basefield::Hex,
                    "dec" => Basefield::Dec,
                    _ => Basefield::Oct,
                };
                let text = unhex_string(args.word());
                out = match kind {
                    "u64" => format!("{:x}", istream::read_u64(&text, base, 7)),
                    "i64" => format!("{:x}", istream::read_i64(&text, base, 7) as u64),
                    "u32" => format!("{:x}", istream::read_u32(&text, base, 7)),
                    _ => format!("{:x}", istream::read_i32(&text, base, 7) as u32),
                };
            }
            "strtoul" => {
                let text = unhex(args.word());
                let (value, end) = istream::strtoul(&text, 0);
                out = format!("{value:x} {end}");
            }
            "fhost" => {
                let size = args.inum();
                let enc = args.num();
                let format = FloatFormat::new(size);
                let (value, class) = format.get_host_float(enc);
                out = format!(
                    "{:x} {} {} {:x}",
                    value.to_bits(),
                    class as i32,
                    format.get_class(enc) as i32,
                    format.get_encoding(value)
                );
            }
            "fenc" => {
                let size = args.inum();
                let value = f64::from_bits(args.num());
                out = format!("{:x}", FloatFormat::new(size).get_encoding(value));
            }
            "fprint" => {
                let size = args.inum();
                let value = f64::from_bits(args.num());
                let format = FloatFormat::new(size);
                out = format!(
                    "{} {}",
                    format.print_decimal(value, false),
                    format.print_decimal(value, true)
                );
            }
            "fop" => {
                let size = args.inum();
                let first = args.num();
                let second = args.num();
                let ff = FloatFormat::new(size);
                let f4 = FloatFormat::new(4);
                let f8 = FloatFormat::new(8);
                let _ = write!(
                    out,
                    "{:x}{:x}{:x}{:x}{:x} {:x} {:x} {:x} {:x} {:x} {:x} {:x} {:x} {:x} {:x} {:x} {:x} {:x} {:x} {:x} {:x} {:x} {:x} {:x} {:x}",
                    ff.op_equal(first, second),
                    ff.op_not_equal(first, second),
                    ff.op_less(first, second),
                    ff.op_less_equal(first, second),
                    ff.op_nan(first),
                    ff.op_add(first, second),
                    ff.op_sub(first, second),
                    ff.op_mult(first, second),
                    ff.op_div(first, second),
                    ff.op_neg(first),
                    ff.op_abs(first),
                    ff.op_sqrt(first),
                    ff.op_ceil(first),
                    ff.op_floor(first),
                    ff.op_round(first),
                    ff.op_trunc(first, 1),
                    ff.op_trunc(first, 2),
                    ff.op_trunc(first, 4),
                    ff.op_trunc(first, 8),
                    ff.op_int2float(first, 1),
                    ff.op_int2float(first, 2),
                    ff.op_int2float(first, 4),
                    ff.op_int2float(first, 8),
                    ff.op_float2float(first, &f4),
                    ff.op_float2float(first, &f8)
                );
            }
            "ctx_register" => {
                let name = args.word();
                let sbit = args.inum();
                let ebit = args.inum();
                out = match self.context.register_variable(name, sbit, ebit) {
                    Ok(()) => format!("{}", self.context.get_context_size()),
                    Err(err) => format!("ERROR {}", err.explain()),
                };
            }
            "ctx_default" => {
                let name = args.word();
                let value = args.num() as u32;
                out = match self
                    .context
                    .set_variable_default(name, value)
                    .and_then(|_| self.context.get_default_value_by_name(name))
                {
                    Ok(value) => format!("{value:x}"),
                    Err(err) => format!("ERROR {}", err.explain()),
                };
            }
            "ctx_setvar" => {
                let name = args.word();
                let addr = self.addr(args);
                let value = args.num() as u32;
                out = match self.context.set_variable(name, &addr, value) {
                    Ok(()) => "ok".to_string(),
                    Err(err) => format!("ERROR {}", err.explain()),
                };
            }
            "ctx_region" => {
                let name = args.word();
                let first = self.addr(args);
                let second = self.addr(args);
                let value = args.num() as u32;
                out = match self.context.set_variable_region(name, &first, &second, value) {
                    Ok(()) => "ok".to_string(),
                    Err(err) => format!("ERROR {}", err.explain()),
                };
            }
            "ctx_changepoint" => {
                let addr = self.addr(args);
                let word = args.inum();
                let mask = args.num() as u32;
                let value = args.num() as u32;
                self.context.set_context_change_point(&addr, word, mask, value);
                out.push_str("ok");
            }
            "ctx_get" => {
                let name = args.word();
                let addr = self.addr(args);
                match self.context.get_variable_value(name, &addr) {
                    Ok(value) => {
                        let bounds = self.context.get_context_bounds(&addr);
                        let _ = write!(out, "{:x} {:x} {:x}", value, bounds.first, bounds.last);
                        for word in self.context.get_context(&addr) {
                            let _ = write!(out, " {word:x}");
                        }
                    }
                    Err(err) => out = format!("ERROR {}", err.explain()),
                }
            }
            "ctx_tracked" => {
                let first = self.addr(args);
                let second = self.addr(args);
                self.context.create_set(&first, &second);
                self.tracked = Some((first, second, Vec::new()));
                out.push_str("ok");
            }
            "ctx_trackadd" => {
                let sp = self.spc(args);
                let offset = args.num();
                let size = args.inum() as u32;
                let val = args.num();
                let (first, second, items) = self.tracked.as_mut().expect("tracked set is open");
                items.push(TrackedContext {
                    loc: VarnodeData::new(sp, offset, size),
                    val,
                });
                let set = self.context.create_set(first, second);
                set.extend(items.iter().cloned());
                let _ = write!(out, "{}", set.len());
            }
            "ctx_trackval" => {
                let sp = self.spc(args);
                let offset = args.num();
                let size = args.inum() as u32;
                let point = self.addr(args);
                let mem = VarnodeData::new(sp, offset, size);
                let _ = write!(out, "{:x}", self.context.get_tracked_value(&mem, &point));
            }
            "ctx_encode" => {
                let mut xml = XmlEncode::new(true);
                self.context.encode(&mut xml)?;
                out = tohex(xml.as_bytes());
            }
            "mcodec" => {
                let specs = parse_spec(&unhex_string(args.word()));
                let reads = unhex(args.word());
                let manager = self.manager();
                let mut xml = XmlEncode::new(true);
                encode_spec(&mut xml, &specs, manager);
                let mut packed = PackedEncode::new();
                encode_spec(&mut packed, &specs, manager);
                let mut xml_decoder = XmlDecode::new(Some(manager), 0);
                let mut packed_decoder = PackedDecode::new(Some(manager));
                let xml_result = decode_spec(&mut xml_decoder, xml.as_bytes(), &reads, &specs);
                let packed_result = decode_spec(&mut packed_decoder, packed.as_bytes(), &reads, &specs);
                out = format!(
                    "{} {} {} {}",
                    tohex(xml.as_bytes()),
                    tohex(packed.as_bytes()),
                    xml_result,
                    packed_result
                );
            }
            "nested" => {
                let depth = args.inum();
                let mut xml = XmlEncode::new(true);
                for index in 0..depth {
                    xml.open_element(ELEM_DATA);
                    if index % 3 == 0 {
                        xml.write_bool(ATTRIB_ALIGN, true);
                    }
                }
                xml.write_string(ATTRIB_CONTENT, "x<y");
                for index in 0..depth {
                    xml.close_element(ELEM_DATA);
                    if index % 2 == 0 {
                        xml.open_element(ELEM_VAL);
                        xml.write_unsigned_integer(ATTRIB_CONTENT, index as u64);
                        xml.close_element(ELEM_VAL);
                    }
                }
                out = tohex(xml.as_bytes());
            }
            "rangedecode" | "rangeprops" | "rldecode" => {
                let data = unhex(args.word());
                let manager = self.manager();
                let mut decoder = XmlDecode::new(Some(manager), 0);
                decoder.set_translate(Some(&self.trans));
                let result = decoder.ingest_stream(&data).and_then(|_| match cmd {
                    "rangedecode" => Range::decode(&mut decoder).map(|range| {
                        let mut text = String::new();
                        range.print_bounds(&mut text);
                        text
                    }),
                    "rangeprops" => {
                        let mut props = RangeProperties::new();
                        props.decode(&mut decoder)?;
                        let range = Range::from_properties(&props, manager, Some(&self.trans))?;
                        let mut text = String::new();
                        range.print_bounds(&mut text);
                        Ok(text)
                    }
                    _ => {
                        let mut list = RangeList::new();
                        list.decode(&mut decoder)?;
                        let mut text = String::new();
                        list.print_bounds(&mut text);
                        Ok(tohex(text.as_bytes()))
                    }
                });
                out = match result {
                    Ok(text) => text,
                    Err(err) => error_text(&err),
                };
            }
            "pcodeop" => {
                let addr = self.addr(args);
                let data = unhex(args.word());
                let manager = self.manager();
                let mut decoder = XmlDecode::new(Some(manager), 0);
                decoder.set_translate(Some(&self.trans));
                let mut emit = PrintEmit::default();
                let result = decoder
                    .ingest_stream(&data)
                    .and_then(|_| emit.decode_op(&addr, &mut decoder));
                out = match result {
                    Ok(()) => emit.out,
                    Err(err) => error_text(&err),
                };
            }
            "merge" => {
                let count = args.inum();
                let mut seq = Vec::new();
                for _ in 0..count {
                    let space = self.spc(args);
                    let offset = args.num();
                    let size = args.inum() as u32;
                    seq.push(VarnodeData::new(space, offset, size));
                }
                JoinRecord::merge_sequence(&mut seq, &self.trans);
                for vn in &seq {
                    let _ = write!(out, "{}:{} ", print_addr(&vn.get_addr()), vn.size);
                }
            }
            "resolve" => {
                let sp = self.spc(args);
                let val = args.num();
                let sz = args.inum();
                let mut full = 0x77u64;
                let res = self
                    .manager()
                    .resolve_constant(&sp, val, sz, &Address::invalid(), &mut full);
                out = format!("{} {:x}", print_addr(&res), full);
            }
            "cache_get" => {
                let addr = self.addr(args);
                let mut buf = [0x55u32; 4];
                self.cache.get_context(&self.context, &addr, &mut buf);
                out = format!("{:x} {:x} {:x} {:x}", buf[0], buf[1], buf[2], buf[3]);
            }
            "cache_set" => {
                let addr = self.addr(args);
                let word = args.inum();
                let mask = args.num() as u32;
                let value = args.num() as u32;
                self.cache.set_context(&mut self.context, &addr, word, mask, value);
                out.push_str("ok");
            }
            "cache_region" => {
                let first = self.addr(args);
                let second = self.addr(args);
                let word = args.inum();
                let mask = args.num() as u32;
                let value = args.num() as u32;
                self.cache
                    .set_context_region(&mut self.context, &first, &second, word, mask, value);
                out.push_str("ok");
            }
            "cache_allow" => {
                self.cache.allow_set(args.inum() != 0);
                out.push_str("ok");
            }
            "ctx_spec" => {
                let data = unhex(args.word());
                let manager = &self.trans.base.manager;
                let mut decoder = XmlDecode::new(Some(manager), 0);
                decoder.set_translate(Some(&self.trans));
                let result = decoder
                    .ingest_stream(&data)
                    .and_then(|_| self.context.decode_from_spec(&mut decoder));
                out = match result {
                    Ok(()) => "ok".to_string(),
                    Err(err) => error_text(&err),
                };
            }
            "ctx_roundtrip" => {
                let mut xml = XmlEncode::new(true);
                self.context.encode(&mut xml)?;
                let mut copy = ContextInternal::new();
                for (name, sbit, ebit) in [
                    ("mode", 0, 3),
                    ("flag", 4, 4),
                    ("big", 8, 23),
                    ("word2", 32, 40),
                    ("top", 60, 63),
                ] {
                    copy.register_variable(name, sbit, ebit)?;
                }
                let manager = self.manager();
                let result = (|| -> Result<String> {
                    if !xml.as_bytes().is_empty() {
                        let mut decoder = XmlDecode::new(Some(manager), 0);
                        decoder.set_translate(Some(&self.trans));
                        decoder.ingest_stream(xml.as_bytes())?;
                        copy.decode(&mut decoder)?;
                    }
                    let mut again = XmlEncode::new(true);
                    copy.encode(&mut again)?;
                    Ok(tohex(again.as_bytes()))
                })();
                out = match result {
                    Ok(text) => text,
                    Err(err) => error_text(&err),
                };
            }
            _ => out = format!("UNKNOWN {cmd}"),
        }
        Ok(out)
    }
}

fn data_path(name: &str) -> String {
    format!("{}/tests/core_data/{}", env!("CARGO_MANIFEST_DIR"), name)
}

#[test]
fn core_behavior_matches_reference() {
    let cases_path = std::env::var("CORE_CASES").unwrap_or_else(|_| data_path("core_cases.txt"));
    let expected_path = std::env::var("CORE_EXPECTED").unwrap_or_else(|_| data_path("core_expected.txt"));
    let cases = std::fs::read_to_string(&cases_path).expect("readable core cases file");
    let expected = std::fs::read_to_string(&expected_path).expect("readable core expected file");
    let mut probe = Probe::new();
    let mut failures = 0;
    let mut total = 0;
    for (case, want) in cases.lines().zip(expected.lines()) {
        total += 1;
        let got = probe.run(case);
        if got != want {
            failures += 1;
            if failures <= 25 {
                eprintln!("line {total}: {case}\n  want {want}\n  got  {got}");
            }
        }
    }
    assert!(total > 0);
    assert_eq!(
        failures, 0,
        "{failures} of {total} core cases differ from the C++ reference"
    );
}
