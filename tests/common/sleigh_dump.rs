use std::fmt::Write as _;
use std::sync::Arc;

use ghidra_decompiler::address::Address;
use ghidra_decompiler::error::{Error, Result};
use ghidra_decompiler::loadimage::LoadImage;
use ghidra_decompiler::opcodes::{OpCode, get_opname};
use ghidra_decompiler::pcoderaw::VarnodeData;
use ghidra_decompiler::sleigh_arch::{LanguageRegistry, SleighDecoder};
use ghidra_decompiler::translate::{AddrSpaceManager, AssemblyEmit, PcodeEmit, Translate};

struct BufferLoadImage {
    base: u64,
    bytes: Vec<u8>,
}

impl LoadImage for BufferLoadImage {
    fn get_file_name(&self) -> &str {
        "buffer"
    }

    fn load_fill(&self, ptr: &mut [u8], addr: &Address) -> Result<()> {
        let start = addr.get_offset();
        for (index, slot) in ptr.iter_mut().enumerate() {
            let current = start.wrapping_add(index as u64);
            *slot = if current < self.base || current - self.base >= self.bytes.len() as u64 {
                0
            } else {
                self.bytes[(current - self.base) as usize]
            };
        }
        Ok(())
    }

    fn get_arch_type(&self) -> String {
        "buffer".to_string()
    }

    fn adjust_vma(&mut self, _adjust: i64) {}
}

#[derive(Default)]
struct AssemblyCapture {
    mnemonic: String,
    body: String,
}

impl AssemblyEmit for AssemblyCapture {
    fn dump(&mut self, _addr: &Address, mnem: &str, body: &str) {
        self.mnemonic = mnem.to_string();
        self.body = body.to_string();
    }
}

struct PcodeCapture<'a> {
    manager: &'a AddrSpaceManager,
    lines: Vec<String>,
}

fn print_varnode(out: &mut String, manager: &AddrSpaceManager, data: &VarnodeData, space_operand: bool) {
    let name = data.space.as_ref().map(|spc| spc.get_name()).unwrap_or("");
    let _ = write!(out, "({name},");
    if space_operand {
        let referenced = data.get_space_from_const(manager);
        let refname = referenced.as_ref().map(|spc| spc.get_name()).unwrap_or("");
        let _ = write!(out, "space:{refname}");
    } else {
        let _ = write!(out, "0x{:x}", data.offset);
    }
    let _ = write!(out, ",{})", data.size);
}

impl PcodeEmit for PcodeCapture<'_> {
    fn dump(
        &mut self,
        _addr: &Address,
        opc: OpCode,
        outvar: Option<&VarnodeData>,
        vars: &[VarnodeData],
    ) -> ghidra_decompiler::error::Result<()> {
        let mut line = String::new();
        if let Some(outvar) = outvar {
            print_varnode(&mut line, self.manager, outvar, false);
            line.push_str(" = ");
        }
        line.push_str(get_opname(opc));
        for (slot, var) in vars.iter().enumerate() {
            line.push(' ');
            let space_operand = slot == 0 && (opc == OpCode::Load || opc == OpCode::Store);
            print_varnode(&mut line, self.manager, var, space_operand);
        }
        self.lines.push(line);
        Ok(())
    }
}

fn escape_text(text: &str) -> String {
    let mut result = String::new();
    for character in text.chars() {
        match character {
            '\n' => result.push_str("\\n"),
            '\t' => result.push_str("\\t"),
            '\r' => result.push_str("\\r"),
            other => result.push(other),
        }
    }
    result
}

fn error_kind(err: &Error) -> &'static str {
    match err {
        Error::Unimpl { .. } => "UnimplError",
        Error::BadData(_) => "BadDataError",
        _ => "LowlevelError",
    }
}

fn print_error(out: &mut Vec<String>, addr: &Address, phase: &str, kind: &str, message: &str) {
    out.push(format!(
        "E\t0x{:x}\t{phase}\t{kind}\t{}",
        addr.get_offset(),
        escape_text(message)
    ));
}

struct Snapshot {
    sleigh: ghidra_decompiler::sleigh::SleighState,
    context: ghidra_decompiler::globalcontext::ContextInternal,
}

fn snapshot(decoder: &SleighDecoder) -> Snapshot {
    Snapshot {
        sleigh: decoder.sleigh.save_state(),
        context: decoder.context.lock().expect("context lock").duplicate(),
    }
}

fn restore(decoder: &SleighDecoder, snap: &Snapshot) {
    decoder.sleigh.restore_state(snap.sleigh.clone());
    *decoder.context.lock().expect("context lock") = snap.context.duplicate();
}

fn probe_delay_slots(decoder: &SleighDecoder, addr: &Address) -> Result<String> {
    let manager = decoder.sleigh.manager();
    let shape = decoder.sleigh.obtain_pcode_context(addr)?;
    let mut fall_offset = shape.length;
    let mut byte_count = 0;
    while byte_count < shape.delay_slot {
        let delay_address = addr + fall_offset as i64;
        let delay_shape = decoder.sleigh.obtain_pcode_context(&delay_address)?;
        if delay_shape.delay_slot > 0 {
            let nested = probe_delay_slots(decoder, &delay_address)?;
            if !nested.is_empty() {
                return Ok(nested);
            }
        } else {
            let mut scratch = PcodeCapture {
                manager,
                lines: Vec::new(),
            };
            match decoder.sleigh.one_instruction(&mut scratch, &delay_address) {
                Err(Error::Unimpl { message, .. }) => return Ok(message),
                Err(err) => return Err(err),
                Ok(_) => {}
            }
        }
        fall_offset += delay_shape.length;
        byte_count += delay_shape.length;
    }
    Ok(String::new())
}

fn unimplemented_delay_slot(decoder: &SleighDecoder, addr: &Address) -> Result<String> {
    let shape = decoder.sleigh.obtain_pcode_context(addr)?;
    if shape.delay_slot <= 0 {
        return Ok(String::new());
    }
    let manager = decoder.sleigh.manager();
    let snap = snapshot(decoder);
    let mut scratch = PcodeCapture {
        manager,
        lines: Vec::new(),
    };
    let real = decoder.sleigh.one_instruction(&mut scratch, addr);
    restore(decoder, &snap);
    if !matches!(real, Err(Error::Unimpl { .. })) {
        return Ok(String::new());
    }
    let message = probe_delay_slots(decoder, addr).unwrap_or_default();
    restore(decoder, &snap);
    Ok(message)
}

pub fn dump_language(
    registry: &LanguageRegistry,
    language: &str,
    base: u64,
    bytes: Vec<u8>,
    overrides: &[(String, u32)],
) -> Vec<String> {
    let mut out = Vec::new();
    out.push(format!("language\t{language}"));
    out.push(format!("base\t0x{base:x}"));
    out.push(format!("size\t{}", bytes.len()));
    for (name, value) in overrides {
        out.push(format!("context\t{name}={value}"));
    }
    let size = bytes.len() as u64;
    let loader = Arc::new(BufferLoadImage { base, bytes });
    let decoder = registry
        .build_decoder(&format!("{language}:default"), loader)
        .and_then(|decoder| {
            for (name, value) in overrides {
                decoder.set_context_override(name, *value)?;
            }
            Ok(decoder)
        });
    let decoder = match decoder {
        Ok(decoder) => decoder,
        Err(err) => {
            let kind = if matches!(err, Error::Decoder(_)) {
                "DecoderError"
            } else {
                "LowlevelError"
            };
            out.push(format!("loaderror\t{kind}\t{}", escape_text(err.explain())));
            out.push("exit\t1".to_string());
            return out;
        }
    };
    let translate: &dyn Translate = &decoder.sleigh;
    let manager = translate.manager();
    let alignment = translate.get_alignment().max(1);
    out.push(format!("alignment\t{alignment}"));
    let code_space = manager.get_default_code_space().expect("default code space");
    out.push(format!(
        "codespace\t{}\t{}",
        code_space.get_name(),
        code_space.get_word_size()
    ));
    let end_offset = base + size;
    let mut addr = Address::new(code_space.clone(), base);
    while addr.get_offset() >= base && addr.get_offset() < end_offset {
        let mut assembly = AssemblyCapture::default();
        let assembly_length = match translate.print_assembly(&mut assembly, &addr) {
            Ok(length) if length > 0 => length,
            Ok(_) => {
                print_error(
                    &mut out,
                    &addr,
                    "assembly",
                    "LowlevelError",
                    "non-positive instruction length",
                );
                let next = (addr.get_offset() / alignment as u64 + 1) * alignment as u64;
                addr = Address::new(code_space.clone(), next);
                continue;
            }
            Err(err) => {
                print_error(&mut out, &addr, "assembly", error_kind(&err), err.explain());
                let next = (addr.get_offset() / alignment as u64 + 1) * alignment as u64;
                addr = Address::new(code_space.clone(), next);
                continue;
            }
        };
        out.push(format!(
            "I\t0x{:x}\t{assembly_length}\t{}\t{}",
            addr.get_offset(),
            escape_text(&assembly.mnemonic),
            escape_text(&assembly.body)
        ));
        let mut pcode = PcodeCapture {
            manager,
            lines: Vec::new(),
        };
        let result = match unimplemented_delay_slot(&decoder, &addr) {
            Err(err) => Err(err),
            Ok(message) if !message.is_empty() => Err(Error::Unimpl {
                message,
                instruction_length: 0,
            }),
            Ok(_) => translate.one_instruction(&mut pcode, &addr),
        };
        match result {
            Err(err) => print_error(&mut out, &addr, "pcode", error_kind(&err), err.explain()),
            Ok(length) => {
                for line in pcode.lines.iter() {
                    out.push(format!("P\t{line}"));
                }
                out.push(format!("L\t{length}"));
            }
        }
        addr = &addr + assembly_length as i64;
    }
    out.push("end".to_string());
    out.push("exit\t0".to_string());
    out
}
