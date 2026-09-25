use std::collections::BTreeMap;

use super::symbols::{ImageSymbols, NamedAddress};
use super::{PcodeOperation, PcodeVarnode, Program};
use crate::opcodes::OpCode;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Location {
    space: String,
    offset: u64,
    size: u32,
}

impl Location {
    fn of(varnode: &PcodeVarnode) -> Location {
        Location {
            space: varnode.space.clone(),
            offset: varnode.offset,
            size: varnode.size,
        }
    }

    fn overlaps(&self, other: &Location) -> bool {
        self.space == other.space
            && self.offset < other.offset + u64::from(other.size)
            && other.offset < self.offset + u64::from(self.size)
    }
}

fn size_mask(size: u32) -> u64 {
    if size >= 8 { u64::MAX } else { (1u64 << (size * 8)) - 1 }
}

fn sign_extension(value: u64, size: u32) -> u64 {
    if size >= 8 {
        return value;
    }
    let shift = 64 - size * 8;
    (((value << shift) as i64) >> shift) as u64
}

const LANDING_PAD_MNEMONICS: [&str; 3] = ["endbr64", "endbr32", "bti"];

#[derive(Clone, Copy)]
struct TrackedValue {
    value: u64,
    first_instruction: Option<u64>,
}

struct ConstantTracker<'program> {
    program: &'program Program,
    got_slot_symbols: &'program BTreeMap<u64, String>,
    values: BTreeMap<Location, TrackedValue>,
    instruction: u64,
    got_slot: Option<(u64, u64)>,
}

impl<'program> ConstantTracker<'program> {
    fn value(&mut self, varnode: &PcodeVarnode) -> Option<TrackedValue> {
        match varnode.space.as_str() {
            "const" => Some(TrackedValue {
                value: varnode.offset,
                first_instruction: None,
            }),
            "register" | "unique" => self.values.get(&Location::of(varnode)).copied(),
            _ => self.load(varnode.offset, varnode.size, Some(self.instruction)),
        }
    }

    fn write(&mut self, output: &PcodeVarnode, value: Option<TrackedValue>) {
        let location = Location::of(output);
        self.values.retain(|known, _| !known.overlaps(&location));
        if let Some(tracked) = value {
            self.values.insert(
                location,
                TrackedValue {
                    value: tracked.value & size_mask(output.size),
                    first_instruction: Some(tracked.first_instruction.unwrap_or(self.instruction)),
                },
            );
        }
    }

    fn load(&mut self, address: u64, size: u32, first_instruction: Option<u64>) -> Option<TrackedValue> {
        let first_instruction = first_instruction.unwrap_or(self.instruction);
        if self.got_slot_symbols.contains_key(&address) {
            self.got_slot = Some((address, first_instruction));
            return None;
        }
        Some(TrackedValue {
            value: self.program.read_unsigned(address, size)?,
            first_instruction: Some(first_instruction),
        })
    }

    fn step(&mut self, operation: &PcodeOperation) -> bool {
        let inputs: Vec<Option<TrackedValue>> = operation.inputs.iter().map(|varnode| self.value(varnode)).collect();
        let first_instruction = inputs
            .iter()
            .flatten()
            .filter_map(|tracked| tracked.first_instruction)
            .min();
        let input = |index: usize| inputs.get(index).copied().flatten().map(|tracked| tracked.value);
        let binary = |combine: fn(u64, u64) -> u64| Some(combine(input(0)?, input(1)?));
        let value = match operation.opcode {
            OpCode::Copy | OpCode::IntZext => input(0),
            OpCode::IntSext => input(0).map(|value| sign_extension(value, operation.inputs[0].size)),
            OpCode::IntAdd => binary(u64::wrapping_add),
            OpCode::IntSub => binary(u64::wrapping_sub),
            OpCode::IntMult => binary(u64::wrapping_mul),
            OpCode::IntAnd => binary(|left, right| left & right),
            OpCode::IntOr => binary(|left, right| left | right),
            OpCode::IntXor => binary(|left, right| left ^ right),
            OpCode::IntLeft => binary(|left, right| left.checked_shl(right as u32).unwrap_or(0)),
            OpCode::IntRight => binary(|left, right| left.checked_shr(right as u32).unwrap_or(0)),
            OpCode::Subpiece => binary(|value, bytes| value.checked_shr((bytes * 8) as u32).unwrap_or(0)),
            OpCode::Load => match (inputs.get(1).copied().flatten(), &operation.output) {
                (Some(address), Some(output)) => self
                    .load(address.value, output.size, address.first_instruction)
                    .map(|tracked| tracked.value),
                _ => None,
            },
            _ => None,
        };
        if let Some(output) = &operation.output {
            let tracked = value.map(|value| TrackedValue {
                value,
                first_instruction,
            });
            self.write(output, tracked);
        }
        matches!(
            operation.opcode,
            OpCode::Branch | OpCode::Branchind | OpCode::Call | OpCode::Callind | OpCode::Return
        )
    }
}

struct DecodedInstruction {
    address: u64,
    mnemonic: String,
}

pub(crate) fn import_stubs(program: &Program, image: &ImageSymbols) -> Vec<NamedAddress> {
    let base_register = image.stub_base_register.as_ref().and_then(|base| {
        let register = program.register(base.register)?;
        let tracked = TrackedValue {
            value: base.value,
            first_instruction: None,
        };
        Some((Location::of(&register), tracked))
    });
    let new_tracker = || ConstantTracker {
        program,
        got_slot_symbols: &image.got_slot_symbols,
        values: base_register.iter().cloned().collect(),
        instruction: 0,
        got_slot: None,
    };
    let mut stubs = Vec::new();
    for section in &image.stub_sections {
        let mut address = section.start;
        let mut tracker = new_tracker();
        let mut stub_instructions: Vec<DecodedInstruction> = Vec::new();
        while address < section.end {
            let decoded = program
                .pcode(address, 1)
                .ok()
                .and_then(|mut list| list.pop())
                .zip(program.disassemble(address, 1).ok().and_then(|mut list| list.pop()));
            let Some((instruction, text)) = decoded else {
                address += 1;
                tracker = new_tracker();
                stub_instructions.clear();
                continue;
            };
            address += instruction.length.max(1) as u64;
            tracker.instruction = instruction.address;
            stub_instructions.push(DecodedInstruction {
                address: instruction.address,
                mnemonic: text.mnemonic.to_ascii_lowercase(),
            });
            let mut is_stub_end = false;
            for operation in &instruction.operations {
                is_stub_end |= tracker.step(operation);
            }
            if !is_stub_end {
                continue;
            }
            if let Some((slot, first_instruction)) = tracker.got_slot
                && let Some(name) = image.got_slot_symbols.get(&slot)
            {
                stubs.push(NamedAddress {
                    name: name.clone(),
                    address: stub_start(&stub_instructions, first_instruction),
                });
            }
            tracker = new_tracker();
            stub_instructions.clear();
        }
    }
    stubs
}

fn stub_start(instructions: &[DecodedInstruction], first_instruction: u64) -> u64 {
    let first_index = instructions
        .iter()
        .position(|instruction| instruction.address == first_instruction)
        .unwrap_or(0);
    instructions[..first_index]
        .iter()
        .rev()
        .take_while(|instruction| LANDING_PAD_MNEMONICS.contains(&instruction.mnemonic.as_str()))
        .last()
        .map_or(first_instruction, |instruction| instruction.address)
}
