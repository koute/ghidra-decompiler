mod demangle;
mod discovery;
mod stubs;
mod symbols;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::Path;
use std::sync::Arc;

use crate::address::Address;
use crate::architecture::{Architecture, ArchitectureBuilder};
use crate::callgraph::CallGraph;
use crate::database::{Database, ScopeId, SymbolId};
use crate::error::{Error, Result};
use crate::loadimage::LoadImageFunc;
use crate::object_arch::{ObjectArchitecture, is_object_file};
use crate::opcodes::{OpCode, get_opname};
use crate::pcoderaw::VarnodeData;
use crate::raw_arch::RawBinaryArchitecture;
use crate::space::SpaceRef;
use crate::translate::{AddrSpaceManager, AssemblyEmit, PcodeEmit};
use crate::types::TypeMetatype;
use crate::xml::DocumentStorage;

pub struct Program {
    architecture: Box<Architecture>,
    functions: BTreeMap<SymbolId, FunctionRecord>,
    data: BTreeMap<u64, DataRecord>,
    string_sections: Vec<std::ops::Range<u64>>,
    code_sections: Vec<std::ops::Range<u64>>,
    entry: Option<u64>,
}

const MIN_STRING_LENGTH: usize = 4;
const MAX_STRING_LENGTH: usize = 4096;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SymbolLoading {
    Loader,
    Full,
}

enum SymbolInput {
    None,
    Loader,
    Full(Box<symbols::ImageSymbols>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FunctionSource {
    SymbolTable,
    DynamicSymbol,
    ImportStub,
    Discovered,
    Requested,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct FunctionEntry {
    pub name: String,
    pub symbol: Option<String>,
    pub address: u64,
    pub source: FunctionSource,
}

struct FunctionRecord {
    name: String,
    loaded_name: String,
    symbol: Option<String>,
    source: FunctionSource,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct DataEntry {
    pub name: String,
    pub symbol: Option<String>,
    pub address: u64,
    pub size: u64,
}

struct DataRecord {
    sym: SymbolId,
    name: String,
    loaded_name: String,
    symbol: Option<String>,
    size: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct Instruction {
    pub address: u64,
    pub length: usize,
    pub bytes: Vec<u8>,
    pub mnemonic: String,
    pub operands: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PcodeVarnode {
    pub space: String,
    pub offset: u64,
    pub size: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PcodeOperation {
    pub opcode: OpCode,
    pub output: Option<PcodeVarnode>,
    pub inputs: Vec<PcodeVarnode>,
    pub space: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InstructionPcode {
    pub address: u64,
    pub length: usize,
    pub operations: Vec<PcodeOperation>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct CallEdge {
    pub caller: u64,
    pub callee: u64,
    pub call_site: u64,
}

impl fmt::Display for PcodeVarnode {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "({},{:#x},{})", self.space, self.offset, self.size)
    }
}

impl fmt::Display for PcodeOperation {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(output) = &self.output {
            write!(formatter, "{output} = ")?;
        }
        formatter.write_str(get_opname(self.opcode))?;
        for (slot, input) in self.inputs.iter().enumerate() {
            match (&self.space, slot) {
                (Some(space), 0) => write!(formatter, " ({},space:{space},{})", input.space, input.size)?,
                _ => write!(formatter, " {input}")?,
            }
        }
        Ok(())
    }
}

struct InstructionText {
    mnemonic: String,
    operands: String,
}

impl AssemblyEmit for InstructionText {
    fn dump(&mut self, _addr: &Address, mnem: &str, body: &str) {
        self.mnemonic = mnem.to_string();
        self.operands = body.to_string();
    }
}

struct OperationCollector<'a> {
    manager: &'a AddrSpaceManager,
    operations: Vec<PcodeOperation>,
}

fn pcode_varnode(data: &VarnodeData) -> PcodeVarnode {
    PcodeVarnode {
        space: data
            .space
            .as_ref()
            .map(|space| space.get_name().to_string())
            .unwrap_or_default(),
        offset: data.offset,
        size: data.size,
    }
}

impl PcodeEmit for OperationCollector<'_> {
    fn dump(&mut self, _addr: &Address, opc: OpCode, outvar: Option<&VarnodeData>, vars: &[VarnodeData]) -> Result<()> {
        let space = match (opc, vars.first()) {
            (OpCode::Load | OpCode::Store, Some(space_operand)) => self
                .manager
                .get_space(space_operand.offset as i32)
                .map(|space| space.get_name().to_string()),
            _ => None,
        };
        self.operations.push(PcodeOperation {
            opcode: opc,
            output: outvar.map(pcode_varnode),
            inputs: vars.iter().map(pcode_varnode).collect(),
            space,
        });
        Ok(())
    }
}

fn string_label(text: &str) -> String {
    text.chars()
        .take(16)
        .map(|character| {
            if character.is_ascii_alphanumeric() {
                character
            } else {
                '_'
            }
        })
        .collect()
}

fn panic_guard<R>(run: impl FnOnce() -> Result<R>) -> Result<R> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(run)).unwrap_or_else(|payload| {
        let message = payload
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| payload.downcast_ref::<&str>().map(|text| text.to_string()))
            .unwrap_or_else(|| "unknown panic".to_string());
        Err(Error::Lowlevel(format!("internal decompiler error: {message}")))
    })
}

impl Program {
    pub fn open(path: &Path, language: Option<&str>) -> Result<Program> {
        Program::open_with(path, language, SymbolLoading::Full)
    }

    pub fn open_with(path: &Path, language: Option<&str>, loading: SymbolLoading) -> Result<Program> {
        let bytes = std::fs::read(path)
            .map_err(|error| Error::Lowlevel(format!("failed to read '{}': {error}", path.display())))?;
        Program::from_image_with(&path.to_string_lossy(), bytes, language, loading)
    }

    pub fn from_image(name: &str, bytes: Vec<u8>, language: Option<&str>) -> Result<Program> {
        Program::from_image_with(name, bytes, language, SymbolLoading::Full)
    }

    pub fn from_image_with(
        name: &str,
        bytes: Vec<u8>,
        language: Option<&str>,
        loading: SymbolLoading,
    ) -> Result<Program> {
        if !is_object_file(&bytes) {
            return Err(Error::Lowlevel(format!("unrecognized executable format: {name}")));
        }
        let symbols = match loading {
            SymbolLoading::Loader => SymbolInput::Loader,
            SymbolLoading::Full => SymbolInput::Full(Box::new(symbols::image_symbols(&bytes))),
        };
        let builder = ObjectArchitecture::with_bytes(name, language.unwrap_or("default"), bytes);
        Program::initialize(Arc::new(builder), symbols)
    }

    pub fn from_raw_bytes(bytes: Vec<u8>, language: &str, base_address: u64) -> Result<Program> {
        let code_end = base_address.saturating_add(bytes.len() as u64);
        let builder = RawBinaryArchitecture::with_bytes("raw", language, bytes, base_address);
        let mut program = Program::initialize(Arc::new(builder), SymbolInput::None)?;
        program.code_sections = std::iter::once(base_address..code_end).collect();
        program.entry = Some(base_address);
        Ok(program)
    }

    fn initialize(builder: Arc<dyn ArchitectureBuilder>, symbols: SymbolInput) -> Result<Program> {
        panic_guard(|| Program::initialize_unguarded(builder, symbols))
    }

    fn initialize_unguarded(builder: Arc<dyn ArchitectureBuilder>, symbols: SymbolInput) -> Result<Program> {
        let mut architecture = Box::new(Architecture::new());
        architecture.builder = Some(builder);
        let mut store = DocumentStorage::new();
        architecture.init(&mut store)?;
        let mut program = Program {
            architecture,
            functions: BTreeMap::new(),
            data: BTreeMap::new(),
            string_sections: Vec::new(),
            code_sections: Vec::new(),
            entry: None,
        };
        match symbols {
            SymbolInput::None => {}
            SymbolInput::Loader => program.architecture.read_loader_symbols()?,
            SymbolInput::Full(image) => program.add_symbols(*image)?,
        }
        Ok(program)
    }

    fn add_symbols(&mut self, image: symbols::ImageSymbols) -> Result<()> {
        self.string_sections = image.string_sections.clone();
        self.code_sections = image.code_sections.clone();
        let loader = self
            .architecture
            .loader
            .clone()
            .ok_or_else(|| Error::Lowlevel("missing load image".to_string()))?;
        self.architecture.loadersymbols_parsed = true;
        let mut named_addresses = BTreeSet::new();
        let mut record = LoadImageFunc::default();
        loader.open_symbols();
        while loader.get_next_symbol(&mut record) {
            if image.undefined_names.contains(&record.name) {
                continue;
            }
            named_addresses.insert(record.address.get_offset());
            self.add_function_symbol(&record.name, &record.address, FunctionSource::SymbolTable)?;
        }
        loader.close_symbols();
        for function in &image.dynamic_functions {
            if named_addresses.insert(function.address) {
                let address = self.code_address(function.address)?;
                self.add_function_symbol(&function.name, &address, FunctionSource::DynamicSymbol)?;
            }
        }
        for data in &image.data_symbols {
            match demangle::demangled_name(&data.name) {
                Some(name) => self.add_data_symbol(&name, Some(&data.name), data.address, data.size),
                None => self.add_data_symbol(&data.name, None, data.address, data.size),
            }
        }
        for (slot, symbol) in &image.got_slot_symbols {
            let name = demangle::demangled_name(symbol).unwrap_or_else(|| symbol.clone());
            self.add_data_symbol(&format!("{name}@got"), Some(symbol), *slot, image.got_slot_size);
        }
        let defined_names: BTreeSet<String> = self.functions.values().map(|record| record.name.clone()).collect();
        for stub in stubs::import_stubs(self, &image) {
            if named_addresses.insert(stub.address) {
                let demangled = demangle::demangled_name(&stub.name).unwrap_or_else(|| stub.name.clone());
                let name = if defined_names.contains(&demangled) {
                    format!("{demangled}@plt")
                } else {
                    demangled
                };
                let symbol = (name != stub.name).then_some(stub.name.as_str());
                let address = self.code_address(stub.address)?;
                self.add_named_function(&name, symbol, &address, FunctionSource::ImportStub)?;
            }
        }
        self.entry = image.entry;
        Ok(())
    }

    fn add_data_symbol(&mut self, name: &str, symbol: Option<&str>, address: u64, size: u64) {
        if let Err(error) = self.add_typed_data_symbol(name, symbol, address, size) {
            self.architecture
                .print_warning(&format!("Data symbol {name} is not added: {}", error.explain()));
        }
    }

    fn add_typed_data_symbol(&mut self, name: &str, symbol: Option<&str>, address: u64, size: u64) -> Result<()> {
        let type_size = i32::try_from(size).map_err(|_| Error::Lowlevel(format!("data symbol too large: {name}")))?;
        let types = self.architecture.types_mut()?;
        let data_type = match type_size {
            1 | 2 | 4 | 8 => types.get_base(type_size, TypeMetatype::Unknown)?,
            _ => {
                let byte = types.get_base(1, TypeMetatype::Unknown)?;
                types.get_type_array(type_size, byte)?
            }
        };
        let scope = self.global_scope()?;
        let data_address = self.data_address(address)?;
        let entry = Database::scope_add_symbol_at(
            &mut self.architecture,
            scope,
            name,
            Some(data_type),
            &data_address,
            &Address::invalid(),
        )?;
        let sym = self.symbol_table()?.entry(entry).get_symbol();
        self.data.insert(
            address,
            DataRecord {
                sym,
                name: name.to_string(),
                loaded_name: name.to_string(),
                symbol: symbol.map(str::to_string),
                size,
            },
        );
        Ok(())
    }

    fn add_referenced_strings(&mut self, sym: SymbolId) -> Result<()> {
        if self.string_sections.is_empty() {
            return Ok(());
        }
        let constants = self.flow_facts(sym)?.map(|facts| facts.constants).unwrap_or_default();
        for constant in constants {
            if self.string_sections.iter().any(|section| section.contains(&constant)) {
                self.add_string_symbol(constant)?;
            }
        }
        Ok(())
    }

    fn add_string_symbol(&mut self, address: u64) -> Result<()> {
        let scope = self.global_scope()?;
        let data_address = self.data_address(address)?;
        if self
            .symbol_table()?
            .scope_query_container(scope, &data_address, 1, &Address::invalid())
            .is_some()
        {
            return Ok(());
        }
        let Some(text) = self.string_at(address) else {
            return Ok(());
        };
        let length = i32::try_from(text.len() + 1).map_err(|_| Error::Lowlevel("string too long".to_string()))?;
        let types = self.architecture.types_mut()?;
        let character = types.get_base(1, TypeMetatype::Int)?;
        let array = types.get_type_array(length, character)?;
        let name = format!("s_{}_{address:08x}", string_label(&text));
        Database::scope_add_symbol_at(
            &mut self.architecture,
            scope,
            &name,
            Some(array),
            &data_address,
            &Address::invalid(),
        )?;
        Ok(())
    }

    fn string_at(&self, address: u64) -> Option<String> {
        let loader = self.architecture.loader.as_ref()?;
        let data_address = self.data_address(address).ok()?;
        let mut bytes = Vec::new();
        let mut chunk = [0u8; 64];
        while bytes.len() < MAX_STRING_LENGTH {
            let chunk_address = data_address.add(bytes.len() as i64);
            loader.load_fill(&mut chunk, &chunk_address).ok()?;
            match chunk.iter().position(|byte| *byte == 0) {
                Some(end) => {
                    bytes.extend_from_slice(&chunk[..end]);
                    let text = String::from_utf8(bytes).ok()?;
                    let is_printable = text
                        .chars()
                        .all(|character| !character.is_control() || matches!(character, '\t' | '\n' | '\r'));
                    return (text.chars().count() >= MIN_STRING_LENGTH && is_printable).then_some(text);
                }
                None => bytes.extend_from_slice(&chunk),
            }
        }
        None
    }

    pub fn data_symbols(&self) -> Result<Vec<DataEntry>> {
        Ok(self
            .data
            .iter()
            .map(|(address, record)| DataEntry {
                name: record.name.clone(),
                symbol: record.symbol.clone(),
                address: *address,
                size: record.size,
            })
            .collect())
    }

    pub fn set_symbol_name(&mut self, address: u64, name: &str) -> Result<()> {
        panic_guard(|| {
            if self.function_starting_at(address)?.is_some() {
                self.set_function_name_unguarded(address, name)
            } else if self.data.contains_key(&address) {
                self.set_data_name_unguarded(address, name)
            } else {
                Err(Error::Lowlevel(format!(
                    "no function or data symbol starts at {address:#x}"
                )))
            }
        })
    }

    pub fn set_function_name(&mut self, address: u64, name: &str) -> Result<()> {
        panic_guard(|| self.set_function_name_unguarded(address, name))
    }

    pub fn set_data_name(&mut self, address: u64, name: &str) -> Result<()> {
        panic_guard(|| self.set_data_name_unguarded(address, name))
    }

    fn function_starting_at(&self, address: u64) -> Result<Option<SymbolId>> {
        let scope = self.global_scope()?;
        Ok(self
            .symbol_table()?
            .scope_query_function(scope, &self.code_address(address)?)
            .filter(|sym| self.function_address(*sym).is_ok_and(|entry| entry == address)))
    }

    fn set_function_name_unguarded(&mut self, address: u64, name: &str) -> Result<()> {
        let sym = match self.function_starting_at(address)? {
            Some(sym) => sym,
            None => self.function_at(address)?,
        };
        let loaded_name = match self.functions.get(&sym) {
            Some(record) => record.loaded_name.clone(),
            None => self.symbol_table()?.symbol(sym).get_name().to_string(),
        };
        let new_name = if name.is_empty() {
            loaded_name.clone()
        } else {
            name.to_string()
        };
        self.check_unused_name(&new_name, Some(sym), None)?;
        let scope = self.global_scope()?;
        self.architecture
            .symboltab_mut()?
            .scope_rename_symbol(scope, sym, &new_name)?;
        match self.functions.get_mut(&sym) {
            Some(record) => record.name = new_name,
            None => {
                self.functions.insert(
                    sym,
                    FunctionRecord {
                        name: new_name,
                        loaded_name,
                        symbol: None,
                        source: FunctionSource::SymbolTable,
                    },
                );
            }
        }
        Ok(())
    }

    pub fn is_code_address(&self, address: u64) -> bool {
        self.code_sections.iter().any(|section| section.contains(&address))
    }

    fn set_data_name_unguarded(&mut self, address: u64, name: &str) -> Result<()> {
        if !self.data.contains_key(&address) {
            self.add_data_label(address)?;
        }
        let (sym, loaded_name) = match self.data.get(&address) {
            Some(record) => (record.sym, record.loaded_name.clone()),
            None => return Err(Error::Lowlevel(format!("no data symbol starts at {address:#x}"))),
        };
        let new_name = if name.is_empty() { loaded_name } else { name.to_string() };
        self.check_unused_name(&new_name, None, Some(address))?;
        let scope = self.global_scope()?;
        self.architecture
            .symboltab_mut()?
            .scope_rename_symbol(scope, sym, &new_name)?;
        if let Some(record) = self.data.get_mut(&address) {
            record.name = new_name;
        }
        Ok(())
    }

    fn add_data_label(&mut self, address: u64) -> Result<()> {
        let scope = self.global_scope()?;
        let data_address = self.data_address(address)?;
        if self
            .symbol_table()?
            .scope_query_container(scope, &data_address, 1, &Address::invalid())
            .is_some()
        {
            return Err(Error::Lowlevel(format!(
                "{address:#x} is inside another symbol; name the symbol at its start"
            )));
        }
        self.add_typed_data_symbol(&format!("DAT_{address:08x}"), None, address, 1)
    }

    fn check_unused_name(&self, name: &str, function: Option<SymbolId>, data_address: Option<u64>) -> Result<()> {
        let is_function_name = self
            .functions
            .iter()
            .any(|(sym, record)| Some(*sym) != function && record.name == name);
        let is_data_name = self
            .data
            .iter()
            .any(|(address, record)| Some(*address) != data_address && record.name == name);
        if is_function_name || is_data_name {
            return Err(Error::Lowlevel(format!("the name {name} is in use")));
        }
        Ok(())
    }

    fn register(&self, name: &str) -> Option<PcodeVarnode> {
        let register = self.architecture.translator().ok()?.get_register(name).ok()?;
        Some(pcode_varnode(&register))
    }

    fn read_unsigned(&self, address: u64, size: u32) -> Option<u64> {
        if size == 0 || size > 8 {
            return None;
        }
        let loader = self.architecture.loader.as_ref()?;
        let mut bytes = vec![0u8; size as usize];
        loader.load_fill(&mut bytes, &self.code_address(address).ok()?).ok()?;
        let is_big_endian = self.architecture.translator().ok()?.is_big_endian();
        let fold = |value: u64, byte: &u8| (value << 8) | u64::from(*byte);
        Some(if is_big_endian {
            bytes.iter().fold(0, fold)
        } else {
            bytes.iter().rev().fold(0, fold)
        })
    }

    fn add_function_symbol(&mut self, symbol: &str, address: &Address, source: FunctionSource) -> Result<SymbolId> {
        match demangle::demangled_name(symbol) {
            Some(name) => self.add_named_function(&name, Some(symbol), address, source),
            None => self.add_named_function(symbol, None, address, source),
        }
    }

    fn add_named_function(
        &mut self,
        name: &str,
        symbol: Option<&str>,
        address: &Address,
        source: FunctionSource,
    ) -> Result<SymbolId> {
        let scope = self.global_scope()?;
        let sym = Database::scope_add_function(&mut self.architecture, scope, address, name)?;
        self.functions.insert(
            sym,
            FunctionRecord {
                name: name.to_string(),
                loaded_name: name.to_string(),
                symbol: symbol.map(str::to_string),
                source,
            },
        );
        Ok(sym)
    }

    pub fn language_id(&self) -> &str {
        &self.architecture.archid
    }

    pub fn description(&self) -> String {
        self.architecture.get_description()
    }

    pub fn architecture(&mut self) -> &mut Architecture {
        &mut self.architecture
    }

    fn code_address(&self, offset: u64) -> Result<Address> {
        let space = self
            .architecture
            .manager
            .get_default_code_space()
            .ok_or_else(|| Error::Lowlevel("missing default code space".to_string()))?;
        Ok(Address::new(space, offset))
    }

    fn data_address(&self, offset: u64) -> Result<Address> {
        let space = self
            .architecture
            .manager
            .get_default_data_space()
            .ok_or_else(|| Error::Lowlevel("missing default data space".to_string()))?;
        Ok(Address::new(space, offset))
    }

    fn symbol_table(&self) -> Result<&Database> {
        self.architecture
            .symboltab
            .as_deref()
            .ok_or_else(|| Error::Lowlevel("missing symbol table".to_string()))
    }

    fn global_scope(&self) -> Result<ScopeId> {
        self.symbol_table()?
            .get_global_scope()
            .ok_or_else(|| Error::Lowlevel("missing global scope".to_string()))
    }

    fn function_address(&self, sym: SymbolId) -> Result<u64> {
        let symboltab = self.symbol_table()?;
        let entry = symboltab.symbol_get_first_whole_map(sym)?;
        Ok(symboltab.entry(entry).get_addr().get_offset())
    }

    pub fn functions(&self) -> Result<Vec<FunctionEntry>> {
        let symboltab = self.symbol_table()?;
        self.architecture
            .function_symbols_address_order()?
            .into_iter()
            .map(|sym| {
                let address = self.function_address(sym)?;
                Ok(match self.functions.get(&sym) {
                    Some(record) => FunctionEntry {
                        name: record.name.clone(),
                        symbol: record.symbol.clone(),
                        address,
                        source: record.source,
                    },
                    None => FunctionEntry {
                        name: symboltab.symbol(sym).get_name().to_string(),
                        symbol: None,
                        address,
                        source: FunctionSource::SymbolTable,
                    },
                })
            })
            .collect()
    }

    pub fn disassemble(&self, address: u64, instruction_count: usize) -> Result<Vec<Instruction>> {
        panic_guard(|| self.disassemble_unguarded(address, instruction_count))
    }

    fn disassemble_unguarded(&self, address: u64, instruction_count: usize) -> Result<Vec<Instruction>> {
        let translate = self.architecture.translator()?;
        let mut current = self.code_address(address)?;
        let mut instructions = Vec::with_capacity(instruction_count);
        for _ in 0..instruction_count {
            let mut text = InstructionText {
                mnemonic: String::new(),
                operands: String::new(),
            };
            let length = translate.print_assembly(&mut text, &current)?;
            let mut bytes = vec![0u8; length as usize];
            if let Some(loader) = &self.architecture.loader {
                loader.load_fill(&mut bytes, &current)?;
            }
            instructions.push(Instruction {
                address: current.get_offset(),
                length: length as usize,
                bytes,
                mnemonic: text.mnemonic,
                operands: text.operands,
            });
            current = current.add(i64::from(length));
        }
        Ok(instructions)
    }

    pub fn pcode(&self, address: u64, instruction_count: usize) -> Result<Vec<InstructionPcode>> {
        panic_guard(|| self.pcode_unguarded(address, instruction_count))
    }

    fn pcode_unguarded(&self, address: u64, instruction_count: usize) -> Result<Vec<InstructionPcode>> {
        let translate = self.architecture.translator()?;
        let mut current = self.code_address(address)?;
        let mut instructions = Vec::with_capacity(instruction_count);
        for _ in 0..instruction_count {
            let mut collector = OperationCollector {
                manager: &self.architecture.manager,
                operations: Vec::new(),
            };
            let length = translate.one_instruction(&mut collector, &current)?;
            instructions.push(InstructionPcode {
                address: current.get_offset(),
                length: length as usize,
                operations: collector.operations,
            });
            current = current.add(i64::from(length));
        }
        Ok(instructions)
    }

    fn function_at(&mut self, address: u64) -> Result<SymbolId> {
        let addr = self.code_address(address)?;
        let scope = self.global_scope()?;
        if let Some(sym) = self.symbol_table()?.scope_query_function(scope, &addr) {
            return Ok(sym);
        }
        let mut name = String::new();
        self.architecture.name_function(&addr, &mut name);
        self.add_named_function(&name, None, &addr, FunctionSource::Requested)
    }

    pub fn decompile(&mut self, address: u64) -> Result<String> {
        panic_guard(|| self.decompile_unguarded(address))
    }

    fn decompile_unguarded(&mut self, address: u64) -> Result<String> {
        let sym = self.function_at(address)?;
        self.add_referenced_strings(sym)?;
        self.architecture.with_function(sym, |function, architecture| {
            if function.has_no_code() {
                return Err(Error::Lowlevel(format!("No code for {}", function.get_name())));
            }
            if function.is_proc_started() {
                architecture.clear_analysis(function);
            }
            let analysis = architecture.with_current_action(|action, architecture| {
                action.reset(function, architecture);
                action.perform(function, architecture)
            });
            let printed = analysis.and_then(|_| {
                architecture
                    .with_printer(Some(&mut *function), |printer, context| printer.doc_function(context))
                    .map(|((), text)| text)
            });
            architecture.clear_analysis(function);
            printed
        })
    }

    pub fn call_graph(&mut self) -> Result<Vec<CallEdge>> {
        panic_guard(|| self.call_graph_unguarded())
    }

    fn call_graph_unguarded(&mut self) -> Result<Vec<CallEdge>> {
        let mut graph = CallGraph::new();
        graph.build_all_nodes(&mut self.architecture)?;
        for sym in self.architecture.function_symbols_address_order()? {
            self.architecture.with_function(sym, |function, architecture| {
                if function.has_no_code() {
                    return Ok(());
                }
                architecture.clear_analysis(function);
                let space: Option<SpaceRef> = function.get_address().get_space().cloned();
                let highest = space.as_ref().map(|space| space.get_highest()).unwrap_or(u64::MAX);
                let start = Address::from_parts(space.clone(), 0);
                let end = Address::from_parts(space, highest);
                if function.follow_flow(&start, &end, architecture).is_ok() {
                    graph.build_edges(function, architecture)?;
                }
                architecture.clear_analysis(function);
                Ok(())
            })?;
        }
        let mut edges = Vec::new();
        for (caller, node) in graph.graph.iter() {
            for index in 0..node.num_out_edge() {
                edges.push(CallEdge {
                    caller: caller.get_offset(),
                    callee: node.get_out_node(index).get_offset(),
                    call_site: node.get_out_edge(index).get_call_site_addr().get_offset(),
                });
            }
        }
        edges.sort();
        Ok(edges)
    }
}
