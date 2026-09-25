use std::fmt;
use std::path::Path;
use std::sync::Arc;

use crate::address::Address;
use crate::architecture::{Architecture, ArchitectureBuilder};
use crate::callgraph::CallGraph;
use crate::database::{Database, ScopeId, SymbolId};
use crate::error::{Error, Result};
use crate::object_arch::{ObjectArchitecture, is_object_file};
use crate::opcodes::{OpCode, get_opname};
use crate::pcoderaw::VarnodeData;
use crate::raw_arch::RawBinaryArchitecture;
use crate::space::SpaceRef;
use crate::translate::{AddrSpaceManager, AssemblyEmit, PcodeEmit};
use crate::xml::DocumentStorage;

pub struct Program {
    architecture: Box<Architecture>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FunctionEntry {
    pub name: String,
    pub address: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Instruction {
    pub address: u64,
    pub length: usize,
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
        let bytes = std::fs::read(path)
            .map_err(|error| Error::Lowlevel(format!("failed to read '{}': {error}", path.display())))?;
        Program::from_image(&path.to_string_lossy(), bytes, language)
    }

    pub fn from_image(name: &str, bytes: Vec<u8>, language: Option<&str>) -> Result<Program> {
        if !is_object_file(&bytes) {
            return Err(Error::Lowlevel(format!("unrecognized executable format: {name}")));
        }
        let builder = ObjectArchitecture::with_bytes(name, language.unwrap_or("default"), bytes);
        Program::initialize(Arc::new(builder), true)
    }

    pub fn from_raw_bytes(bytes: Vec<u8>, language: &str, base_address: u64) -> Result<Program> {
        let builder = RawBinaryArchitecture::with_bytes("raw", language, bytes, base_address);
        Program::initialize(Arc::new(builder), false)
    }

    fn initialize(builder: Arc<dyn ArchitectureBuilder>, symbols_present: bool) -> Result<Program> {
        panic_guard(|| Program::initialize_unguarded(builder, symbols_present))
    }

    fn initialize_unguarded(builder: Arc<dyn ArchitectureBuilder>, symbols_present: bool) -> Result<Program> {
        let mut architecture = Box::new(Architecture::new());
        architecture.builder = Some(builder);
        let mut store = DocumentStorage::new();
        architecture.init(&mut store)?;
        if symbols_present {
            architecture.read_loader_symbols()?;
        }
        Ok(Program { architecture })
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
                Ok(FunctionEntry {
                    name: symboltab.symbol(sym).get_name().to_string(),
                    address: self.function_address(sym)?,
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
            instructions.push(Instruction {
                address: current.get_offset(),
                length: length as usize,
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
        Database::scope_add_function(&mut self.architecture, scope, &addr, &name)
    }

    pub fn decompile(&mut self, address: u64) -> Result<String> {
        panic_guard(|| self.decompile_unguarded(address))
    }

    fn decompile_unguarded(&mut self, address: u64) -> Result<String> {
        let sym = self.function_at(address)?;
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
