mod analysis;
mod console;
mod load;
mod printing;

use std::any::Any;

use crate::address::{Address, SeqNum};
use crate::architecture::Architecture;
use crate::callgraph::CallGraph;
use crate::database::{Database, ScopeId, SymbolId};
use crate::error::{Error, Result};
use crate::funcdata::Funcdata;
use crate::grammar::parse_varnode;
use crate::interface::{
    FunctionCommand, IStream, IfaceError, IfaceResult, IfaceStatus, OutStream, base_command, ifc_closefile, ifc_echo,
    ifc_history, ifc_openfile, ifc_openfile_append, ifc_quit, out_write,
};
use crate::printlanguage::{PrintContext, PrintLanguage};
use crate::sleigh_arch::LoaderSlot;
use crate::space::SpaceType;
use crate::testfunction::FunctionTestCollection;
use crate::translate::AssemblyEmit;
use crate::varnode::VarnodeId;

pub use analysis::*;
pub use console::*;
pub use load::*;
pub use printing::*;

pub const DECOMPILE_MODULE: &str = "decompile";

pub struct IfaceDecompData {
    pub fd: Option<SymbolId>,
    pub conf: Option<Box<Architecture>>,
    pub cgraph: Option<CallGraph>,
    pub test_collection: Option<Box<FunctionTestCollection>>,
    pub loader_slot: Option<LoaderSlot>,
}

impl Default for IfaceDecompData {
    fn default() -> IfaceDecompData {
        IfaceDecompData::new()
    }
}

impl IfaceDecompData {
    pub fn new() -> IfaceDecompData {
        IfaceDecompData {
            fd: None,
            conf: None,
            cgraph: None,
            test_collection: None,
            loader_slot: None,
        }
    }

    pub fn allocate_call_graph(&mut self) {
        self.cgraph = Some(CallGraph::new());
    }

    pub fn abort_function(&mut self, stream: &OutStream) {
        let Some(sym) = self.fd else {
            return;
        };
        if let Some(glb) = self.conf.as_deref_mut() {
            let _ = with_function(glb, sym, |fd, glb| {
                let message = format!("Unable to proceed with function: {}\n", fd.get_name());
                out_write(stream, &message);
                glb.clear_analysis(fd);
                Ok(())
            });
        }
        self.fd = None;
    }

    pub fn clear_architecture(&mut self) {
        self.conf = None;
        self.loader_slot = None;
        self.fd = None;
    }

    pub fn follow_flow(&mut self, stream: &OutStream, size: i32) -> IfaceResult<()> {
        let sym = self
            .fd
            .ok_or_else(|| IfaceError::Execution("No function selected".to_string()))?;
        let glb = conf_mut(self, "No image loaded")?;
        with_function(glb, sym, |fd, glb| {
            let result = if size == 0 {
                let space = fd
                    .get_address()
                    .get_space()
                    .cloned()
                    .ok_or_else(|| Error::Lowlevel("function address is invalid".to_string()))?;
                let baddr = Address::new(space.clone(), 0);
                let eaddr = Address::new(space.clone(), space.get_highest());
                fd.follow_flow(&baddr, &eaddr, glb)
            } else {
                let baddr = fd.get_address().clone();
                let eaddr = fd.get_address().add(size as i64);
                fd.follow_flow(&baddr, &eaddr, glb)
            };
            match result {
                Ok(()) => {
                    let mut text = format!("Function {}: ", fd.get_name());
                    fd.get_address().print_raw(&mut text);
                    text.push('\n');
                    out_write(stream, &text);
                    Ok(())
                }
                Err(err) if err.is_recov() => {
                    let text = format!("Function {}: {}\n", fd.get_name(), err.explain());
                    out_write(stream, &text);
                    Ok(())
                }
                Err(err) => Err(err.into()),
            }
        })
    }

    pub fn read_varnode(&mut self, args: &mut IStream) -> IfaceResult<VarnodeId> {
        let sym = self
            .fd
            .ok_or_else(|| IfaceError::Execution("No function selected".to_string()))?;
        let glb = conf_mut(self, "No function selected")?;
        let mut defsize: i32 = 0;
        let mut pc = Address::invalid();
        let mut uq: u32 = 0;
        let loc = parse_varnode(args, &mut defsize, &mut pc, &mut uq, glb)?;
        with_function(glb, sym, |fd, glb| {
            let mut vn: Option<VarnodeId> = None;
            let is_constant = loc
                .get_space()
                .map(|spc| spc.get_type() == SpaceType::Constant)
                .unwrap_or(false);
            if is_constant {
                if pc.is_invalid() || uq == u32::MAX {
                    return Err(IfaceError::Parse("Missing p-code sequence number".to_string()));
                }
                let seq = SeqNum::new(pc.clone(), uq);
                if let Some(op) = fd.find_op(&seq) {
                    for slot in 0..fd.op(op).num_input() {
                        let tmpvn = fd.op(op).get_in(slot);
                        if *fd.vn(tmpvn).get_addr() == loc {
                            vn = Some(tmpvn);
                            break;
                        }
                    }
                }
            } else if pc.is_invalid() && uq == u32::MAX {
                vn = fd.find_varnode_input(defsize, &loc);
            } else if !pc.is_invalid() && uq != u32::MAX {
                vn = fd.find_varnode_written(defsize, &loc, &pc, uq);
            } else {
                let begin = fd.begin_loc_size(defsize, &loc);
                let end = fd.end_loc_size(defsize, &loc);
                let candidates = fd.vbank.loc_range(&begin, &end);
                for candidate in candidates {
                    vn = Some(candidate);
                    if fd.vn(candidate).is_free() {
                        continue;
                    }
                    if fd.vn(candidate).is_written() {
                        let def = fd.vn(candidate).get_def().expect("written varnode has a defining op");
                        if !pc.is_invalid() && *fd.op(def).get_addr() == pc {
                            break;
                        }
                        if uq != u32::MAX && fd.op(def).get_time() == uq {
                            break;
                        }
                    }
                }
            }
            let _ = glb;
            vn.ok_or_else(|| IfaceError::Execution("Requested varnode does not exist".to_string()))
        })
    }

    pub fn read_symbol(&mut self, name: &str, res: &mut Vec<SymbolId>) -> IfaceResult<()> {
        let fdsym = self.fd;
        let glb = conf_mut(self, "No load image present")?;
        let scope = match fdsym {
            None => global_scope(glb)?,
            Some(sym) => with_function(glb, sym, |fd, _glb| {
                fd.get_scope_local()
                    .ok_or_else(|| IfaceError::Execution("Function has no local scope".to_string()))
            })?,
        };
        let delim = glb.get_scope_delimiter();
        let mut basename = String::new();
        let symboltab = symbol_table(glb)?;
        let Some(scope) = symboltab.resolve_scope_from_symbol_name(name, &delim, &mut basename, Some(scope)) else {
            return Err(IfaceError::Parse(format!("Bad namespace for symbol: {name}")));
        };
        symboltab.scope_query_by_name(scope, &basename, res);
        Ok(())
    }
}

pub fn new_decomp_data() -> Box<dyn Any> {
    Box::new(IfaceDecompData::new())
}

pub fn decomp_command(run: crate::interface::CommandFunction) -> Box<dyn crate::interface::IfaceCommand> {
    Box::new(FunctionCommand::new(DECOMPILE_MODULE, run, Some(new_decomp_data)))
}

pub fn decomp_data(status: &mut IfaceStatus) -> &mut IfaceDecompData {
    status
        .get_data_mut(DECOMPILE_MODULE)
        .and_then(|data| data.downcast_mut::<IfaceDecompData>())
        .expect("decompiler console data is registered")
}

pub fn conf_mut<'a>(dcp: &'a mut IfaceDecompData, message: &str) -> IfaceResult<&'a mut Architecture> {
    dcp.conf
        .as_deref_mut()
        .ok_or_else(|| IfaceError::Execution(message.to_string()))
}

pub fn symbol_table(glb: &mut Architecture) -> IfaceResult<&mut Database> {
    glb.symboltab
        .as_deref_mut()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing symbol table".to_string())))
}

pub fn global_scope(glb: &Architecture) -> IfaceResult<ScopeId> {
    glb.symboltab
        .as_ref()
        .and_then(|symboltab| symboltab.get_global_scope())
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing global scope".to_string())))
}

pub fn take_function(glb: &mut Architecture, sym: SymbolId) -> IfaceResult<Box<Funcdata>> {
    if Database::symbol_get_function(glb, sym)?.is_none() {
        return Err(IfaceError::Execution("Symbol is not a function".to_string()));
    }
    symbol_table(glb)?
        .symbol_take_function(sym)
        .ok_or_else(|| IfaceError::Execution("Function is already in use".to_string()))
}

pub fn restore_function(glb: &mut Architecture, sym: SymbolId, function: Box<Funcdata>) {
    if let Some(symboltab) = glb.symboltab.as_deref_mut() {
        symboltab.symbol_restore_function(sym, function);
    }
}

pub fn with_function<R>(
    glb: &mut Architecture,
    sym: SymbolId,
    body: impl FnOnce(&mut Funcdata, &mut Architecture) -> IfaceResult<R>,
) -> IfaceResult<R> {
    let mut function = take_function(glb, sym)?;
    let result = body(&mut function, glb);
    restore_function(glb, sym, function);
    result
}

pub fn with_current_function<R>(
    dcp: &mut IfaceDecompData,
    body: impl FnOnce(&mut Funcdata, &mut Architecture) -> IfaceResult<R>,
) -> IfaceResult<R> {
    let sym = dcp
        .fd
        .ok_or_else(|| IfaceError::Execution("No function selected".to_string()))?;
    let glb = conf_mut(dcp, "No function selected")?;
    with_function(glb, sym, body)
}

pub fn function_name(glb: &mut Architecture, sym: SymbolId) -> IfaceResult<String> {
    with_function(glb, sym, |fd, _glb| Ok(fd.get_name().to_string()))
}

pub fn with_current_action<R>(
    glb: &mut Architecture,
    body: impl FnOnce(&mut dyn crate::action::Action, &mut Architecture) -> Result<R>,
) -> Result<R> {
    glb.with_current_action(body)
}

pub fn with_printer<R>(
    glb: &mut Architecture,
    data: Option<&mut Funcdata>,
    body: impl FnOnce(&mut dyn PrintLanguage, &mut PrintContext<'_>) -> Result<R>,
) -> Result<(R, String)> {
    glb.with_printer(data, body)
}

pub struct IfaceAssemblyEmit {
    mnemonicpad: i32,
    pub out: String,
}

impl IfaceAssemblyEmit {
    pub fn new(mp: i32) -> IfaceAssemblyEmit {
        IfaceAssemblyEmit {
            mnemonicpad: mp,
            out: String::new(),
        }
    }
}

impl AssemblyEmit for IfaceAssemblyEmit {
    fn dump(&mut self, addr: &Address, mnem: &str, body: &str) {
        addr.print_raw(&mut self.out);
        self.out.push_str(": ");
        self.out.push_str(mnem);
        let mut index = mnem.len() as i32;
        while index < self.mnemonicpad {
            self.out.push(' ');
            index += 1;
        }
        self.out.push_str(body);
        self.out.push('\n');
    }
}

pub fn execute(status: &mut IfaceStatus) {
    let result = status.run_command();
    let err = match result {
        Ok(_) => return,
        Err(err) => err,
    };
    let optr = status.optr.clone();
    match &err {
        IfaceError::Parse(message) => out_write(&optr, &format!("Command parsing error: {message}\n")),
        IfaceError::Execution(message) => out_write(&optr, &format!("Execution error: {message}\n")),
        IfaceError::Generic(message) => out_write(&optr, &format!("ERROR: {message}\n")),
        IfaceError::Core(core) => match core {
            Error::Parse(message) => out_write(&optr, &format!("Parse ERROR: {message}\n")),
            Error::Recov(_) | Error::DuplicateFunction { .. } => {
                out_write(&optr, &format!("Function ERROR: {}\n", core.explain()))
            }
            Error::Decoder(message) => {
                out_write(&optr, &format!("Decoding ERROR: {message}\n"));
                decomp_data(status).abort_function(&optr);
            }
            _ => {
                out_write(&optr, &format!("Low-level ERROR: {}\n", core.explain()));
                decomp_data(status).abort_function(&optr);
            }
        },
    }
    status.evaluate_error();
}

pub fn mainloop(status: &mut IfaceStatus) {
    loop {
        while !status.is_stream_finished() {
            status.write_prompt();
            let optr = status.optr.clone();
            status.flush_stream(&optr);
            execute(status);
        }
        if status.done {
            break;
        }
        if status.get_num_input_stream_size() == 0 {
            break;
        }
        status.pop_script();
    }
}

pub fn iterate_functions_addr_order(
    status: &mut IfaceStatus,
    callback: &mut dyn FnMut(&mut IfaceStatus, SymbolId) -> IfaceResult<()>,
) -> IfaceResult<()> {
    let functions = conf_mut(decomp_data(status), "No architecture loaded")?.function_symbols_address_order()?;
    for sym in functions {
        callback(status, sym)?;
    }
    Ok(())
}

pub fn iterate_functions_leaf_order(
    status: &mut IfaceStatus,
    callback: &mut dyn FnMut(&mut IfaceStatus, SymbolId) -> IfaceResult<()>,
) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    if dcp.conf.is_none() {
        return Err(IfaceError::Execution("No architecture loaded".to_string()));
    }
    if dcp.cgraph.is_none() {
        return Err(IfaceError::Execution("No callgraph present".to_string()));
    }
    let mut node = dcp.cgraph.as_mut().and_then(|graph| graph.init_leaf_walk());
    while let Some(addr) = node {
        let dcp = decomp_data(status);
        let graph = dcp.cgraph.as_mut().expect("callgraph is present");
        let entry = graph.find_node(&addr).expect("leaf walk node exists");
        let has_name = !entry.get_name().is_empty();
        let target = entry.get_funcdata();
        if has_name && let Some(sym) = target {
            callback(status, sym)?;
        }
        let dcp = decomp_data(status);
        let graph = dcp.cgraph.as_mut().expect("callgraph is present");
        node = graph.next_leaf(&addr);
    }
    Ok(())
}

pub fn register_commands(status: &mut IfaceStatus) {
    status.register_com(decomp_command(ifc_comment), &["//"]);
    status.register_com(decomp_command(ifc_comment), &["#"]);
    status.register_com(decomp_command(ifc_comment), &["%"]);
    status.register_com(base_command(ifc_quit), &["quit"]);
    status.register_com(base_command(ifc_history), &["history"]);
    status.register_com(base_command(ifc_openfile), &["openfile", "write"]);
    status.register_com(base_command(ifc_openfile_append), &["openfile", "append"]);
    status.register_com(base_command(ifc_closefile), &["closefile"]);
    status.register_com(base_command(ifc_echo), &["echo"]);

    status.register_com(decomp_command(ifc_source), &["source"]);
    status.register_com(decomp_command(ifc_option), &["option"]);
    status.register_com(decomp_command(ifc_parse_file), &["parse", "file"]);
    status.register_com(decomp_command(ifc_parse_line), &["parse", "line"]);
    status.register_com(decomp_command(ifc_adjust_vma), &["adjust", "vma"]);
    status.register_com(decomp_command(ifc_funcload), &["load", "function"]);
    status.register_com(decomp_command(ifc_addrrange_load), &["load", "addr"]);
    status.register_com(decomp_command(ifc_read_symbols), &["read", "symbols"]);
    status.register_com(decomp_command(ifc_cleararch), &["clear", "architecture"]);
    status.register_com(decomp_command(ifc_mapaddress), &["map", "address"]);
    status.register_com(decomp_command(ifc_maphash), &["map", "hash"]);
    status.register_com(decomp_command(ifc_map_param), &["map", "param"]);
    status.register_com(decomp_command(ifc_map_return), &["map", "return"]);
    status.register_com(decomp_command(ifc_mapfunction), &["map", "function"]);
    status.register_com(decomp_command(ifc_mapexternalref), &["map", "externalref"]);
    status.register_com(decomp_command(ifc_maplabel), &["map", "label"]);
    status.register_com(decomp_command(ifc_mapconvert), &["map", "convert"]);
    status.register_com(decomp_command(ifc_mapunionfacet), &["map", "unionfacet"]);
    status.register_com(decomp_command(ifc_printdisasm), &["disassemble"]);
    status.register_com(decomp_command(ifc_decompile), &["decompile"]);
    status.register_com(decomp_command(ifc_dump), &["dump"]);
    status.register_com(decomp_command(ifc_dumpbinary), &["binary"]);
    status.register_com(decomp_command(ifc_forcegoto), &["force", "goto"]);
    status.register_com(decomp_command(ifc_force_format), &["force", "varnode"]);
    status.register_com(decomp_command(ifc_force_datatype_format), &["force", "datatype"]);
    status.register_com(decomp_command(ifc_protooverride), &["override", "prototype"]);
    status.register_com(decomp_command(ifc_jump_override), &["override", "jumptable"]);
    status.register_com(decomp_command(ifc_flow_override), &["override", "flow"]);
    status.register_com(decomp_command(ifc_destination_override), &["override", "destination"]);
    status.register_com(decomp_command(ifc_deadcodedelay), &["deadcode", "delay"]);
    status.register_com(decomp_command(ifc_global_add), &["global", "add"]);
    status.register_com(decomp_command(ifc_global_remove), &["global", "remove"]);
    status.register_com(decomp_command(ifc_globalify), &["global", "spaces"]);
    status.register_com(decomp_command(ifc_global_registers), &["global", "registers"]);
    status.register_com(decomp_command(ifc_graph_dataflow), &["graph", "dataflow"]);
    status.register_com(decomp_command(ifc_graph_controlflow), &["graph", "controlflow"]);
    status.register_com(decomp_command(ifc_graph_dom), &["graph", "dom"]);
    status.register_com(decomp_command(ifc_print_language), &["print", "language"]);
    status.register_com(decomp_command(ifc_print_cstruct), &["print", "C"]);
    status.register_com(decomp_command(ifc_print_cflat), &["print", "C", "flat"]);
    status.register_com(decomp_command(ifc_print_cglobals), &["print", "C", "globals"]);
    status.register_com(decomp_command(ifc_print_ctypes), &["print", "C", "types"]);
    status.register_com(decomp_command(ifc_print_cxml), &["print", "C", "xml"]);
    status.register_com(decomp_command(ifc_print_param_measures), &["print", "parammeasures"]);
    status.register_com(decomp_command(ifc_produce_c), &["produce", "C"]);
    status.register_com(decomp_command(ifc_produce_prototypes), &["produce", "prototypes"]);
    status.register_com(decomp_command(ifc_print_raw), &["print", "raw"]);
    status.register_com(decomp_command(ifc_print_inputs), &["print", "inputs"]);
    status.register_com(decomp_command(ifc_print_inputs_all), &["print", "inputs", "all"]);
    status.register_com(decomp_command(ifc_listaction), &["list", "action"]);
    status.register_com(decomp_command(ifc_list_override), &["list", "override"]);
    status.register_com(decomp_command(ifc_listprototypes), &["list", "prototypes"]);
    status.register_com(decomp_command(ifc_setcontextrange), &["set", "context"]);
    status.register_com(decomp_command(ifc_settrackedrange), &["set", "track"]);
    status.register_com(decomp_command(ifc_breakstart), &["break", "start"]);
    status.register_com(decomp_command(ifc_breakaction), &["break", "action"]);
    status.register_com(decomp_command(ifc_print_spaces), &["print", "spaces"]);
    status.register_com(decomp_command(ifc_print_high), &["print", "high"]);
    status.register_com(decomp_command(ifc_print_tree), &["print", "tree", "varnode"]);
    status.register_com(decomp_command(ifc_print_blocktree), &["print", "tree", "block"]);
    status.register_com(decomp_command(ifc_print_localrange), &["print", "localrange"]);
    status.register_com(decomp_command(ifc_print_map), &["print", "map"]);
    status.register_com(decomp_command(ifc_print_varnode), &["print", "varnode"]);
    status.register_com(decomp_command(ifc_print_cover), &["print", "cover", "high"]);
    status.register_com(decomp_command(ifc_varnode_cover), &["print", "cover", "varnode"]);
    status.register_com(
        decomp_command(ifc_varnodehigh_cover),
        &["print", "cover", "varnodehigh"],
    );
    status.register_com(decomp_command(ifc_print_extrapop), &["print", "extrapop"]);
    status.register_com(decomp_command(ifc_print_actionstats), &["print", "actionstats"]);
    status.register_com(decomp_command(ifc_reset_actionstats), &["reset", "actionstats"]);
    status.register_com(decomp_command(ifc_count_pcode), &["count", "pcode"]);
    status.register_com(decomp_command(ifc_type_varnode), &["type", "varnode"]);
    status.register_com(decomp_command(ifc_name_varnode), &["name", "varnode"]);
    status.register_com(decomp_command(ifc_rename), &["rename"]);
    status.register_com(decomp_command(ifc_retype), &["retype"]);
    status.register_com(decomp_command(ifc_remove), &["remove"]);
    status.register_com(decomp_command(ifc_isolate), &["isolate"]);
    status.register_com(decomp_command(ifc_lock_prototype), &["prototype", "lock"]);
    status.register_com(decomp_command(ifc_unlock_prototype), &["prototype", "unlock"]);
    status.register_com(decomp_command(ifc_comment_instr), &["comment", "instruction"]);
    status.register_com(decomp_command(ifc_find_varnode_hash), &["find", "varnode", "hash"]);
    status.register_com(decomp_command(ifc_find_op_hash), &["find", "op", "hash"]);
    status.register_com(decomp_command(ifc_duplicate_hash), &["duplicate", "hash"]);
    status.register_com(decomp_command(ifc_call_graph_build), &["callgraph", "build"]);
    status.register_com(
        decomp_command(ifc_call_graph_build_quick),
        &["callgraph", "build", "quick"],
    );
    status.register_com(decomp_command(ifc_call_graph_dump), &["callgraph", "dump"]);
    status.register_com(decomp_command(ifc_call_graph_load), &["callgraph", "load"]);
    status.register_com(decomp_command(ifc_call_graph_list), &["callgraph", "list"]);
    status.register_com(decomp_command(ifc_call_fixup), &["fixup", "call"]);
    status.register_com(decomp_command(ifc_call_other_fixup), &["fixup", "callother"]);
    status.register_com(decomp_command(ifc_fixup_apply), &["fixup", "apply"]);
    status.register_com(decomp_command(ifc_volatile), &["volatile"]);
    status.register_com(decomp_command(ifc_readonly), &["readonly"]);
    status.register_com(decomp_command(ifc_pointer_setting), &["pointer", "setting"]);
    status.register_com(decomp_command(ifc_prefer_split), &["prefersplit"]);
    status.register_com(decomp_command(ifc_structure_blocks), &["structure", "blocks"]);
    status.register_com(decomp_command(ifc_analyze_range), &["analyze", "range"]);
    status.register_com(decomp_command(ifc_load_test_file), &["load", "test", "file"]);
    status.register_com(decomp_command(ifc_list_test_commands), &["list", "test", "commands"]);
    status.register_com(
        decomp_command(ifc_execute_test_command),
        &["execute", "test", "command"],
    );
    status.register_com(decomp_command(ifc_continue), &["continue"]);
}

pub fn register_all_commands(status: &mut IfaceStatus) {
    register_commands(status);
}

pub fn ifc_comment(_args: &mut IStream, _status: &mut IfaceStatus) -> IfaceResult<()> {
    Ok(())
}
