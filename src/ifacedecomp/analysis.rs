use std::io::Write;
use std::time::Instant;

use crate::address::Address;
use crate::architecture::Architecture;
use crate::block::{BlockKind, FlowBlock};
use crate::blockaction::CollapseStructure;
use crate::database::{Database, Symbol, SymbolId};
use crate::dynamic::DynamicHash;
use crate::error::{Error, Result};
use crate::fspec::{FuncProto, PrototypePieces};
use crate::funcdata::Funcdata;
use crate::grammar::{parse_protopieces, parse_toseparator, parse_type, parse_varnode};
use crate::interface::{IStream, IfaceError, IfaceResult, IfaceStatus, OutStream, out_write};
use crate::marshal::{XmlDecode, XmlEncode};
use crate::opcodes::OpCode;
use crate::pcodeinject::CALLFIXUP_TYPE;
use crate::rangeutil::{ValueSetSolver, WidenerFull, WidenerNone};
use crate::space::SpaceType;
use crate::types::{Datatype, TypeMetatype};
use crate::userop::UserOpManage;
use crate::varnode::{Varnode, VarnodeId};
use crate::xml::DocumentStorage;

use super::load::{read_machaddr, set_symbol_attribute, types_mut};
use super::{
    conf_mut, decomp_data, global_scope, iterate_functions_addr_order, iterate_functions_leaf_order, symbol_table,
    with_current_action, with_current_function, with_function,
};

fn no_function() -> IfaceError {
    IfaceError::Execution("No function selected".to_string())
}

fn single_symbol(status: &mut IfaceStatus, name: &str, multiple: &str) -> IfaceResult<SymbolId> {
    let mut sym_list = Vec::new();
    decomp_data(status).read_symbol(name, &mut sym_list)?;
    if sym_list.is_empty() {
        return Err(IfaceError::Execution(format!("No symbol named: {name}")));
    }
    if sym_list.len() > 1 {
        return Err(IfaceError::Execution(format!("{multiple}{name}")));
    }
    Ok(sym_list[0])
}

fn prepare_symbol_edit(glb: &mut Architecture, fdsym: Option<SymbolId>, sym: SymbolId) -> IfaceResult<()> {
    let fdsym = fdsym.ok_or_else(no_function)?;
    let category = symbol_table(glb)?.symbol(sym).get_category();
    with_function(glb, fdsym, |fd, glb| {
        if category == Symbol::FUNCTION_PARAMETER {
            fd.get_func_proto_mut().set_input_lock(true, glb);
        }
        fd.remap_conflict_symbol(sym, glb)?;
        Ok(())
    })
}

pub fn ifc_rename(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let mut oldname = String::new();
    let mut newname = String::new();
    args.ws()
        .read_word_into(&mut oldname)
        .ws()
        .read_word_into(&mut newname)
        .ws();
    if oldname.is_empty() {
        return Err(IfaceError::Parse("Missing old symbol name".to_string()));
    }
    if newname.is_empty() {
        return Err(IfaceError::Parse("Missing new name".to_string()));
    }
    let sym = single_symbol(status, &oldname, "More than one symbol named: ")?;
    let dcp = decomp_data(status);
    let fdsym = dcp.fd;
    let glb = conf_mut(dcp, "No load image present")?;
    prepare_symbol_edit(glb, fdsym, sym)?;
    let symboltab = symbol_table(glb)?;
    let scope = symboltab.symbol(sym).get_scope();
    symboltab.scope_rename_symbol(scope, sym, &newname)?;
    set_symbol_attribute(glb, sym, Varnode::NAMELOCK | Varnode::TYPELOCK)
}

pub fn ifc_remove(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let mut name = String::new();
    args.ws().read_word_into(&mut name);
    if name.is_empty() {
        return Err(IfaceError::Parse("Missing symbol name".to_string()));
    }
    let sym = single_symbol(status, &name, "More than one symbol named: ")?;
    let glb = conf_mut(decomp_data(status), "No load image present")?;
    let symboltab = symbol_table(glb)?;
    let scope = symboltab.symbol(sym).get_scope();
    symboltab.scope_remove_symbol(scope, sym);
    Ok(())
}

pub fn ifc_retype(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let mut name = String::new();
    let mut newname = String::new();
    args.ws().read_word_into(&mut name);
    if name.is_empty() {
        return Err(IfaceError::Parse("Must specify name of symbol".to_string()));
    }
    let ct = {
        let glb = conf_mut(decomp_data(status), "No load image present")?;
        parse_type(args, &mut newname, glb)?
    };
    let sym = single_symbol(status, &name, "More than one symbol named : ")?;
    let dcp = decomp_data(status);
    let fdsym = dcp.fd;
    let glb = conf_mut(dcp, "No load image present")?;
    prepare_symbol_edit(glb, fdsym, sym)?;
    let scope = symbol_table(glb)?.symbol(sym).get_scope();
    Database::scope_retype_symbol(glb, scope, sym, ct)?;
    set_symbol_attribute(glb, sym, Varnode::TYPELOCK)?;
    if !newname.is_empty() && newname != name {
        let symboltab = symbol_table(glb)?;
        let scope = symboltab.symbol(sym).get_scope();
        symboltab.scope_rename_symbol(scope, sym, &newname)?;
        set_symbol_attribute(glb, sym, Varnode::NAMELOCK)?;
    }
    Ok(())
}

pub fn ifc_isolate(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let mut symbol_name = String::new();
    args.ws().read_word_into(&mut symbol_name);
    if symbol_name.is_empty() {
        return Err(IfaceError::Parse("Missing symbol name".to_string()));
    }
    let sym = single_symbol(status, &symbol_name, "More than one symbol named: ")?;
    let glb = conf_mut(decomp_data(status), "No load image present")?;
    let types = glb
        .types
        .as_deref()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing type factory".to_string())))?;
    let symboltab = glb
        .symboltab
        .as_deref_mut()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing symbol table".to_string())))?;
    symboltab.symbol_mut(sym).set_isolated(true, types);
    Ok(())
}

fn print_varnode_info(fd: &mut Funcdata, glb: &Architecture, vn: VarnodeId, out: &mut String) -> Result<()> {
    if fd.vn(vn).is_annotation() || !fd.is_high_on() {
        fd.vn_print_info(vn, out, glb);
    } else {
        let high = fd.vn(vn).get_high()?;
        fd.high_print_info(high, out, glb);
    }
    Ok(())
}

pub fn ifc_print_varnode(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    let vn = dcp.read_varnode(args)?;
    with_current_function(dcp, |fd, glb| {
        let mut text = String::new();
        print_varnode_info(fd, glb, vn, &mut text)?;
        out_write(&optr, &text);
        Ok(())
    })
}

pub fn ifc_print_cover(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function());
    }
    let mut name = String::new();
    args.ws().read_word_into(&mut name);
    if name.is_empty() {
        return Err(IfaceError::Parse("Missing variable name".to_string()));
    }
    with_current_function(dcp, |fd, glb| {
        let Some(high) = fd.find_high(&name, glb)? else {
            return Err(IfaceError::Execution(format!("Unable to find variable: {name}")));
        };
        let mut text = String::new();
        fd.high(high).print_cover(&mut text, fd);
        out_write(&optr, &text);
        Ok(())
    })
}

pub fn ifc_varnodehigh_cover(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    let vn = dcp.read_varnode(args)?;
    with_current_function(dcp, |fd, _glb| {
        match fd.vn(vn).get_high_option() {
            Some(high) => {
                let mut text = String::new();
                fd.high(high).print_cover(&mut text, fd);
                out_write(&optr, &text);
            }
            None => out_write(&optr, "Unmerged\n"),
        }
        Ok(())
    })
}

pub fn ifc_varnode_cover(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    let vn = dcp.read_varnode(args)?;
    with_current_function(dcp, |fd, _glb| {
        let mut text = String::new();
        let result = fd.vn_print_cover(vn, &mut text);
        out_write(&optr, &text);
        result?;
        Ok(())
    })
}

fn add_varnode_symbol(args: &mut IStream, status: &mut IfaceStatus, typed: bool) -> IfaceResult<()> {
    let fileoptr = status.fileoptr.clone();
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function());
    }
    let glb = conf_mut(dcp, "No function selected")?;
    let mut size: i32 = 0;
    let mut uq: u32 = 0;
    let mut pc = Address::invalid();
    let loc = parse_varnode(args, &mut size, &mut pc, &mut uq, glb)?;
    let mut token = String::new();
    let ct = if typed {
        parse_type(args, &mut token, glb)?
    } else {
        args.ws().read_word_into(&mut token);
        if token.is_empty() {
            return Err(IfaceError::Parse("Must specify name".to_string()));
        }
        types_mut(glb)?.get_base(size, TypeMetatype::Unknown)?
    };
    with_current_function(dcp, |fd, glb| {
        glb.clear_analysis(fd);
        let local = fd
            .get_scope_local()
            .ok_or_else(|| IfaceError::Execution("Function has no local scope".to_string()))?;
        let scope = symbol_table(glb)?
            .scope_discover_scope(local, &loc, size, &pc)
            .unwrap_or(local);
        let entry = Database::scope_add_symbol_at(glb, scope, &token, Some(ct), &loc, &pc)?;
        let sym = symbol_table(glb)?.entry(entry).get_symbol();
        if typed {
            set_symbol_attribute(glb, sym, Varnode::TYPELOCK)?;
            let types = glb
                .types
                .as_deref()
                .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing type factory".to_string())))?;
            let symboltab = glb
                .symboltab
                .as_deref_mut()
                .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing symbol table".to_string())))?;
            symboltab.symbol_mut(sym).set_isolated(true, types);
            if !token.is_empty() {
                set_symbol_attribute(glb, sym, Varnode::NAMELOCK)?;
            }
        } else {
            set_symbol_attribute(glb, sym, Varnode::NAMELOCK)?;
        }
        let delim = glb.get_scope_delimiter();
        let symboltab = symbol_table(glb)?;
        let symname = if typed {
            symboltab.symbol(sym).get_name().to_string()
        } else {
            token.clone()
        };
        let fullname = symboltab.scope_get_full_name(scope, &delim);
        out_write(
            &fileoptr,
            &format!("Successfully added {symname} to scope {fullname}\n"),
        );
        Ok(())
    })
}

pub fn ifc_name_varnode(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    add_varnode_symbol(args, status, false)
}

pub fn ifc_type_varnode(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    add_varnode_symbol(args, status, true)
}

pub fn ifc_force_format(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    let vn = dcp.read_varnode(args)?;
    with_current_function(dcp, |fd, glb| {
        if !fd.vn(vn).is_constant() {
            return Err(IfaceError::Execution("Can only force format on a constant".to_string()));
        }
        let tp = fd.vn(vn).get_type();
        let mt = types_mut(glb)?.get(tp).get_metatype();
        if mt != TypeMetatype::Int && mt != TypeMetatype::Uint && mt != TypeMetatype::Unknown {
            return Err(IfaceError::Execution(
                "Can only force format on integer type constant".to_string(),
            ));
        }
        fd.build_dynamic_symbol(vn, glb)?;
        let high = fd.vn(vn).get_high()?;
        let Some(sym) = fd.high_get_symbol(high, glb) else {
            return Err(IfaceError::Execution("Unable to create symbol".to_string()));
        };
        let mut format_string = String::new();
        args.ws().read_word_into(&mut format_string);
        let format = Datatype::encode_integer_format(&format_string)?;
        let symboltab = symbol_table(glb)?;
        let scope = symboltab.symbol(sym).get_scope();
        symboltab.scope_set_display_format(scope, sym, format);
        set_symbol_attribute(glb, sym, Varnode::TYPELOCK)?;
        out_write(&optr, "Successfully forced format display\n");
        Ok(())
    })
}

pub fn ifc_force_datatype_format(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let glb = conf_mut(decomp_data(status), "No load image present")?;
    let mut type_name = String::new();
    args.ws().read_word_into(&mut type_name);
    let types = types_mut(glb)?;
    let Some(dt) = types.find_by_name(&type_name) else {
        return Err(IfaceError::Execution(format!("Unknown data-type: {type_name}")));
    };
    let mut format_string = String::new();
    args.ws().read_word_into(&mut format_string);
    let format = Datatype::encode_integer_format(&format_string)?;
    types.set_display_format(dt, format);
    out_write(&optr, "Successfully forced data-type display\n");
    Ok(())
}

pub fn ifc_forcegoto(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function());
    }
    with_current_function(dcp, |fd, glb| {
        let mut discard: i32 = 0;
        args.ws();
        let target = read_machaddr(args, &mut discard, glb)?;
        args.ws();
        let dest = read_machaddr(args, &mut discard, glb)?;
        fd.get_override().insert_force_goto(&target, &dest);
        Ok(())
    })
}

pub fn ifc_protooverride(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function());
    }
    with_current_function(dcp, |fd, glb| {
        let mut discard: i32 = 0;
        args.ws();
        let callpoint = read_machaddr(args, &mut discard, glb)?;
        let mut found = false;
        for index in 0..fd.num_calls() {
            let op = fd.call_spec(fd.get_call_specs(index)).get_op();
            if *fd.op(op).get_addr() == callpoint {
                found = true;
                break;
            }
        }
        if !found {
            return Err(IfaceError::Execution("No call is made at this address".to_string()));
        }
        let mut pieces = PrototypePieces::default();
        parse_protopieces(&mut pieces, args, glb)?;
        let mut newproto = FuncProto::new();
        let model = pieces
            .model
            .ok_or_else(|| IfaceError::Core(Error::Lowlevel("prototype has no model".to_string())))?;
        let void_type = types_mut(glb)?.get_type_void()?;
        newproto.set_internal(model, void_type, glb);
        newproto.set_pieces(&pieces, glb)?;
        fd.get_override().insert_proto_override(&callpoint, Box::new(newproto));
        fd.clear(glb)?;
        Ok(())
    })
}

pub fn ifc_jump_override(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function());
    }
    with_current_function(dcp, |fd, glb| {
        let mut discard: i32 = 0;
        args.ws();
        let jmpaddr = read_machaddr(args, &mut discard, glb)?;
        let jt = fd.install_jump_table(&jmpaddr)?;
        let mut adtable = Vec::new();
        let naddr = Address::invalid();
        let hash: u64 = 0;
        let mut sv: u64 = 0;
        let mut token = String::new();
        args.read_word_into(&mut token);
        if token == "startval" {
            args.unset_basefield();
            args.read_u64(&mut sv);
            args.read_word_into(&mut token);
        }
        if token == "table" {
            args.ws();
            while !args.eof() {
                let addr = read_machaddr(args, &mut discard, glb)?;
                adtable.push(addr);
            }
        }
        if adtable.is_empty() {
            return Err(IfaceError::Execution("Missing jumptable address entries".to_string()));
        }
        fd.jump_table_mut(jt).set_override(&adtable, &naddr, hash, sv)?;
        out_write(&optr, "Successfully installed jumptable override\n");
        Ok(())
    })
}

pub fn ifc_flow_override(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function());
    }
    with_current_function(dcp, |fd, glb| {
        let mut discard: i32 = 0;
        args.ws();
        let addr = read_machaddr(args, &mut discard, glb)?;
        let mut token = String::new();
        args.read_word_into(&mut token);
        if token.is_empty() {
            return Err(IfaceError::Parse("Missing override type".to_string()));
        }
        fd.get_override().insert_flow_override(&addr, &token)?;
        out_write(&optr, "Successfully added flow override\n");
        Ok(())
    })
}

pub fn ifc_destination_override(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function());
    }
    with_current_function(dcp, |fd, glb| {
        let mut discard: i32 = 0;
        args.ws();
        let addr = read_machaddr(args, &mut discard, glb)?;
        let mut token = String::new();
        args.read_word_into(&mut token).ws();
        if token.is_empty() {
            return Err(IfaceError::Parse("Missing override type".to_string()));
        }
        let dest = read_machaddr(args, &mut discard, glb)?;
        fd.get_override().insert_destination_override(&addr, &dest, &token)?;
        out_write(&optr, "Successfully added destination override\n");
        Ok(())
    })
}

fn non_trivial_use(fd: &mut Funcdata, vn: VarnodeId) -> bool {
    let mut vnlist = vec![vn];
    let mut res = false;
    let mut proc = 0usize;
    while proc < vnlist.len() {
        let tmpvn = vnlist[proc];
        proc += 1;
        let descend: Vec<_> = fd.vn(tmpvn).descend().to_vec();
        for op in descend {
            let code = fd.op(op).code();
            if code == OpCode::Copy || code == OpCode::Cast || code == OpCode::Indirect || code == OpCode::Multiequal {
                let Some(outvn) = fd.op(op).get_out() else {
                    continue;
                };
                if !fd.vn(outvn).is_mark() {
                    fd.vn_mut(outvn).set_mark();
                    vnlist.push(outvn);
                }
            } else {
                res = true;
                break;
            }
        }
    }
    for vnode in vnlist {
        fd.vn_mut(vnode).clear_mark();
    }
    res
}

fn check_restore(fd: &mut Funcdata, vn: VarnodeId) -> i32 {
    let mut vnlist = vec![vn];
    let mut res = 0;
    let mut proc = 0usize;
    while proc < vnlist.len() {
        let tmpvn = vnlist[proc];
        proc += 1;
        if fd.vn(tmpvn).is_input() {
            if fd.vn(tmpvn).get_size() != fd.vn(vn).get_size() || fd.vn(tmpvn).get_addr() != fd.vn(vn).get_addr() {
                res = 1;
                break;
            }
        } else if !fd.vn(tmpvn).is_written() {
            res = 1;
            break;
        } else {
            let op = fd.vn(tmpvn).get_def().expect("written varnode has a defining op");
            let code = fd.op(op).code();
            if code == OpCode::Copy || code == OpCode::Cast || code == OpCode::Indirect {
                let invn = fd.op(op).get_in(0);
                if !fd.vn(invn).is_mark() {
                    fd.vn_mut(invn).set_mark();
                    vnlist.push(invn);
                }
            } else if code == OpCode::Multiequal {
                for slot in 0..fd.op(op).num_input() {
                    let invn = fd.op(op).get_in(slot);
                    if !fd.vn(invn).is_mark() {
                        fd.vn_mut(invn).set_mark();
                        vnlist.push(invn);
                    }
                }
            } else {
                res = 1;
                break;
            }
        }
    }
    for vnode in vnlist {
        fd.vn_mut(vnode).clear_mark();
    }
    res
}

fn find_restore(fd: &mut Funcdata, vn: VarnodeId, glb: &Architecture) -> bool {
    let addr = fd.vn(vn).get_addr().clone();
    let begin = fd.begin_loc_addr(&addr);
    let end = fd.end_loc_addr(&addr, glb);
    let candidates = fd.vbank.loc_range(&begin, &end);
    let mut count = 0;
    for candidate in candidates {
        if !fd.vn(candidate).has_no_descend() {
            continue;
        }
        if !fd.vn(candidate).is_written() {
            continue;
        }
        let op = fd.vn(candidate).get_def().expect("written varnode has a defining op");
        if fd.op(op).code() == OpCode::Indirect {
            continue;
        }
        if check_restore(fd, candidate) != 0 {
            return false;
        }
        count += 1;
    }
    count > 0
}

fn print_inputs(fd: &mut Funcdata, glb: &Architecture, args: &mut String) -> Result<()> {
    args.push_str(&format!("Function: {}\n", fd.get_name()));
    let begin = fd.begin_def_flags(Varnode::INPUT)?;
    let end = fd.end_def_flags(Varnode::INPUT)?;
    let inputs = fd.vbank.def_range(&begin, &end);
    for vn in inputs {
        fd.vn_print_raw(vn, args, glb);
        if fd.is_high_on() {
            let high = fd.vn(vn).get_high()?;
            if let Some(sym) = fd.high_get_symbol(high, glb) {
                let name = glb
                    .symboltab
                    .as_deref()
                    .map(|symboltab| symboltab.symbol(sym).get_name().to_string())
                    .unwrap_or_default();
                args.push_str(&format!("    {name}"));
            }
        }
        let findres = find_restore(fd, vn, glb);
        let nontriv = non_trivial_use(fd, vn);
        if findres && !nontriv {
            args.push_str("     restored");
        } else if nontriv {
            args.push_str("     nontriv");
        }
        args.push('\n');
    }
    Ok(())
}

pub fn ifc_print_inputs(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let fileoptr = status.fileoptr.clone();
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function());
    }
    with_current_function(dcp, |fd, glb| {
        let mut text = String::new();
        let result = print_inputs(fd, glb, &mut text);
        out_write(&fileoptr, &text);
        result?;
        Ok(())
    })
}

fn decompile_for_iteration(
    fd: &mut Funcdata,
    glb: &mut Architecture,
    optr: &OutStream,
    report: &mut dyn FnMut(&mut Funcdata, &mut Architecture, f32) -> Result<()>,
) -> IfaceResult<()> {
    glb.clear_analysis(fd);
    let start = Instant::now();
    let result = with_current_action(glb, |action, glb| {
        action.reset(fd, glb);
        action.perform(fd, glb)
    })
    .and_then(|_| report(fd, glb, start.elapsed().as_secs_f32() * 1000.0));
    if let Err(err) = result {
        if !err.is_lowlevel() {
            return Err(err.into());
        }
        out_write(optr, &format!("Skipping {}: {}\n", fd.get_name(), err.explain()));
    }
    Ok(())
}

pub fn ifc_print_inputs_all(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let fileoptr = status.fileoptr.clone();
    conf_mut(decomp_data(status), "No load image present")?;
    let mut callback = |status: &mut IfaceStatus, sym: SymbolId| -> IfaceResult<()> {
        let glb = conf_mut(decomp_data(status), "No architecture loaded")?;
        with_function(glb, sym, |fd, glb| {
            if fd.has_no_code() {
                out_write(&optr, &format!("No code for {}\n", fd.get_name()));
                return Ok(());
            }
            decompile_for_iteration(fd, glb, &optr, &mut |fd, glb, _duration| {
                let mut text = String::new();
                let result = print_inputs(fd, glb, &mut text);
                out_write(&fileoptr, &text);
                result
            })?;
            glb.clear_analysis(fd);
            Ok(())
        })
    };
    iterate_functions_addr_order(status, &mut callback)
}

fn set_prototype_lock(status: &mut IfaceStatus, val: bool) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function());
    }
    with_current_function(dcp, |fd, glb| {
        fd.get_func_proto_mut().set_input_lock(val, glb);
        fd.get_func_proto_mut().set_output_lock(val, glb);
        Ok(())
    })
}

pub fn ifc_lock_prototype(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    set_prototype_lock(status, true)
}

pub fn ifc_unlock_prototype(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    set_prototype_lock(status, false)
}

fn duplicate_hash_check(fd: &mut Funcdata, glb: &mut Architecture, args: &mut String) -> Result<()> {
    let mut dhash = DynamicHash::new();
    let begin = fd.begin_loc();
    let end = fd.end_loc();
    let varnodes = fd.vbank.loc_range(&begin, &end);
    for vn in varnodes {
        if fd.vn(vn).is_annotation() {
            continue;
        }
        if fd.vn(vn).is_constant() {
            let op = fd.vn(vn).lone_descend().expect("constant has a single descendant");
            let slot = fd.op(op).get_slot(vn);
            if slot == 0 {
                let code = fd.op(op).code();
                if code == OpCode::Load || code == OpCode::Store || code == OpCode::Return {
                    continue;
                }
            }
        } else if fd.vn(vn).get_space().map(|spc| spc.get_type()) != Some(SpaceType::Internal) {
            continue;
        } else if fd.vn(vn).is_implied() {
            continue;
        }
        dhash.unique_hash_varnode(vn, fd);
        let describe_op = |fd: &Funcdata| {
            if let Some(first) = fd.vn(vn).descend().first() {
                *first
            } else {
                fd.vn(vn).get_def().expect("varnode has a defining op")
            }
        };
        if dhash.get_hash() == 0 {
            let op = describe_op(fd);
            args.push_str("Could not get unique hash for : ");
            fd.vn_print_raw(vn, args, glb);
            args.push_str(" : ");
            fd.op_print_raw(op, args, glb);
            args.push('\n');
            return Ok(());
        }
        let total = DynamicHash::get_total_from_hash(dhash.get_hash());
        if total != 1 {
            let op = describe_op(fd);
            args.push_str(&format!(
                "Duplicate : {} out of {total} : ",
                DynamicHash::get_position_from_hash(dhash.get_hash())
            ));
            fd.vn_print_raw(vn, args, glb);
            args.push_str(" : ");
            fd.op_print_raw(op, args, glb);
            args.push('\n');
        }
    }
    Ok(())
}

fn hash_lookup_prelude(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<(Address, u64)> {
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "Image not loaded")?;
    let _ = glb;
    if dcp.fd.is_none() {
        return Err(no_function());
    }
    let glb = conf_mut(dcp, "Image not loaded")?;
    let mut size: i32 = 0;
    let addr = read_machaddr(args, &mut size, glb)?;
    let mut hash: u64 = 0;
    args.ws().hex().read_u64(&mut hash);
    Ok((addr, hash))
}

pub fn ifc_find_varnode_hash(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let (addr, hash) = hash_lookup_prelude(args, status)?;
    with_current_function(decomp_data(status), |fd, glb| {
        let mut dynamic = DynamicHash::new();
        match dynamic.find_varnode(fd, &addr, hash) {
            None => out_write(&optr, "Varnode not found\n"),
            Some(vn) => {
                let mut text = String::new();
                fd.vn_print_info(vn, &mut text, glb);
                out_write(&optr, &text);
            }
        }
        Ok(())
    })
}

pub fn ifc_find_op_hash(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let (addr, hash) = hash_lookup_prelude(args, status)?;
    with_current_function(decomp_data(status), |fd, glb| {
        let mut dynamic = DynamicHash::new();
        match dynamic.find_op(fd, &addr, hash) {
            None => out_write(&optr, "Op not found\n"),
            Some(op) => {
                let mut text = String::new();
                fd.op_print_raw(op, &mut text, glb);
                text.push('\n');
                out_write(&optr, &text);
            }
        }
        Ok(())
    })
}

pub fn ifc_duplicate_hash(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let mut callback = |status: &mut IfaceStatus, sym: SymbolId| -> IfaceResult<()> {
        let glb = conf_mut(decomp_data(status), "No architecture loaded")?;
        with_function(glb, sym, |fd, glb| {
            if fd.has_no_code() {
                out_write(&optr, &format!("No code for {}\n", fd.get_name()));
                return Ok(());
            }
            decompile_for_iteration(fd, glb, &optr, &mut |fd, glb, duration| {
                out_write(
                    &optr,
                    &format!(
                        "Decompiled {}({}) time={:.0} ms\n",
                        fd.get_name(),
                        fd.get_size(),
                        duration
                    ),
                );
                let mut text = String::new();
                let result = duplicate_hash_check(fd, glb, &mut text);
                out_write(&optr, &text);
                result
            })?;
            glb.clear_analysis(fd);
            Ok(())
        })
    };
    iterate_functions_addr_order(status, &mut callback)
}

fn call_graph_build(status: &mut IfaceStatus, quick: bool) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    dcp.allocate_call_graph();
    let mut graph = dcp.cgraph.take().expect("callgraph was just allocated");
    let glb = conf_mut(dcp, "No architecture loaded")?;
    let result = graph.build_all_nodes(glb);
    dcp.cgraph = Some(graph);
    result?;
    let mut callback = |status: &mut IfaceStatus, sym: SymbolId| -> IfaceResult<()> {
        let dcp = decomp_data(status);
        let hascode = {
            let glb = conf_mut(dcp, "No architecture loaded")?;
            with_function(glb, sym, |fd, _glb| Ok(!fd.has_no_code()))?
        };
        if !hascode {
            let glb = conf_mut(dcp, "No architecture loaded")?;
            let name = with_function(glb, sym, |fd, _glb| Ok(fd.get_name().to_string()))?;
            out_write(&optr, &format!("No code for {name}\n"));
            return Ok(());
        }
        if quick {
            dcp.fd = Some(sym);
            dcp.follow_flow(&optr, 0)?;
        } else {
            let glb = conf_mut(dcp, "No architecture loaded")?;
            with_function(glb, sym, |fd, glb| {
                decompile_for_iteration(fd, glb, &optr, &mut |fd, _glb, duration| {
                    out_write(
                        &optr,
                        &format!(
                            "Decompiled {}({}) time={:.0} ms\n",
                            fd.get_name(),
                            fd.get_size(),
                            duration
                        ),
                    );
                    Ok(())
                })
            })?;
        }
        let mut graph = dcp.cgraph.take().expect("callgraph is present");
        let glb = conf_mut(dcp, "No architecture loaded")?;
        let result = with_function(glb, sym, |fd, glb| {
            graph.build_edges(fd, glb)?;
            glb.clear_analysis(fd);
            Ok(())
        });
        dcp.cgraph = Some(graph);
        result
    };
    iterate_functions_addr_order(status, &mut callback)?;
    out_write(&optr, "Successfully built callgraph\n");
    Ok(())
}

pub fn ifc_call_graph_build(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    call_graph_build(status, false)
}

pub fn ifc_call_graph_build_quick(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    call_graph_build(status, true)
}

pub fn ifc_call_graph_dump(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    let Some(graph) = dcp.cgraph.as_ref() else {
        return Err(IfaceError::Execution("No callgraph has been built".to_string()));
    };
    let mut name = String::new();
    args.ws().read_word_into(&mut name);
    if name.is_empty() {
        return Err(IfaceError::Parse("Need file name to write callgraph to".to_string()));
    }
    let Ok(mut file) = std::fs::File::create(&name) else {
        return Err(IfaceError::Execution(format!("Unable to open file {name}")));
    };
    let mut encoder = XmlEncode::new(true);
    let result = graph.encode(&mut encoder);
    let _ = file.write_all(encoder.as_str().as_bytes());
    result?;
    out_write(&optr, &format!("Successfully saved callgraph to {name}\n"));
    Ok(())
}

pub fn ifc_call_graph_load(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    conf_mut(dcp, "Decompile action not loaded")?;
    if dcp.cgraph.is_some() {
        return Err(IfaceError::Execution("Callgraph already loaded".to_string()));
    }
    let mut name = String::new();
    args.ws().read_word_into(&mut name);
    if name.is_empty() {
        return Err(IfaceError::Execution(
            "Need name of file to read callgraph from".to_string(),
        ));
    }
    let Ok(bytes) = std::fs::read(&name) else {
        return Err(IfaceError::Execution(format!("Unable to open callgraph file {name}")));
    };
    let mut store = DocumentStorage::new();
    let doc = store.parse_document(&bytes)?;
    dcp.allocate_call_graph();
    let mut graph = dcp.cgraph.take().expect("callgraph was just allocated");
    let glb = conf_mut(dcp, "Decompile action not loaded")?;
    let result = {
        let mut decoder = XmlDecode::with_root(Some(&glb.manager), doc.get_root().clone(), 0);
        graph.decode(&mut decoder)
    };
    if let Err(err) = result {
        dcp.cgraph = Some(graph);
        return Err(err.into());
    }
    out_write(&optr, "Successfully read in callgraph\n");
    let gscope = global_scope(glb)?;
    let keys: Vec<Address> = graph.graph.keys().cloned().collect();
    for key in keys {
        let nodename = graph.graph[&key].get_name().to_string();
        let Some(sym) = symbol_table(glb)?.scope_query_function_by_name(gscope, &nodename) else {
            dcp.cgraph = Some(graph);
            return Err(IfaceError::Execution(format!(
                "Function:{nodename} in callgraph has not been loaded"
            )));
        };
        let node = graph.graph.get_mut(&key).expect("node exists");
        let result = with_function(glb, sym, |fd, _glb| {
            node.set_funcdata(fd)?;
            Ok(())
        });
        if let Err(err) = result {
            dcp.cgraph = Some(graph);
            return Err(err);
        }
    }
    dcp.cgraph = Some(graph);
    out_write(&optr, "Successfully associated functions with callgraph nodes\n");
    Ok(())
}

pub fn ifc_call_graph_list(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    if decomp_data(status).cgraph.is_none() {
        return Err(IfaceError::Execution("Callgraph not generated".to_string()));
    }
    let mut callback = |status: &mut IfaceStatus, sym: SymbolId| -> IfaceResult<()> {
        let glb = conf_mut(decomp_data(status), "No architecture loaded")?;
        let name = with_function(glb, sym, |fd, _glb| Ok(fd.get_name().to_string()))?;
        out_write(&optr, &format!("{name}\n"));
        Ok(())
    };
    iterate_functions_leaf_order(status, &mut callback)
}

pub fn read_pcode_snippet(
    args: &mut IStream,
    name: &mut String,
    outname: &mut String,
    inname: &mut Vec<String>,
    pcodestring: &mut String,
) -> IfaceResult<()> {
    args.read_word_into(outname);
    parse_toseparator(args, name);
    let mut bracket = args.read_char();
    if outname == "void" {
        outname.clear();
    }
    if bracket != Some(b'(') {
        return Err(IfaceError::Parse("Missing '('".to_string()));
    }
    while bracket != Some(b')') {
        let mut param = String::new();
        parse_toseparator(args, &mut param);
        bracket = args.read_char().or(bracket);
        if !param.is_empty() {
            inname.push(param);
        }
        if args.fail() && bracket != Some(b')') {
            break;
        }
    }
    let bracket = args.ws().read_char();
    if bracket != Some(b'{') {
        return Err(IfaceError::Parse("Missing '{'".to_string()));
    }
    args.getline_into(pcodestring, b'}');
    Ok(())
}

pub fn ifc_call_fixup(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let mut name = String::new();
    let mut outname = String::new();
    let mut pcodestring = String::new();
    let mut inname = Vec::new();
    read_pcode_snippet(args, &mut name, &mut outname, &mut inname, &mut pcodestring)?;
    let glb = conf_mut(decomp_data(status), "No load image present")?;
    let mut library = glb
        .pcodeinjectlib
        .take()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing p-code inject library".to_string())))?;
    let result = library.manual_call_fixup(&name, &pcodestring, glb);
    let id = match result {
        Ok(id) => id,
        Err(err) => {
            glb.pcodeinjectlib = Some(library);
            if !err.is_lowlevel() {
                return Err(err.into());
            }
            out_write(&optr, &format!("Error compiling pcode: {}\n", err.explain()));
            return Ok(());
        }
    };
    let mut text = String::new();
    library.get_payload(id).print_template(&mut text);
    glb.pcodeinjectlib = Some(library);
    out_write(&optr, &text);
    Ok(())
}

pub fn ifc_call_other_fixup(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let mut useropname = String::new();
    let mut outname = String::new();
    let mut pcodestring = String::new();
    let mut inname = Vec::new();
    read_pcode_snippet(args, &mut useropname, &mut outname, &mut inname, &mut pcodestring)?;
    let glb = conf_mut(decomp_data(status), "No load image present")?;
    UserOpManage::manual_call_other_fixup(&useropname, &outname, &inname, &pcodestring, glb)?;
    out_write(&optr, "Successfully registered callotherfixup\n");
    Ok(())
}

pub fn ifc_fixup_apply(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let glb = conf_mut(decomp_data(status), "No load image present")?;
    let mut fixup_name = String::new();
    let mut func_name = String::new();
    args.ws();
    if args.eof() {
        return Err(IfaceError::Parse("Missing fixup name".to_string()));
    }
    args.read_word_into(&mut fixup_name).ws();
    if args.eof() {
        return Err(IfaceError::Parse("Missing function name".to_string()));
    }
    args.read_word_into(&mut func_name);
    let injectid = glb
        .pcodeinjectlib
        .as_deref()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing p-code inject library".to_string())))?
        .get_payload_id(CALLFIXUP_TYPE, &fixup_name);
    if injectid < 0 {
        return Err(IfaceError::Execution(format!("Unknown fixup: {fixup_name}")));
    }
    let delim = glb.get_scope_delimiter();
    let mut basename = String::new();
    let symboltab = symbol_table(glb)?;
    let Some(funcscope) = symboltab.resolve_scope_from_symbol_name(&func_name, &delim, &mut basename, None) else {
        return Err(IfaceError::Execution(format!("Bad namespace: {func_name}")));
    };
    let Some(sym) = symboltab.scope_query_function_by_name(funcscope, &basename) else {
        return Err(IfaceError::Execution(format!("Unknown function name: {func_name}")));
    };
    with_function(glb, sym, |fd, _glb| {
        fd.get_func_proto_mut().set_inject_id(injectid);
        Ok(())
    })?;
    out_write(&optr, "Successfully applied callfixup\n");
    Ok(())
}

pub fn ifc_structure_blocks(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let glb = conf_mut(decomp_data(status), "No load image present")?;
    let mut infile = String::new();
    let mut outfile = String::new();
    args.read_word_into(&mut infile);
    args.read_word_into(&mut outfile);
    if infile.is_empty() {
        return Err(IfaceError::Parse("Missing input file".to_string()));
    }
    if outfile.is_empty() {
        return Err(IfaceError::Parse("Missing output file".to_string()));
    }
    let Ok(bytes) = std::fs::read(&infile) else {
        return Err(IfaceError::Execution(format!("Unable to open file: {infile}")));
    };
    let mut store = DocumentStorage::new();
    let doc = store.parse_document(&bytes)?;
    let codespace = glb
        .manager
        .get_default_code_space()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing default code space".to_string())))?;
    let mut scratch = Funcdata::new(
        "structure",
        "structure",
        None,
        &Address::new(codespace, 0),
        None,
        0,
        glb,
    )?;
    let result = (|| -> IfaceResult<()> {
        let ingraph = scratch.blocks.alloc(FlowBlock::new_graph_kind(BlockKind::Graph));
        {
            let mut decoder = XmlDecode::with_root(Some(&glb.manager), doc.get_root().clone(), 0);
            scratch.block_graph_decode(ingraph, &mut decoder)?;
        }
        let resultgraph = scratch.blocks.alloc(FlowBlock::new_graph_kind(BlockKind::Graph));
        let mut rootlist = Vec::new();
        scratch.block_build_copy(resultgraph, ingraph);
        scratch.block_structure_loops(resultgraph, &mut rootlist)?;
        scratch.block_calc_forward_dominator(resultgraph, &rootlist)?;
        let mut collapse = CollapseStructure::new(resultgraph);
        collapse.collapse_all(&mut scratch, glb)?;
        let Ok(mut file) = std::fs::File::create(&outfile) else {
            return Err(IfaceError::Execution(format!("Unable to open output file: {outfile}")));
        };
        let mut encoder = XmlEncode::new(true);
        let encoded = scratch.block_encode(resultgraph, &mut encoder);
        let _ = file.write_all(encoder.as_str().as_bytes());
        encoded?;
        Ok(())
    })();
    scratch.destroy(glb);
    match result {
        Err(IfaceError::Core(err)) if err.is_lowlevel() => {
            out_write(&optr, &format!("{}\n", err.explain()));
            Ok(())
        }
        other => other,
    }
}

pub fn ifc_analyze_range(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    conf_mut(dcp, "Image not loaded")?;
    if dcp.fd.is_none() {
        return Err(no_function());
    }
    let mut token = String::new();
    args.ws().read_word_into(&mut token);
    let use_full_widener = if token == "full" {
        true
    } else if token == "partial" {
        false
    } else {
        return Err(IfaceError::Parse(
            "Must specify \"full\" or \"partial\" widening".to_string(),
        ));
    };
    let vn = dcp.read_varnode(args)?;
    with_current_function(dcp, |fd, glb| {
        let sinks = vec![vn];
        let mut reads = Vec::new();
        for op in fd.vn(vn).descend().to_vec() {
            let code = fd.op(op).code();
            if code == OpCode::Load || code == OpCode::Store {
                reads.push(op);
            }
        }
        let stack_space = glb
            .manager
            .get_stack_space()
            .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing stack space".to_string())))?;
        let stack_reg = fd.find_spacebase_input(&stack_space)?;
        let mut vs_solver = ValueSetSolver::default();
        vs_solver.establish_value_sets(&sinks, &reads, stack_reg, false, fd);
        if use_full_widener {
            let mut widener = WidenerFull::new();
            vs_solver.solve(10000, &mut widener, fd);
        } else {
            let mut widener = WidenerNone::new();
            vs_solver.solve(10000, &mut widener, fd);
        }
        let mut text = String::new();
        for value_set in vs_solver.value_sets() {
            value_set.print_raw(&mut text, fd, glb);
            text.push('\n');
        }
        for (_seq, read) in vs_solver.value_set_reads() {
            read.print_raw(&mut text, fd);
            text.push('\n');
        }
        out_write(&optr, &text);
        Ok(())
    })
}
