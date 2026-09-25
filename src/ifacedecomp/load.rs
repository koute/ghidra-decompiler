use std::io::BufReader;

use crate::address::{Address, Range};
use crate::architecture::Architecture;
use crate::database::{Database, Symbol, SymbolId};
use crate::error::{Error, Result};
use crate::fspec::ParameterPieces;
use crate::globalcontext::TrackedContext;
use crate::grammar::{parse_c, parse_machaddr, parse_type};
use crate::interface::{IStream, IfaceError, IfaceResult, IfaceStatus, out_write};
use crate::marshal::ElementId;
use crate::options::OptionDatabase;
use crate::prefersplit::PreferSplitRecord;
use crate::types::{TypeFactory, TypeMetatype};
use crate::varnode::Varnode;

use super::{conf_mut, decomp_data, global_scope, symbol_table, with_current_function, with_function};

pub fn types_mut(glb: &mut Architecture) -> IfaceResult<&mut TypeFactory> {
    glb.types
        .as_deref_mut()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing type factory".to_string())))
}

pub fn set_symbol_attribute(glb: &mut Architecture, sym: SymbolId, attr: u32) -> IfaceResult<()> {
    let types = glb
        .types
        .as_deref()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing type factory".to_string())))?;
    let symboltab = glb
        .symboltab
        .as_deref_mut()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing symbol table".to_string())))?;
    let scope = symboltab.symbol(sym).get_scope();
    symboltab.scope_set_attribute(types, scope, sym, attr);
    Ok(())
}

pub fn read_machaddr(args: &mut IStream, size: &mut i32, glb: &Architecture) -> Result<Address> {
    parse_machaddr(args, size, glb, false)
}

pub fn ifc_source(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    args.ws();
    if args.eof() {
        return Err(IfaceError::Parse("filename parameter required for source".to_string()));
    }
    let mut filename = String::new();
    args.read_word_into(&mut filename);
    status.push_script_file(&filename, &format!("{filename}> "))
}

pub fn ifc_option(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No load image present")?;
    let mut optname = String::new();
    let mut p1 = String::new();
    let mut p2 = String::new();
    let mut p3 = String::new();
    args.ws().read_word_into(&mut optname).ws();
    if optname.is_empty() {
        return Err(IfaceError::Parse("Missing option name".to_string()));
    }
    if !args.eof() {
        args.read_word_into(&mut p1).ws();
        if !args.eof() {
            args.read_word_into(&mut p2).ws();
            if !args.eof() {
                args.read_word_into(&mut p3).ws();
                if !args.eof() {
                    return Err(IfaceError::Parse("Too many option parameters".to_string()));
                }
            }
        }
    }
    match OptionDatabase::set(glb, ElementId::find(&optname, 0), &p1, &p2, &p3) {
        Ok(res) => {
            out_write(&optr, &format!("{res}\n"));
            Ok(())
        }
        Err(Error::Parse(message)) => {
            out_write(&optr, &format!("{message}\n"));
            Err(IfaceError::Parse("Bad option".to_string()))
        }
        Err(err) if err.is_recov() => {
            out_write(&optr, &format!("{}\n", err.explain()));
            Err(IfaceError::Execution("Bad option".to_string()))
        }
        Err(err) => Err(err.into()),
    }
}

fn report_c_parse(result: Result<()>, optr: &crate::interface::OutStream) -> IfaceResult<()> {
    match result {
        Ok(()) => Ok(()),
        Err(Error::Parse(message)) => {
            out_write(optr, &format!("Error in C syntax: {message}\n"));
            Err(IfaceError::Execution("Bad C syntax".to_string()))
        }
        Err(err) => Err(err.into()),
    }
}

pub fn ifc_parse_file(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No load image present")?;
    let mut filename = String::new();
    args.ws().read_word_into(&mut filename);
    if filename.is_empty() {
        return Err(IfaceError::Parse("Missing filename".to_string()));
    }
    let Ok(file) = std::fs::File::open(&filename) else {
        return Err(IfaceError::Execution(format!("Unable to open file: {filename}")));
    };
    let mut reader = BufReader::new(file);
    report_c_parse(parse_c(glb, &mut reader), &optr)
}

pub fn ifc_parse_line(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No load image present")?;
    args.ws();
    if args.eof() {
        return Err(IfaceError::Parse("No input".to_string()));
    }
    report_c_parse(parse_c(glb, args), &optr)
}

pub fn ifc_adjust_vma(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    let mut adjust: u64 = 0;
    if dcp.conf.is_none() {
        return Err(IfaceError::Execution("No load image present".to_string()));
    }
    args.unset_basefield();
    args.ws().read_u64(&mut adjust);
    if adjust == 0 {
        return Err(IfaceError::Parse("No adjustment parameter".to_string()));
    }
    let loader = dcp
        .loader_slot
        .as_ref()
        .and_then(|slot| slot.read().expect("poisoned lock").clone());
    match loader {
        Some(loader) => {
            loader.adjust_vma_shared(adjust as i64);
            Ok(())
        }
        None => Err(IfaceError::Execution(
            "Load image does not support vma adjustment".to_string(),
        )),
    }
}

pub fn ifc_funcload(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let mut funcname = String::new();
    args.read_word_into(&mut funcname);
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No image loaded")?;
    let delim = glb.get_scope_delimiter();
    let mut basename = String::new();
    let symboltab = symbol_table(glb)?;
    let Some(funcscope) = symboltab.resolve_scope_from_symbol_name(&funcname, &delim, &mut basename, None) else {
        return Err(IfaceError::Execution(format!("Bad namespace: {funcname}")));
    };
    let fdsym = symboltab.scope_query_function_by_name(funcscope, &basename);
    dcp.fd = fdsym;
    let Some(sym) = fdsym else {
        return Err(IfaceError::Execution(format!("Unknown function name: {funcname}")));
    };
    let glb = conf_mut(dcp, "No image loaded")?;
    let hascode = with_function(glb, sym, |fd, _glb| Ok(!fd.has_no_code()))?;
    if hascode {
        dcp.follow_flow(&optr, 0)?;
    }
    Ok(())
}

pub fn ifc_addrrange_load(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No image loaded")?;
    let mut size: i32 = 0;
    let offset = read_machaddr(args, &mut size, glb)?;
    args.ws();
    if size <= offset.get_addr_size() {
        size = 0;
    }
    if glb.loader.is_none() {
        return Err(IfaceError::Execution("No binary loaded".to_string()));
    }
    let mut name = String::new();
    args.read_word_into(&mut name);
    if name.is_empty() {
        glb.name_function(&offset, &mut name);
    }
    let scope = global_scope(glb)?;
    let sym = Database::scope_add_function(glb, scope, &offset, &name)?;
    dcp.fd = Some(sym);
    dcp.follow_flow(&optr, size)
}

pub fn ifc_cleararch(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    decomp_data(status).clear_architecture();
    Ok(())
}

pub fn ifc_read_symbols(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No load image present")?;
    if glb.loader.is_none() {
        return Err(IfaceError::Execution("No binary loaded".to_string()));
    }
    glb.read_loader_symbols()?;
    Ok(())
}

pub fn ifc_mapaddress(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    let fdsym = dcp.fd;
    let glb = conf_mut(dcp, "No load image present")?;
    let mut size: i32 = 0;
    let addr = read_machaddr(args, &mut size, glb)?;
    args.ws();
    let mut name = String::new();
    let ct = parse_type(args, &mut name, glb)?;
    match fdsym {
        Some(sym) => {
            let scope = with_function(glb, sym, |fd, _glb| {
                fd.get_scope_local()
                    .ok_or_else(|| IfaceError::Execution("Function has no local scope".to_string()))
            })?;
            let entry = Database::scope_add_symbol_at(glb, scope, &name, Some(ct), &addr, &Address::invalid())?;
            let newsym = symbol_table(glb)?.entry(entry).get_symbol();
            set_symbol_attribute(glb, newsym, Varnode::NAMELOCK | Varnode::TYPELOCK)?;
        }
        None => {
            let mut flags = Varnode::NAMELOCK | Varnode::TYPELOCK;
            flags |= symbol_table(glb)?.get_property(&addr);
            let delim = glb.get_scope_delimiter();
            let num_spaces = glb.manager.num_spaces();
            let mut basename = String::new();
            let scope = symbol_table(glb)?.find_create_scope_from_symbol_name(
                &name,
                &delim,
                &mut basename,
                None,
                num_spaces,
            )?;
            let entry = Database::scope_add_symbol_at(glb, scope, &basename, Some(ct), &addr, &Address::invalid())?;
            let newsym = symbol_table(glb)?.entry(entry).get_symbol();
            set_symbol_attribute(glb, newsym, flags)?;
            let symboltab = symbol_table(glb)?;
            if symboltab.scope(scope).get_parent().is_some() {
                let entry_data = symboltab.entry(entry);
                let space = entry_data
                    .get_addr()
                    .get_space()
                    .cloned()
                    .ok_or_else(|| Error::Lowlevel("symbol entry has no space".to_string()))?;
                let first = entry_data.get_first();
                let last = entry_data.get_last();
                symboltab.add_range(scope, &space, first, last);
            }
        }
    }
    Ok(())
}

fn local_scope(glb: &mut Architecture, sym: SymbolId) -> IfaceResult<crate::database::ScopeId> {
    with_function(glb, sym, |fd, _glb| {
        fd.get_scope_local()
            .ok_or_else(|| IfaceError::Execution("Function has no local scope".to_string()))
    })
}

pub fn ifc_maphash(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    let Some(fdsym) = dcp.fd else {
        return Err(IfaceError::Execution("No function loaded".to_string()));
    };
    let glb = conf_mut(dcp, "No function loaded")?;
    let mut size: i32 = 0;
    let addr = read_machaddr(args, &mut size, glb)?;
    let mut hash: u64 = 0;
    args.hex().read_u64(&mut hash);
    args.ws();
    let mut name = String::new();
    let ct = parse_type(args, &mut name, glb)?;
    let scope = local_scope(glb, fdsym)?;
    let types = glb
        .types
        .as_deref()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing type factory".to_string())))?;
    let symboltab = glb
        .symboltab
        .as_deref_mut()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing symbol table".to_string())))?;
    let sym = symboltab.scope_add_dynamic_symbol(scope, &name, Some(ct), &addr, hash, types)?;
    set_symbol_attribute(glb, sym, Varnode::NAMELOCK | Varnode::TYPELOCK)
}

pub fn ifc_map_param(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(IfaceError::Execution("No function loaded".to_string()));
    }
    let mut index: i32 = 0;
    args.dec().read_i32(&mut index);
    with_current_function(dcp, |fd, glb| {
        let mut size: i32 = 0;
        let mut name = String::new();
        let addr = read_machaddr(args, &mut size, glb)?;
        let tp = parse_type(args, &mut name, glb)?;
        let piece = ParameterPieces {
            addr,
            tp: Some(tp),
            flags: ParameterPieces::TYPELOCK | ParameterPieces::NAMELOCK,
        };
        fd.get_func_proto_mut().set_param(index, &name, &piece, glb)?;
        Ok(())
    })
}

pub fn ifc_map_return(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(IfaceError::Execution("No function loaded".to_string()));
    }
    with_current_function(dcp, |fd, glb| {
        let mut size: i32 = 0;
        let mut name = String::new();
        let addr = read_machaddr(args, &mut size, glb)?;
        let tp = parse_type(args, &mut name, glb)?;
        let piece = ParameterPieces {
            addr,
            tp: Some(tp),
            flags: ParameterPieces::TYPELOCK,
        };
        fd.get_func_proto_mut().set_output(&piece, glb)?;
        Ok(())
    })
}

pub fn ifc_mapfunction(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    let has_loader = dcp.conf.as_ref().map(|glb| glb.loader.is_some()).unwrap_or(false);
    if !has_loader {
        return Err(IfaceError::Execution("No binary loaded".to_string()));
    }
    let glb = conf_mut(dcp, "No binary loaded")?;
    let mut size: i32 = 0;
    let addr = read_machaddr(args, &mut size, glb)?;
    let mut name = String::new();
    args.read_word_into(&mut name);
    if name.is_empty() {
        glb.name_function(&addr, &mut name);
    }
    let delim = glb.get_scope_delimiter();
    let num_spaces = glb.manager.num_spaces();
    let mut basename = String::new();
    let scope =
        symbol_table(glb)?.find_create_scope_from_symbol_name(&name, &delim, &mut basename, None, num_spaces)?;
    let sym = Database::scope_add_function(glb, scope, &addr, &name)?;
    dcp.fd = Some(sym);
    let mut nocode = String::new();
    args.ws().read_word_into(&mut nocode);
    if nocode == "nocode" {
        with_current_function(dcp, |fd, _glb| {
            fd.set_no_code(true);
            Ok(())
        })?;
    }
    Ok(())
}

pub fn ifc_mapexternalref(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No load image present")?;
    let mut size1: i32 = 0;
    let mut size2: i32 = 0;
    let addr1 = read_machaddr(args, &mut size1, glb)?;
    let addr2 = read_machaddr(args, &mut size2, glb)?;
    let mut name = String::new();
    args.read_word_into(&mut name);
    let scope = global_scope(glb)?;
    Database::scope_add_external_ref(glb, scope, &addr1, &addr2, &name)?;
    Ok(())
}

pub fn ifc_maplabel(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    let fdsym = dcp.fd;
    let mut name = String::new();
    args.read_word_into(&mut name);
    if name.is_empty() {
        return Err(IfaceError::Parse("Need label name and address".to_string()));
    }
    let glb = conf_mut(dcp, "No load image present")?;
    let mut size: i32 = 0;
    let addr = read_machaddr(args, &mut size, glb)?;
    let scope = match fdsym {
        Some(sym) => local_scope(glb, sym)?,
        None => global_scope(glb)?,
    };
    let sym = Database::scope_add_code_label(glb, scope, &addr, &name)?;
    let types = glb
        .types
        .as_deref()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing type factory".to_string())))?;
    let symboltab = glb
        .symboltab
        .as_deref_mut()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing symbol table".to_string())))?;
    symboltab.scope_set_attribute(types, scope, sym, Varnode::NAMELOCK | Varnode::TYPELOCK);
    Ok(())
}

pub fn ifc_mapconvert(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    let Some(fdsym) = dcp.fd else {
        return Err(IfaceError::Execution("No function loaded".to_string()));
    };
    let glb = conf_mut(dcp, "No function loaded")?;
    let mut name = String::new();
    let mut value: u64 = 0;
    let mut hash: u64 = 0;
    let mut size: i32 = 0;
    args.read_word_into(&mut name);
    let format = match name.as_str() {
        "hex" => Symbol::FORCE_HEX,
        "dec" => Symbol::FORCE_DEC,
        "bin" => Symbol::FORCE_BIN,
        "oct" => Symbol::FORCE_OCT,
        "char" => Symbol::FORCE_CHAR,
        _ => return Err(IfaceError::Parse("Bad convert format".to_string())),
    };
    args.ws().hex().read_u64(&mut value);
    let addr = read_machaddr(args, &mut size, glb)?;
    args.hex().read_u64(&mut hash);
    let scope = local_scope(glb, fdsym)?;
    Database::scope_add_equate_symbol(glb, scope, "", format, value, &addr, hash)?;
    Ok(())
}

pub fn ifc_mapunionfacet(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    let Some(fdsym) = dcp.fd else {
        return Err(IfaceError::Execution("No function loaded".to_string()));
    };
    let glb = conf_mut(dcp, "No function loaded")?;
    let mut union_name = String::new();
    args.ws().read_word_into(&mut union_name);
    let types = types_mut(glb)?;
    let ct = types.find_by_name(&union_name);
    let Some(ct) = ct.filter(|ct| types.get(*ct).get_metatype() == TypeMetatype::Union) else {
        return Err(IfaceError::Parse(format!("Bad union data-type: {union_name}")));
    };
    let mut field_num: i32 = 0;
    args.ws().dec().read_i32(&mut field_num);
    let num_depend = types.get(ct).num_depend(types);
    if field_num < -1 || field_num >= num_depend {
        return Err(IfaceError::Parse("Bad field index".to_string()));
    }
    let mut size: i32 = 0;
    let addr = read_machaddr(args, &mut size, glb)?;
    let mut hash: u64 = 0;
    args.hex().read_u64(&mut hash);
    let symname = format!("unionfacet{}_{:x}", field_num + 1, addr.get_offset());
    let scope = local_scope(glb, fdsym)?;
    let sym = Database::scope_add_union_facet_symbol(glb, scope, &symname, ct, field_num, &addr, hash)?;
    set_symbol_attribute(glb, sym, Varnode::TYPELOCK | Varnode::NAMELOCK)
}

fn lock_context(
    glb: &Architecture,
) -> IfaceResult<std::sync::MutexGuard<'_, dyn crate::globalcontext::ContextDatabase + Send + 'static>> {
    let context = glb
        .context
        .as_ref()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing context database".to_string())))?;
    context
        .lock()
        .map_err(|_| IfaceError::Core(Error::Lowlevel("context database lock is poisoned".to_string())))
}

pub fn ifc_setcontextrange(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No load image present")?;
    let mut name = String::new();
    args.read_word_into(&mut name).ws();
    if name.is_empty() {
        return Err(IfaceError::Parse("Missing context variable name".to_string()));
    }
    args.unset_basefield();
    let mut value: u32 = 0xbadbeef;
    args.read_u32(&mut value);
    if value == 0xbadbeef {
        return Err(IfaceError::Parse("Missing context value".to_string()));
    }
    args.ws();
    if args.eof() {
        lock_context(glb)?.set_variable_default(&name, value)?;
        return Ok(());
    }
    let mut size1: i32 = 0;
    let mut size2: i32 = 0;
    let addr1 = read_machaddr(args, &mut size1, glb)?;
    let addr2 = read_machaddr(args, &mut size2, glb)?;
    if addr1.is_invalid() || addr2.is_invalid() {
        return Err(IfaceError::Parse("Invalid address range".to_string()));
    }
    if addr2 <= addr1 {
        return Err(IfaceError::Parse("Bad address range".to_string()));
    }
    lock_context(glb)?.set_variable_region(&name, &addr1, &addr2, value)?;
    Ok(())
}

pub fn ifc_settrackedrange(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No load image present")?;
    let mut name = String::new();
    args.read_word_into(&mut name).ws();
    if name.is_empty() {
        return Err(IfaceError::Parse("Missing tracked register name".to_string()));
    }
    args.unset_basefield();
    let mut value: u64 = 0xbadbeef;
    args.read_u64(&mut value);
    if value == 0xbadbeef {
        return Err(IfaceError::Parse("Missing context value".to_string()));
    }
    args.ws();
    let translate = glb
        .translate
        .as_deref()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing translator".to_string())))?;
    if args.eof() {
        let loc = translate.get_register(&name)?;
        let mut context = lock_context(glb)?;
        let track = context.get_tracked_default();
        track.push(TrackedContext { loc, val: value });
        return Ok(());
    }
    let mut size1: i32 = 0;
    let mut size2: i32 = 0;
    let addr1 = read_machaddr(args, &mut size1, glb)?;
    let addr2 = read_machaddr(args, &mut size2, glb)?;
    if addr1.is_invalid() || addr2.is_invalid() {
        return Err(IfaceError::Parse("Invalid address range".to_string()));
    }
    if addr2 <= addr1 {
        return Err(IfaceError::Parse("Bad address range".to_string()));
    }
    let loc = translate.get_register(&name)?;
    let mut context = lock_context(glb)?;
    let def = context.get_tracked_default().clone();
    let track = context.create_set(&addr1, &addr2);
    *track = def;
    track.push(TrackedContext { loc, val: value });
    Ok(())
}

pub fn ifc_global_add(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No image loaded")?;
    let mut size: i32 = 0;
    let addr = read_machaddr(args, &mut size, glb)?;
    let first = addr.get_offset();
    let last = first.wrapping_add((size - 1) as i64 as u64);
    let scope = global_scope(glb)?;
    let space = addr
        .get_space()
        .cloned()
        .ok_or_else(|| Error::Lowlevel("invalid address".to_string()))?;
    symbol_table(glb)?.add_range(scope, &space, first, last);
    Ok(())
}

pub fn ifc_global_remove(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No image loaded")?;
    let mut size: i32 = 0;
    let addr = read_machaddr(args, &mut size, glb)?;
    let first = addr.get_offset();
    let last = first.wrapping_add((size - 1) as i64 as u64);
    let scope = global_scope(glb)?;
    let space = addr
        .get_space()
        .cloned()
        .ok_or_else(|| Error::Lowlevel("invalid address".to_string()))?;
    symbol_table(glb)?.remove_range(scope, &space, first, last);
    Ok(())
}

pub fn ifc_globalify(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No load image present")?;
    glb.globalify()?;
    out_write(&optr, "Successfully made all registers/memory locations global\n");
    Ok(())
}

pub fn ifc_global_registers(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No load image present")?;
    let mut reglist = std::collections::BTreeMap::new();
    glb.translate
        .as_deref()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing translator".to_string())))?
        .get_all_registers(&mut reglist);
    let mut spc: Option<i32> = None;
    let mut lastoff: u64 = 0;
    let globalscope = global_scope(glb)?;
    let mut count = 0;
    for (dat, regname) in reglist.iter() {
        let space = dat
            .space
            .clone()
            .ok_or_else(|| Error::Lowlevel("register without space".to_string()))?;
        if spc == Some(space.get_index()) && dat.offset <= lastoff {
            continue;
        }
        spc = Some(space.get_index());
        lastoff = dat.offset.wrapping_add(dat.size as u64).wrapping_sub(1);
        let addr = Address::new(space, dat.offset);
        let mut flags: u32 = 0;
        symbol_table(glb)?.scope_query_properties(globalscope, &addr, dat.size as i32, &Address::invalid(), &mut flags);
        if (flags & Varnode::PERSIST) != 0 {
            let ct = types_mut(glb)?.get_base(dat.size as i32, TypeMetatype::Uint)?;
            Database::scope_add_symbol_at(glb, globalscope, regname, Some(ct), &addr, &Address::invalid())?;
            count += 1;
        }
    }
    if count == 0 {
        out_write(&optr, "No global registers\n");
    } else {
        out_write(
            &optr,
            &format!("Successfully made a global symbol for {count} registers\n"),
        );
    }
    Ok(())
}

fn mark_property_range(args: &mut IStream, status: &mut IfaceStatus, flag: u32, message: &str) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No load image present")?;
    let mut size: i32 = 0;
    let addr = read_machaddr(args, &mut size, glb)?;
    if size == 0 {
        return Err(IfaceError::Execution("Must specify a size".to_string()));
    }
    let space = addr
        .get_space()
        .cloned()
        .ok_or_else(|| Error::Lowlevel("invalid address".to_string()))?;
    let range = Range::new(
        space,
        addr.get_offset(),
        addr.get_offset().wrapping_add((size - 1) as i64 as u64),
    );
    let symboltab = glb
        .symboltab
        .as_deref_mut()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing symbol table".to_string())))?;
    symboltab.set_property_range(flag, &range, &glb.manager);
    out_write(&optr, message);
    Ok(())
}

pub fn ifc_volatile(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    mark_property_range(
        args,
        status,
        Varnode::VOLATIL,
        "Successfully marked range as volatile\n",
    )
}

pub fn ifc_readonly(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    mark_property_range(
        args,
        status,
        Varnode::READONLY,
        "Successfully marked range as readonly\n",
    )
}

pub fn ifc_pointer_setting(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No load image present")?;
    let mut type_name = String::new();
    let mut base_type = String::new();
    let mut setting = String::new();
    args.ws();
    if args.eof() {
        return Err(IfaceError::Parse("Missing name".to_string()));
    }
    args.read_word_into(&mut type_name).ws();
    if args.eof() {
        return Err(IfaceError::Parse("Missing base-type".to_string()));
    }
    args.read_word_into(&mut base_type).ws();
    if args.eof() {
        return Err(IfaceError::Parse("Missing setting".to_string()));
    }
    args.read_word_into(&mut setting).ws();
    if setting == "offset" {
        let mut off: i32 = -1;
        args.unset_basefield();
        args.read_i32(&mut off);
        if off <= 0 {
            return Err(IfaceError::Parse("Missing offset".to_string()));
        }
        let spc = glb
            .manager
            .get_default_data_space()
            .ok_or_else(|| Error::Lowlevel("missing default data space".to_string()))?;
        let types = types_mut(glb)?;
        let bt = types.find_by_name(&base_type);
        let Some(bt) = bt.filter(|bt| types.get(*bt).get_metatype() == TypeMetatype::Struct) else {
            return Err(IfaceError::Parse("Base-type must be a structure".to_string()));
        };
        let ptrto = crate::types::Datatype::get_ptr_to_from_parent(bt, off, types)?;
        types.get_type_pointer_rel_named(
            spc.get_addr_size() as i32,
            bt,
            ptrto,
            spc.get_word_size() as i32,
            off,
            &type_name,
        )?;
    } else if setting == "space" {
        let mut space_name = String::new();
        args.read_word_into(&mut space_name);
        if space_name.is_empty() {
            return Err(IfaceError::Parse("Missing name of address space".to_string()));
        }
        let spc = glb.manager.get_space_by_name(&space_name);
        let types = types_mut(glb)?;
        let Some(ptr_to) = types.find_by_name(&base_type) else {
            return Err(IfaceError::Parse(format!("Unknown base data-type: {base_type}")));
        };
        let Some(spc) = spc else {
            return Err(IfaceError::Parse(format!("Unknown space: {space_name}")));
        };
        types.get_type_pointer_with_space(ptr_to, &spc, &type_name)?;
    } else {
        return Err(IfaceError::Parse(format!("Unknown pointer setting: {setting}")));
    }
    out_write(&optr, &format!("Successfully created pointer: {type_name}\n"));
    Ok(())
}

pub fn ifc_prefer_split(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No load image present")?;
    let mut size: i32 = 0;
    let addr = read_machaddr(args, &mut size, glb)?;
    if size == 0 {
        return Err(IfaceError::Execution("Must specify a size".to_string()));
    }
    let mut split: i32 = -1;
    args.ws();
    if args.eof() {
        return Err(IfaceError::Parse("Missing split offset".to_string()));
    }
    args.dec().read_i32(&mut split);
    if split == -1 {
        return Err(IfaceError::Parse("Bad split offset".to_string()));
    }
    let mut rec = PreferSplitRecord::default();
    rec.storage.space = addr.get_space().cloned();
    rec.storage.offset = addr.get_offset();
    rec.storage.size = size as u32;
    rec.splitoffset = split;
    glb.splitrecords.push(rec);
    out_write(&optr, "Successfully added split record\n");
    Ok(())
}

pub fn ifc_deadcodedelay(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    let fdsym = dcp.fd;
    let glb = conf_mut(dcp, "No load image present")?;
    let mut name = String::new();
    let mut delay: i32 = -1;
    args.read_word_into(&mut name);
    args.ws();
    args.read_i32(&mut delay);
    let Some(spc) = glb.manager.get_space_by_name(&name) else {
        return Err(IfaceError::Parse(format!("Bad space: {name}")));
    };
    if delay == -1 {
        return Err(IfaceError::Parse("Need delay integer".to_string()));
    }
    match fdsym {
        Some(sym) => {
            with_function(glb, sym, |fd, _glb| {
                fd.get_override().insert_deadcode_delay(&spc, delay);
                Ok(())
            })?;
            out_write(&optr, "Successfully overrided deadcode delay for single function\n");
        }
        None => {
            glb.manager.set_deadcode_delay(&spc, delay);
            out_write(&optr, "Successfully overrided deadcode delay for all functions\n");
        }
    }
    Ok(())
}
