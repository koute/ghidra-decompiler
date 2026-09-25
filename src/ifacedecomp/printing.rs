use std::io::Write;
use std::time::Instant;

use crate::action::{BREAK_ACTION, BREAK_START, STATUS_END, STATUS_START};
use crate::address::Address;
use crate::architecture::Architecture;
use crate::database::SymbolId;
use crate::error::Error;
use crate::fspec::ProtoModel;
use crate::funcdata::Funcdata;
use crate::graph::{dump_controlflow_graph, dump_dataflow_graph, dump_dom_graph};
use crate::interface::{IStream, IfaceError, IfaceResult, IfaceStatus, OutStream, out_write};
use crate::paramid::ParamIdAnalysis;
use crate::space::SpaceType;
use crate::types::print_data;

use super::load::read_machaddr;
use super::{
    IfaceAssemblyEmit, conf_mut, decomp_data, function_name, iterate_functions_addr_order,
    iterate_functions_leaf_order, symbol_table, with_current_action, with_current_function, with_function,
    with_printer,
};

fn no_function(message: &str) -> IfaceError {
    IfaceError::Execution(message.to_string())
}

pub fn ifc_printdisasm(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let fileoptr = status.fileoptr.clone();
    let dcp = decomp_data(status);
    args.ws();
    let (mut addr, mut size) = if args.eof() {
        let Some(sym) = dcp.fd else {
            return Err(no_function("No function selected"));
        };
        let glb = conf_mut(dcp, "No function selected")?;
        let (name, addr, size) = with_function(glb, sym, |fd, _glb| {
            Ok((fd.get_name().to_string(), fd.get_address().clone(), fd.get_size()))
        })?;
        out_write(&fileoptr, &format!("Assembly listing for {name}\n"));
        (addr, size)
    } else {
        let glb = conf_mut(dcp, "No load image present")?;
        let mut size: i32 = 0;
        let addr = read_machaddr(args, &mut size, glb)?;
        args.ws();
        let offset2 = read_machaddr(args, &mut size, glb)?;
        let size = offset2.get_offset().wrapping_sub(addr.get_offset()) as i32;
        (addr, size)
    };
    let glb = conf_mut(dcp, "No load image present")?;
    let translate = glb
        .translate
        .as_deref()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing translator".to_string())))?;
    let mut assem = IfaceAssemblyEmit::new(10);
    while size > 0 {
        let result = translate.print_assembly(&mut assem, &addr);
        out_write(&fileoptr, &std::mem::take(&mut assem.out));
        let sz = result?;
        addr = addr.add(sz as i64);
        size -= sz;
    }
    Ok(())
}

pub fn ifc_dump(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let fileoptr = status.fileoptr.clone();
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No load image present")?;
    let mut size: i32 = 0;
    let offset = read_machaddr(args, &mut size, glb)?;
    let loader = glb
        .loader
        .clone()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing load image".to_string())))?;
    let buffer = loader.load(size, &offset)?;
    let mut text = String::new();
    print_data(&mut text, Some(&buffer), size, &offset);
    out_write(&fileoptr, &text);
    Ok(())
}

pub fn ifc_dumpbinary(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No load image present")?;
    let mut size: i32 = 0;
    let offset = read_machaddr(args, &mut size, glb)?;
    args.ws();
    if args.eof() {
        return Err(IfaceError::Parse("Missing file name for binary dump".to_string()));
    }
    let mut filename = String::new();
    args.read_word_into(&mut filename);
    let Ok(mut file) = std::fs::File::create(&filename) else {
        return Err(IfaceError::Execution(format!("Unable to open file {filename}")));
    };
    let loader = glb
        .loader
        .clone()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing load image".to_string())))?;
    let buffer = loader.load(size, &offset)?;
    let _ = file.write_all(&buffer);
    Ok(())
}

fn perform_report(optr: &OutStream, res: i32, glb: &mut Architecture) {
    if res < 0 {
        out_write(optr, "Break at ");
        let mut state = String::new();
        if let Some(action) = glb.allacts.get_current() {
            action.print_state(&mut state);
        }
        out_write(optr, &state);
    } else {
        out_write(optr, "Decompilation complete");
        if res == 0 {
            out_write(optr, " (no change)");
        }
    }
    out_write(optr, "\n");
}

pub fn ifc_decompile(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function("No function selected"));
    }
    with_current_function(dcp, |fd, glb| {
        if fd.has_no_code() {
            out_write(&optr, &format!("No code for {}\n", fd.get_name()));
            return Ok(());
        }
        if fd.is_proc_started() {
            out_write(&optr, "Clearing old decompilation\n");
            glb.clear_analysis(fd);
        }
        out_write(&optr, &format!("Decompiling {}\n", fd.get_name()));
        let res = with_current_action(glb, |action, glb| {
            action.reset(fd, glb);
            action.perform(fd, glb)
        })?;
        perform_report(&optr, res, glb);
        Ok(())
    })
}

pub fn ifc_print_cflat(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let fileoptr = status.fileoptr.clone();
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function("No function selected"));
    }
    with_current_function(dcp, |fd, glb| {
        let ((), text) = with_printer(glb, Some(fd), |printer, ctx| {
            printer.set_flat(true);
            let result = printer.doc_function(ctx);
            printer.set_flat(false);
            result
        })?;
        out_write(&fileoptr, &text);
        Ok(())
    })
}

pub fn ifc_print_cglobals(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let fileoptr = status.fileoptr.clone();
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No load image present")?;
    let ((), text) = with_printer(glb, None, |printer, ctx| printer.doc_all_globals(ctx))?;
    out_write(&fileoptr, &text);
    Ok(())
}

pub fn ifc_print_ctypes(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let fileoptr = status.fileoptr.clone();
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No load image present")?;
    if glb.types.is_some() {
        let ((), text) = with_printer(glb, None, |printer, ctx| printer.doc_type_definitions(ctx))?;
        out_write(&fileoptr, &text);
    }
    Ok(())
}

pub fn ifc_print_cxml(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let fileoptr = status.fileoptr.clone();
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function("No function selected"));
    }
    with_current_function(dcp, |fd, glb| {
        let ((), text) = with_printer(glb, Some(fd), |printer, ctx| {
            printer.set_markup(true);
            printer.set_packed_output(false);
            let result = printer.doc_function(ctx);
            printer.get_output_stream().push(b'\n');
            printer.set_markup(false);
            result
        })?;
        out_write(&fileoptr, &text);
        Ok(())
    })
}

pub fn ifc_print_cstruct(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let fileoptr = status.fileoptr.clone();
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function("No function selected"));
    }
    with_current_function(dcp, |fd, glb| {
        let ((), text) = with_printer(glb, Some(fd), |printer, ctx| printer.doc_function(ctx))?;
        out_write(&fileoptr, &text);
        Ok(())
    })
}

pub fn ifc_print_language(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let fileoptr = status.fileoptr.clone();
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function("No function selected"));
    }
    args.ws();
    if args.eof() {
        return Err(IfaceError::Parse("No print language specified".to_string()));
    }
    let mut langroot = String::new();
    args.read_word_into(&mut langroot);
    langroot.push_str("-language");
    with_current_function(dcp, |fd, glb| {
        let curlangname = glb.printlist[glb.print]
            .as_deref()
            .map(|printer| printer.get_name().to_string())
            .unwrap_or_default();
        glb.set_print_language(&langroot)?;
        let result = with_printer(glb, Some(fd), |printer, ctx| printer.doc_function(ctx));
        let reset = glb.set_print_language(&curlangname);
        let ((), text) = result?;
        reset?;
        out_write(&fileoptr, &text);
        Ok(())
    })
}

pub fn ifc_print_raw(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let fileoptr = status.fileoptr.clone();
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function("No function selected"));
    }
    with_current_function(dcp, |fd, glb| {
        let mut text = String::new();
        let result = fd.print_raw(&mut text, glb);
        out_write(&fileoptr, &text);
        result?;
        Ok(())
    })
}

pub fn ifc_listaction(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let fileoptr = status.fileoptr.clone();
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "Decompile action not loaded")?;
    let mut text = String::new();
    if let Some(action) = glb.allacts.get_current() {
        action.print(&mut text, 0, 0);
    }
    out_write(&fileoptr, &text);
    Ok(())
}

pub fn ifc_list_override(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function("No function selected"));
    }
    with_current_function(dcp, |fd, glb| {
        let mut text = format!("Function: {}\n", fd.get_name());
        let result = fd.get_override().print_raw(&mut text, glb);
        out_write(&optr, &text);
        result?;
        Ok(())
    })
}

pub fn ifc_listprototypes(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No load image present")?;
    let mut text = String::new();
    for model in glb.proto_model_map.values() {
        text.push_str(glb.proto_models.get(*model).get_name());
        if Some(*model) == glb.defaultfp {
            text.push_str(" default");
        } else if Some(*model) == glb.evalfp_called {
            text.push_str(" eval called");
        } else if Some(*model) == glb.evalfp_current {
            text.push_str(" eval current");
        }
        text.push('\n');
    }
    out_write(&optr, &text);
    Ok(())
}

fn set_break(args: &mut IStream, status: &mut IfaceStatus, tp: u32) -> IfaceResult<()> {
    let mut specify = String::new();
    args.read_word_into(&mut specify).ws();
    if specify.is_empty() {
        return Err(IfaceError::Execution("No action/rule specified".to_string()));
    }
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "Decompile action not loaded")?;
    let res = match glb.allacts.get_current() {
        Some(action) => action.set_break_point(tp, &specify),
        None => false,
    };
    if !res {
        return Err(IfaceError::Execution(format!("Bad action/rule specifier: {specify}")));
    }
    Ok(())
}

pub fn ifc_breakaction(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    set_break(args, status, BREAK_ACTION)
}

pub fn ifc_breakstart(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    set_break(args, status, BREAK_START)
}

pub fn ifc_print_tree(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let fileoptr = status.fileoptr.clone();
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function("No function selected"));
    }
    with_current_function(dcp, |fd, glb| {
        let mut text = String::new();
        fd.print_varnode_tree(&mut text, glb);
        out_write(&fileoptr, &text);
        Ok(())
    })
}

pub fn ifc_print_blocktree(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let fileoptr = status.fileoptr.clone();
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function("No function selected"));
    }
    with_current_function(dcp, |fd, glb| {
        let mut text = String::new();
        fd.print_block_tree(&mut text, glb);
        out_write(&fileoptr, &text);
        Ok(())
    })
}

pub fn ifc_print_spaces(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let fileoptr = status.fileoptr.clone();
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No load image present")?;
    let num = glb.manager.num_spaces();
    let mut text = String::new();
    for index in 0..num {
        let Some(spc) = glb.manager.get_space(index) else {
            continue;
        };
        text.push_str(&format!(
            "{} : '{}' {}",
            spc.get_index(),
            spc.get_shortcut(),
            spc.get_name()
        ));
        match spc.get_type() {
            SpaceType::Constant => text.push_str(" constant "),
            SpaceType::Processor => text.push_str(" processor"),
            SpaceType::Spacebase => text.push_str(" spacebase"),
            SpaceType::Internal => text.push_str(" internal "),
            _ => text.push_str(" special  "),
        }
        if spc.is_big_endian() {
            text.push_str(" big  ");
        } else {
            text.push_str(" small");
        }
        text.push_str(&format!(
            " addrsize={} wordsize={} delay={}\n",
            spc.get_addr_size(),
            spc.get_word_size(),
            spc.get_delay()
        ));
    }
    out_write(&fileoptr, &text);
    Ok(())
}

pub fn ifc_print_high(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function("No function selected"));
    }
    let mut varname = String::new();
    args.read_word_into(&mut varname).ws();
    with_current_function(dcp, |fd, glb| {
        let Some(high) = fd.find_high(&varname, glb)? else {
            return Err(IfaceError::Execution(format!("Unknown variable name: {varname}")));
        };
        let mut text = String::new();
        fd.high_print_info(high, &mut text, glb);
        out_write(&optr, &text);
        Ok(())
    })
}

pub fn ifc_print_param_measures(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let fileoptr = status.fileoptr.clone();
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function("No function selected"));
    }
    with_current_function(dcp, |fd, glb| {
        let pidanalysis = ParamIdAnalysis::new(fd, false, glb);
        let mut text = String::new();
        pidanalysis.save_pretty(&mut text, true, fd, glb);
        text.push('\n');
        out_write(&fileoptr, &text);
        Ok(())
    })
}

pub fn ifc_print_localrange(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function("No function selected"));
    }
    with_current_function(dcp, |fd, glb| {
        let mut text = String::new();
        fd.print_local_range(&mut text, glb);
        out_write(&optr, &text);
        Ok(())
    })
}

pub fn ifc_print_map(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let fileoptr = status.fileoptr.clone();
    let mut name = String::new();
    args.read_word_into(&mut name);
    let dcp = decomp_data(status);
    let fdsym = dcp.fd;
    let glb = conf_mut(dcp, "No load image")?;
    let scope = if !name.is_empty() || fdsym.is_none() {
        let mut fullname = format!("{name}::a");
        let delim = glb.get_scope_delimiter();
        let lookup = fullname.clone();
        symbol_table(glb)?.resolve_scope_from_symbol_name(&lookup, &delim, &mut fullname, None)
    } else {
        let sym = fdsym.expect("function is selected");
        with_function(glb, sym, |fd, _glb| Ok(fd.get_scope_local()))?
    };
    let Some(scope) = scope else {
        return Err(IfaceError::Execution(format!("No map named: {name}")));
    };
    let delim = glb.get_scope_delimiter();
    let types = glb
        .types
        .as_deref()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing type factory".to_string())))?;
    let symboltab = glb
        .symboltab
        .as_deref()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing symbol table".to_string())))?;
    let mut text = symboltab.scope_get_full_name(scope, &delim);
    text.push('\n');
    symboltab.scope(scope).print_bounds(&mut text);
    symboltab.scope_print_entries(scope, &mut text, types);
    out_write(&fileoptr, &text);
    Ok(())
}

fn timed_perform(fd: &mut Funcdata, glb: &mut Architecture) -> crate::error::Result<f32> {
    glb.clear_analysis(fd);
    let start = Instant::now();
    with_current_action(glb, |action, glb| {
        action.reset(fd, glb);
        action.perform(fd, glb)
    })?;
    Ok(start.elapsed().as_secs_f32() * 1000.0)
}

pub fn ifc_produce_c(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let mut name = String::new();
    args.ws().read_word_into(&mut name);
    if name.is_empty() {
        return Err(IfaceError::Parse("Need file name to write to".to_string()));
    }
    let mut output = String::new();
    let mut callback = |status: &mut IfaceStatus, sym: SymbolId| -> IfaceResult<()> {
        let glb = conf_mut(decomp_data(status), "No architecture loaded")?;
        with_function(glb, sym, |fd, glb| {
            if fd.has_no_code() {
                out_write(&optr, &format!("No code for {}\n", fd.get_name()));
                return Ok(());
            }
            let result = timed_perform(fd, glb).and_then(|duration| {
                out_write(
                    &optr,
                    &format!(
                        "Decompiled {}({}) time={:.0} ms\n",
                        fd.get_name(),
                        fd.get_size(),
                        duration
                    ),
                );
                let ((), text) = with_printer(glb, Some(fd), |printer, ctx| printer.doc_function(ctx))?;
                output.push_str(&text);
                Ok(())
            });
            if let Err(err) = result {
                if !err.is_lowlevel() {
                    return Err(err.into());
                }
                out_write(&optr, &format!("Skipping {}: {}\n", fd.get_name(), err.explain()));
            }
            glb.clear_analysis(fd);
            Ok(())
        })
    };
    let result = iterate_functions_addr_order(status, &mut callback);
    if let Ok(mut file) = std::fs::File::create(&name) {
        let _ = file.write_all(output.as_bytes());
    }
    result
}

pub fn ifc_produce_prototypes(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No load image")?;
    let _ = glb;
    if dcp.cgraph.is_none() {
        return Err(IfaceError::Execution("Callgraph has not been built".to_string()));
    }
    let glb = conf_mut(dcp, "No load image")?;
    let Some(current) = glb.evalfp_current else {
        out_write(&optr, "Always using default prototype\n");
        return Ok(());
    };
    let model = glb.proto_models.get(current);
    if !model.is_merged() {
        out_write(&optr, &format!("Always using prototype {}\n", model.get_name()));
        return Ok(());
    }
    let mut text = String::from("Trying to distinguish between prototypes:\n");
    for index in 0..model.num_models() {
        let sub = model.get_model(index);
        text.push_str(&format!("  {}\n", glb.proto_models.get(sub).get_name()));
    }
    out_write(&optr, &text);
    let mut callback = |status: &mut IfaceStatus, sym: SymbolId| -> IfaceResult<()> {
        let glb = conf_mut(decomp_data(status), "No architecture loaded")?;
        with_function(glb, sym, |fd, glb| {
            out_write(&optr, &format!("{} ", fd.get_name()));
            if fd.has_no_code() {
                out_write(&optr, "has no code\n");
                return Ok(());
            }
            if fd.get_func_proto_mut().is_input_locked(glb) {
                out_write(&optr, "has locked prototype\n");
                return Ok(());
            }
            let result = timed_perform(fd, glb).map(|duration| {
                let modelname = fd.get_func_proto().get_model_name(glb).to_string();
                out_write(&optr, &format!("proto={modelname}"));
                fd.get_func_proto_mut().set_model_lock(true);
                out_write(&optr, &format!(" time={duration:.0} ms\n"));
            });
            if let Err(err) = result {
                if !err.is_lowlevel() {
                    return Err(err.into());
                }
                out_write(&optr, &format!("Skipping {}: {}\n", fd.get_name(), err.explain()));
            }
            glb.clear_analysis(fd);
            Ok(())
        })
    };
    iterate_functions_leaf_order(status, &mut callback)
}

pub fn ifc_continue(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    conf_mut(dcp, "Decompile action not loaded")?;
    if dcp.fd.is_none() {
        return Err(no_function("No function selected"));
    }
    let glb = conf_mut(dcp, "Decompile action not loaded")?;
    let current_status = glb.allacts.get_current().map(|action| action.get_status());
    if current_status == Some(STATUS_START) {
        return Err(IfaceError::Execution("Decompilation has not been started".to_string()));
    }
    if current_status == Some(STATUS_END) {
        return Err(IfaceError::Execution("Decompilation is already complete".to_string()));
    }
    with_current_function(dcp, |fd, glb| {
        let res = with_current_action(glb, |action, glb| action.perform(fd, glb))?;
        perform_report(&optr, res, glb);
        Ok(())
    })
}

fn open_graph_file(args: &mut IStream) -> IfaceResult<String> {
    let mut filename = String::new();
    args.read_word_into(&mut filename);
    if filename.is_empty() {
        return Err(IfaceError::Parse("Missing output file".to_string()));
    }
    Ok(filename)
}

fn write_graph_file(filename: &str, text: &str) -> IfaceResult<()> {
    let Ok(mut file) = std::fs::File::create(filename) else {
        return Err(IfaceError::Execution(format!("Unable to open output file: {filename}")));
    };
    let _ = file.write_all(text.as_bytes());
    Ok(())
}

pub fn ifc_graph_dataflow(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function("No function selected"));
    }
    let filename = open_graph_file(args)?;
    with_current_function(dcp, |fd, glb| {
        if !fd.is_proc_started() {
            return Err(IfaceError::Execution("Syntax tree not calculated".to_string()));
        }
        if std::fs::File::create(&filename).is_err() {
            return Err(IfaceError::Execution(format!("Unable to open output file: {filename}")));
        }
        let mut text = String::new();
        dump_dataflow_graph(fd, &mut text, glb);
        write_graph_file(&filename, &text)
    })
}

pub fn ifc_graph_controlflow(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function("No function selected"));
    }
    let filename = open_graph_file(args)?;
    with_current_function(dcp, |fd, _glb| {
        let graph = fd.get_basic_blocks();
        if fd.block(graph).get_size() == 0 {
            return Err(IfaceError::Execution(
                "Basic block structure not calculated".to_string(),
            ));
        }
        if std::fs::File::create(&filename).is_err() {
            return Err(IfaceError::Execution(format!("Unable to open output file: {filename}")));
        }
        let mut text = String::new();
        let name = fd.get_name().to_string();
        dump_controlflow_graph(&name, fd, graph, &mut text);
        write_graph_file(&filename, &text)
    })
}

pub fn ifc_graph_dom(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    if dcp.fd.is_none() {
        return Err(no_function("No function selected"));
    }
    let filename = open_graph_file(args)?;
    with_current_function(dcp, |fd, _glb| {
        if !fd.is_proc_started() {
            return Err(IfaceError::Execution(
                "Basic block structure not calculated".to_string(),
            ));
        }
        if std::fs::File::create(&filename).is_err() {
            return Err(IfaceError::Execution(format!("Unable to open output file: {filename}")));
        }
        let mut text = String::new();
        let name = fd.get_name().to_string();
        let graph = fd.get_basic_blocks();
        dump_dom_graph(&name, fd, graph, &mut text);
        write_graph_file(&filename, &text)
    })
}

pub fn ifc_comment_instr(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    conf_mut(dcp, "Decompile action not loaded")?;
    let Some(sym) = dcp.fd else {
        return Err(no_function("No function selected"));
    };
    let glb = conf_mut(dcp, "Decompile action not loaded")?;
    let mut size: i32 = 0;
    let addr = read_machaddr(args, &mut size, glb)?;
    args.ws();
    let mut comment = Vec::new();
    let mut tok = args.get();
    while !args.eof() {
        if let Some(byte) = tok {
            comment.push(byte);
        }
        tok = args.get();
    }
    let comment = String::from_utf8_lossy(&comment).into_owned();
    let tp = glb.printlist[glb.print]
        .as_deref()
        .map(|printer| printer.get_instruction_comment())
        .unwrap_or(0);
    let funcaddr = with_function(glb, sym, |fd, _glb| Ok(fd.get_address().clone()))?;
    glb.commentdb
        .as_deref_mut()
        .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing comment database".to_string())))?
        .add_comment(tp, &funcaddr, &addr, &comment);
    Ok(())
}

pub fn ifc_print_actionstats(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let fileoptr = status.fileoptr.clone();
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "Image not loaded")?;
    let Some(action) = glb.allacts.get_current() else {
        return Err(IfaceError::Execution("No action set".to_string()));
    };
    let mut text = String::new();
    action.print_statistics(&mut text);
    out_write(&fileoptr, &text);
    Ok(())
}

pub fn ifc_reset_actionstats(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "Image not loaded")?;
    let Some(action) = glb.allacts.get_current() else {
        return Err(IfaceError::Execution("No action set".to_string()));
    };
    action.reset_stats();
    Ok(())
}

pub fn ifc_count_pcode(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    conf_mut(dcp, "Image not loaded")?;
    if dcp.fd.is_none() {
        return Err(no_function("No function selected"));
    }
    with_current_function(dcp, |fd, _glb| {
        let mut count: u32 = 0;
        let mut iter = fd.begin_op_alive();
        let enditer = fd.end_op_alive();
        while iter != enditer {
            count += 1;
            iter = iter.and_then(|op| fd.obank.next_in_list(op, crate::op::PcodeOp::INSERT_LIST));
        }
        out_write(&optr, &format!("Count - pcode = {count}\n"));
        Ok(())
    })
}

fn extrapop_text(expop: i32) -> String {
    if expop == ProtoModel::EXTRAPOP_UNKNOWN {
        "unknown".to_string()
    } else {
        expop.to_string()
    }
}

pub fn ifc_print_extrapop(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let mut name = String::new();
    args.ws().read_word_into(&mut name);
    let dcp = decomp_data(status);
    let fdsym = dcp.fd;
    let glb = conf_mut(dcp, "No load image present")?;
    if name.is_empty() {
        match fdsym {
            Some(sym) => with_function(glb, sym, |fd, _glb| {
                let mut text = String::new();
                for index in 0..fd.num_calls() {
                    let fc = fd.call_spec(fd.get_call_specs(index));
                    text.push_str(&format!("ExtraPop for {}(", fc.get_name()));
                    let opaddr = fd.op(fc.get_op()).get_addr().clone();
                    text.push_str(&address_text(&opaddr));
                    text.push(')');
                    text.push(' ');
                    text.push_str(&extrapop_text(fc.get_effective_extra_pop()));
                    text.push('(');
                    text.push_str(&extrapop_text(fc.get_extra_pop()));
                    text.push_str(")\n");
                }
                out_write(&optr, &text);
                Ok(())
            })?,
            None => {
                let model = glb
                    .defaultfp
                    .ok_or_else(|| IfaceError::Core(Error::Lowlevel("missing default prototype".to_string())))?;
                let expop = glb.proto_models.get(model).get_extra_pop();
                out_write(&optr, &format!("Default extra pop = {}\n", extrapop_text(expop)));
            }
        }
        return Ok(());
    }
    let scope = super::global_scope(glb)?;
    let Some(target) = symbol_table(glb)?.scope_query_function_by_name(scope, &name) else {
        return Err(IfaceError::Execution(format!("Unknown function: {name}")));
    };
    let (expop, target_name) = with_function(glb, target, |fd, _glb| {
        Ok((fd.get_func_proto().get_extra_pop(), fd.get_name().to_string()))
    })?;
    out_write(
        &optr,
        &format!("ExtraPop for function {name} is {}\n", extrapop_text(expop)),
    );
    if let Some(sym) = fdsym {
        with_function(glb, sym, |fd, _glb| {
            let mut text = String::new();
            for index in 0..fd.num_calls() {
                let fc = fd.call_spec(fd.get_call_specs(index));
                if fc.get_name() == target_name {
                    text.push_str("For this function, extrapop = ");
                    text.push_str(&extrapop_text(fc.get_effective_extra_pop()));
                    text.push('(');
                    text.push_str(&extrapop_text(fc.get_extra_pop()));
                    text.push_str(")\n");
                }
            }
            out_write(&optr, &text);
            Ok(())
        })?;
    }
    Ok(())
}

fn address_text(addr: &Address) -> String {
    let mut text = String::new();
    addr.print_raw(&mut text);
    text
}

pub fn current_function_name(status: &mut IfaceStatus) -> IfaceResult<String> {
    let dcp = decomp_data(status);
    let sym = dcp.fd.ok_or_else(|| no_function("No function selected"))?;
    let glb = conf_mut(dcp, "No function selected")?;
    function_name(glb, sym)
}
