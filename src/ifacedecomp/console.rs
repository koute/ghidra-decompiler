use std::io::Write;
use std::path::Path;

use crate::interface::{CharSource, IStream, IfaceError, IfaceResult, IfaceStatus, out_write};
use crate::marshal::XmlEncode;
use crate::sleigh_arch::{add_global_language_directory, find_sleigh_capability, find_sleigh_capability_doc};
use crate::testfunction::FunctionTestCollection;
use crate::xml::DocumentStorage;

use super::{conf_mut, decomp_command, decomp_data};

thread_local! {
    static SAVEFILE: std::cell::RefCell<String> = const { std::cell::RefCell::new(String::new()) };
}

pub fn ifc_load_file(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    if dcp.conf.is_some() {
        return Err(IfaceError::Execution("Load image already present".to_string()));
    }
    let mut filename = String::new();
    let target;
    args.read_word_into(&mut filename);
    if !args.eof() {
        target = filename.clone();
        args.read_word_into(&mut filename);
    } else {
        target = "default".to_string();
    }
    let Some(capa) = find_sleigh_capability(&filename) else {
        return Err(IfaceError::Execution(format!(
            "Unable to recognize imagefile {filename}"
        )));
    };
    let (glb, slot) = capa.build_with_slot(&filename, &target, Some(optr.clone()))?;
    dcp.conf = Some(glb);
    dcp.loader_slot = Some(slot);
    let mut store = DocumentStorage::new();
    let glb = dcp.conf.as_deref_mut().expect("architecture was just built");
    if let Err(err) = glb.init(&mut store) {
        out_write(&optr, &format!("{}\n", err.explain()));
        out_write(&optr, "Could not create architecture\n");
        dcp.conf = None;
        dcp.loader_slot = None;
        return Ok(());
    }
    if capa.get_name() == "xml" {
        glb.read_loader_symbols()?;
    }
    let description = glb.get_description();
    out_write(&optr, &format!("{filename} successfully loaded: {description}\n"));
    Ok(())
}

pub fn ifc_addpath(args: &mut IStream, _status: &mut IfaceStatus) -> IfaceResult<()> {
    let mut newpath = String::new();
    args.read_word_into(&mut newpath);
    if newpath.is_empty() {
        return Err(IfaceError::Parse("Missing path name".to_string()));
    }
    add_global_language_directory(Path::new(&newpath))?;
    Ok(())
}

pub fn ifc_save(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    args.ws();
    if !args.eof() {
        let mut name = String::new();
        args.read_word_into(&mut name);
        SAVEFILE.with(|savefile| *savefile.borrow_mut() = name);
    }
    let savefile = SAVEFILE.with(|savefile| savefile.borrow().clone());
    if savefile.is_empty() {
        return Err(IfaceError::Parse("Missing savefile name".to_string()));
    }
    let Ok(mut file) = std::fs::File::create(&savefile) else {
        return Err(IfaceError::Execution(format!("Unable to open file: {savefile}")));
    };
    let dcp = decomp_data(status);
    let glb = conf_mut(dcp, "No load image present")?;
    let mut encoder = XmlEncode::new(true);
    let result = glb.encode(&mut encoder);
    let _ = file.write_all(encoder.as_str().as_bytes());
    result?;
    Ok(())
}

pub fn ifc_restore(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let mut name = String::new();
    args.read_word_into(&mut name);
    SAVEFILE.with(|savefile| *savefile.borrow_mut() = name);
    let savefile = SAVEFILE.with(|savefile| savefile.borrow().clone());
    if savefile.is_empty() {
        return Err(IfaceError::Parse("Missing file name".to_string()));
    }
    let mut store = DocumentStorage::new();
    let doc = store.open_document(&savefile)?;
    store.register_tag(doc.get_root());
    let dcp = decomp_data(status);
    dcp.clear_architecture();
    let Some(capa) = find_sleigh_capability_doc(&doc) else {
        return Err(IfaceError::Execution("Could not find savefile tag".to_string()));
    };
    let (glb, slot) = capa.build_with_slot("", "", Some(optr.clone()))?;
    dcp.conf = Some(glb);
    dcp.loader_slot = Some(slot);
    let glb = dcp.conf.as_deref_mut().expect("architecture was just built");
    if let Err(err) = glb.restore_xml(&mut store) {
        return Err(IfaceError::Execution(err.explain().to_string()));
    }
    let description = glb.get_description();
    out_write(&optr, &format!("{savefile} successfully loaded: {description}\n"));
    Ok(())
}

pub fn register_console_commands(status: &mut IfaceStatus) {
    status.register_com(decomp_command(ifc_load_file), &["load", "file"]);
    status.register_com(decomp_command(ifc_addpath), &["addpath"]);
    status.register_com(decomp_command(ifc_save), &["save"]);
    status.register_com(decomp_command(ifc_restore), &["restore"]);
}

pub fn ifc_load_test_file(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    if dcp.conf.is_some() {
        return Err(IfaceError::Execution("Load image already present".to_string()));
    }
    let mut filename = String::new();
    args.read_word_into(&mut filename);
    let mut collection = Box::new(FunctionTestCollection::new());
    let result = collection.load_test(&filename, status);
    let dcp = decomp_data(status);
    dcp.test_collection = Some(collection);
    result?;
    let glb = conf_mut(dcp, "No load image present")?;
    let description = glb.get_description();
    out_write(&optr, &format!("{filename} test successfully loaded: {description}\n"));
    Ok(())
}

pub fn ifc_list_test_commands(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let optr = status.optr.clone();
    let dcp = decomp_data(status);
    let Some(collection) = dcp.test_collection.as_ref() else {
        return Err(IfaceError::Execution("No test file is loaded".to_string()));
    };
    let mut text = String::new();
    for index in 0..collection.num_commands() {
        text.push_str(&format!(" {}: {}\n", index + 1, collection.get_command(index)));
    }
    out_write(&optr, &text);
    Ok(())
}

pub fn ifc_execute_test_command(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let dcp = decomp_data(status);
    let Some(collection) = dcp.test_collection.as_ref() else {
        return Err(IfaceError::Execution("No test file is loaded".to_string()));
    };
    let mut first: i32 = -1;
    let mut last: i32 = -1;
    args.ws().dec().read_i32(&mut first);
    first -= 1;
    if first < 0 || first > collection.num_commands() {
        return Err(IfaceError::Execution("Command index out of bounds".to_string()));
    }
    args.ws();
    if !args.eof() {
        let hyphen = args.ws().read_char();
        if hyphen != Some(b'-') {
            return Err(IfaceError::Execution("Missing hyphenated command range".to_string()));
        }
        args.ws().read_i32(&mut last);
        last -= 1;
        if last < 0 || last < first || last > collection.num_commands() {
            return Err(IfaceError::Execution("Command index out of bounds".to_string()));
        }
    } else {
        last = first;
    }
    let mut script = String::new();
    for index in first..=last {
        script.push_str(&collection.get_command(index));
        script.push('\n');
    }
    status.push_script(Some(CharSource::from_bytes(script.into_bytes())), "test> ")
}
