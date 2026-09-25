use std::sync::Arc;

use regex::bytes::{Regex, RegexBuilder};

use crate::ifacedecomp::{decomp_data, mainloop, register_all_commands};
use crate::interface::{IfaceError, IfaceResult, IfaceStatus, OutStream, new_out_stream, out_write};
use crate::istream::{Basefield, read_i32};
use crate::sleigh_arch::get_sleigh_capability;
use crate::xml::{DocumentStorage, Element};

#[derive(Clone, Debug, Default)]
pub struct FunctionTestProperty {
    minimum_match: i32,
    maximum_match: i32,
    name: String,
    pattern: Vec<Regex>,
    patnum: u32,
    count: u32,
}

impl FunctionTestProperty {
    pub fn get_name(&self) -> String {
        self.name.clone()
    }

    pub fn start_test(&mut self) {
        self.count = 0;
        self.patnum = 0;
    }

    pub fn process_line(&mut self, line: &[u8]) {
        if self.pattern[self.patnum as usize].is_match(line) {
            self.patnum += 1;
            if self.patnum as usize >= self.pattern.len() {
                self.count += 1;
                self.patnum = 0;
            }
        } else if self.patnum > 0 {
            self.patnum = 0;
            if self.pattern[self.patnum as usize].is_match(line) {
                self.patnum += 1;
            }
        }
    }

    pub fn end_test(&self) -> bool {
        (self.count as i64) >= self.minimum_match as i64 && (self.count as i64) <= self.maximum_match as i64
    }

    fn ecmascript_to_rust_pattern(text: &str) -> String {
        let mut converted = String::with_capacity(text.len());
        let mut characters = text.chars();
        while let Some(character) = characters.next() {
            if character != '\\' {
                converted.push(character);
                continue;
            }
            match characters.next() {
                Some(escaped) if escaped.is_ascii_alphanumeric() => {
                    converted.push('\\');
                    converted.push(escaped);
                }
                Some(escaped) => converted.push_str(&regex::escape(&escaped.to_string())),
                None => converted.push('\\'),
            }
        }
        converted
    }

    fn compile_pattern(text: &str) -> IfaceResult<Regex> {
        RegexBuilder::new(&Self::ecmascript_to_rust_pattern(text))
            .unicode(false)
            .build()
            .map_err(|err| IfaceError::Parse(format!("Bad regular expression: {text}: {err}")))
    }

    pub fn restore_xml(&mut self, el: &Element) -> IfaceResult<()> {
        self.name = el.get_attribute_value("name")?.to_string();
        self.minimum_match = read_i32(el.get_attribute_value("min")?, Basefield::Dec, self.minimum_match);
        self.maximum_match = read_i32(el.get_attribute_value("max")?, Basefield::Dec, self.maximum_match);
        let line = el.get_content().as_bytes();
        let mut pos: Option<usize> = Some(0);
        while let Some(mut start) = pos {
            while start < line.len() && (line[start] == b' ' || line[start] == b'\t') {
                start += 1;
            }
            if start >= line.len() {
                break;
            }
            let nextpos = line[start..]
                .iter()
                .position(|byte| *byte == b'\n')
                .map(|index| index + start);
            let piece = match nextpos {
                None => &line[start..],
                Some(end) => &line[start..end],
            };
            let text = String::from_utf8_lossy(piece).into_owned();
            self.pattern.push(FunctionTestProperty::compile_pattern(&text)?);
            pos = nextpos.map(|end| end + 1);
        }
        Ok(())
    }
}

#[derive(Default)]
pub struct FunctionTestCollection {
    file_name: String,
    test_list: Vec<FunctionTestProperty>,
    commands: Vec<String>,
    num_tests_applied: i32,
    num_tests_succeeded: i32,
}

pub fn new_test_console(args: OutStream) -> IfaceStatus {
    let mut console = IfaceStatus::new_commands("> ", args, Vec::new());
    register_all_commands(&mut console);
    console
}

impl FunctionTestCollection {
    pub fn new() -> FunctionTestCollection {
        FunctionTestCollection::default()
    }

    pub fn get_tests_applied(&self) -> i32 {
        self.num_tests_applied
    }

    pub fn get_tests_succeeded(&self) -> i32 {
        self.num_tests_succeeded
    }

    pub fn num_commands(&self) -> i32 {
        self.commands.len() as i32
    }

    pub fn get_command(&self, index: i32) -> String {
        self.commands[index as usize].clone()
    }

    pub fn clear(&mut self, console: &mut IfaceStatus) {
        decomp_data(console).clear_architecture();
        self.commands.clear();
        self.test_list.clear();
        console.reset();
    }

    fn strip_newlines(reference: &str) -> String {
        let mut res = String::new();
        for character in reference.chars() {
            if character == '\r' {
                continue;
            }
            if character == '\n' {
                res.push(' ');
            } else {
                res.push(character);
            }
        }
        res
    }

    fn restore_xml_commands(&mut self, el: &Element) {
        for subel in el.get_children() {
            self.commands
                .push(FunctionTestCollection::strip_newlines(subel.get_content()));
        }
    }

    fn build_program(&mut self, store: &mut DocumentStorage, console: &mut IfaceStatus) -> IfaceResult<()> {
        let Some(capa) = get_sleigh_capability("xml") else {
            return Err(IfaceError::Execution("Missing XML architecture capability".to_string()));
        };
        let estream = console.optr.clone();
        let (glb, slot) = capa.build_with_slot("test", "", Some(estream))?;
        let dcp = decomp_data(console);
        dcp.conf = Some(glb);
        dcp.loader_slot = Some(slot);
        let glb = dcp.conf.as_deref_mut().expect("architecture was just built");
        let result = glb.init(store).and_then(|_| glb.read_loader_symbols());
        match result {
            Ok(()) => Ok(()),
            Err(err) => Err(IfaceError::Execution(format!(
                "Error during architecture initialization: {}",
                err.explain()
            ))),
        }
    }

    fn start_tests(&mut self) {
        for test in self.test_list.iter_mut() {
            test.start_test();
        }
    }

    fn pass_line_to_tests(&mut self, line: &[u8]) {
        for test in self.test_list.iter_mut() {
            test.process_line(line);
        }
    }

    fn evaluate_tests(&mut self, late_stream: &mut Vec<String>, optr: &OutStream) {
        for test in self.test_list.iter() {
            self.num_tests_applied += 1;
            if test.end_test() {
                out_write(optr, &format!("Success -- {}\n", test.get_name()));
                self.num_tests_succeeded += 1;
            } else {
                out_write(optr, &format!("FAIL -- {}\n", test.get_name()));
                late_stream.push(test.get_name());
            }
        }
    }

    pub fn load_test(&mut self, filename: &str, console: &mut IfaceStatus) -> IfaceResult<()> {
        self.file_name = filename.to_string();
        let mut doc_storage = DocumentStorage::new();
        let doc = doc_storage.open_document(filename)?;
        let el = doc.get_root().clone();
        if el.get_name() == "decompilertest" {
            self.restore_xml(&mut doc_storage, &el, console)
        } else if el.get_name() == "binaryimage" {
            self.restore_xml_old_form(&mut doc_storage, &el)
        } else {
            Err(IfaceError::Parse(format!(
                "Test file {filename} has unrecognized XML tag: {}",
                el.get_name()
            )))
        }
    }

    pub fn restore_xml(
        &mut self,
        store: &mut DocumentStorage,
        el: &Arc<Element>,
        console: &mut IfaceStatus,
    ) -> IfaceResult<()> {
        let mut saw_script = false;
        let mut saw_tests = false;
        let mut saw_program = false;
        for subel in el.get_children() {
            if subel.get_name() == "script" {
                saw_script = true;
                self.restore_xml_commands(subel);
            } else if subel.get_name() == "stringmatch" {
                saw_tests = true;
                let mut test = FunctionTestProperty::default();
                test.restore_xml(subel)?;
                self.test_list.push(test);
            } else if subel.get_name() == "binaryimage" {
                saw_program = true;
                store.register_tag(subel);
                self.build_program(store, console)?;
            } else {
                return Err(IfaceError::Parse(format!(
                    "Unknown tag in <decompilertest>: {}",
                    subel.get_name()
                )));
            }
        }
        if !saw_script {
            return Err(IfaceError::Parse(
                "Did not see <script> tag in <decompilertest>".to_string(),
            ));
        }
        if !saw_tests {
            return Err(IfaceError::Parse(
                "Did not see any <stringmatch> tags in <decompilertest>".to_string(),
            ));
        }
        if !saw_program {
            return Err(IfaceError::Parse(
                "No <binaryimage> tag in <decompilertest>".to_string(),
            ));
        }
        Ok(())
    }

    pub fn restore_xml_old_form(&mut self, _store: &mut DocumentStorage, _el: &Arc<Element>) -> IfaceResult<()> {
        Err(IfaceError::Parse("Old format test not supported".to_string()))
    }

    pub fn run_tests(&mut self, console: &mut IfaceStatus, late_stream: &mut Vec<String>) {
        let orig_stream = console.optr.clone();
        let orig_file = console.fileoptr.clone();
        self.num_tests_applied = 0;
        self.num_tests_succeeded = 0;
        let mid_buffer = new_out_stream();
        console.optr = mid_buffer.clone();
        let bulkout = new_out_stream();
        console.fileoptr = bulkout.clone();
        if let Some(input) = console.commands_mut() {
            input.commands = self.commands.clone();
        }
        mainloop(console);
        console.optr = orig_stream.clone();
        console.fileoptr = orig_file;
        if console.is_in_error() {
            out_write(
                &orig_stream,
                &format!("Error: Did not apply tests in {}\n", self.file_name),
            );
            let mid = mid_buffer.lock().expect("poisoned output stream lock").clone();
            out_write(&orig_stream, &format!("{mid}\n"));
            late_stream.push(format!("Execution failed for {}", self.file_name));
            return;
        }
        let result = bulkout.lock().expect("poisoned output stream lock").clone();
        if let Some(dump_path) = std::env::var_os("GHIDRA_TEST_OUTPUT") {
            use std::io::Write;
            if let Ok(mut dump) = std::fs::OpenOptions::new().create(true).append(true).open(dump_path) {
                let _ = write!(dump, "===\n{result}");
            }
        }
        if result.is_empty() {
            late_stream.push(format!("No output for {}", self.file_name));
            return;
        }
        self.start_tests();
        let bytes = result.as_bytes();
        let mut prevpos = 0usize;
        let mut pos = bytes.iter().position(|byte| *byte == b'\n');
        while let Some(found) = pos {
            self.pass_line_to_tests(&bytes[prevpos..found]);
            prevpos = found + 1;
            pos = bytes[prevpos..]
                .iter()
                .position(|byte| *byte == b'\n')
                .map(|index| index + prevpos);
        }
        if prevpos != bytes.len() {
            self.pass_line_to_tests(&bytes[prevpos..]);
        }
        self.evaluate_tests(late_stream, &orig_stream);
    }

    pub fn run_test_file(
        &mut self,
        filename: &str,
        console: &mut IfaceStatus,
        failures: &mut Vec<String>,
    ) -> Option<(i32, i32)> {
        let args = console.optr.clone();
        self.clear(console);
        let result = self.load_test(filename, console).map(|_| {
            self.run_tests(console, failures);
        });
        match result {
            Ok(()) => Some((self.get_tests_applied(), self.get_tests_succeeded())),
            Err(IfaceError::Parse(message)) => {
                let fs = format!("Error parsing {filename}: {message}");
                out_write(&args, &format!("{fs}\n"));
                failures.push(fs);
                None
            }
            Err(IfaceError::Execution(message)) => {
                let fs = format!("Error executing {filename}: {message}");
                out_write(&args, &format!("{fs}\n"));
                failures.push(fs);
                None
            }
            Err(err) => {
                let fs = format!("Error executing {filename}: {}", err.explain());
                out_write(&args, &format!("{fs}\n"));
                failures.push(fs);
                None
            }
        }
    }

    pub fn run_test_files(test_files: &[String], args: &OutStream) -> i32 {
        let mut total_tests_applied = 0;
        let mut total_tests_succeeded = 0;
        let mut failures: Vec<String> = Vec::new();
        let mut console = new_test_console(args.clone());
        console.set_error_is_done(true);
        let mut test_collection = FunctionTestCollection::new();
        for filename in test_files {
            if let Some((applied, succeeded)) = test_collection.run_test_file(filename, &mut console, &mut failures) {
                total_tests_applied += applied;
                total_tests_succeeded += succeeded;
            }
        }
        let mut text = String::from("\n");
        text.push_str(&format!("Total tests applied = {total_tests_applied}\n"));
        text.push_str(&format!("Total passing tests = {total_tests_succeeded}\n"));
        text.push('\n');
        if !failures.is_empty() {
            text.push_str("Failures: \n");
            for failure in failures.iter().take(10) {
                text.push_str(&format!("  {failure}\n"));
            }
        }
        out_write(args, &text);
        total_tests_applied - total_tests_succeeded
    }
}
