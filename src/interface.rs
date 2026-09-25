use std::any::Any;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt::Write as FmtWrite;
use std::io::{BufRead, BufReader, Read, Write};
use std::sync::{Arc, Mutex};

use crate::error::Error;
use crate::istream::{Basefield, IntegerExtraction, extract_i32, extract_i64, extract_u32, extract_u64};

pub type OutStream = Arc<Mutex<String>>;

pub fn new_out_stream() -> OutStream {
    Arc::new(Mutex::new(String::new()))
}

pub fn out_write(stream: &OutStream, text: &str) {
    stream.lock().expect("poisoned output stream lock").push_str(text);
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IfaceError {
    Parse(String),
    Execution(String),
    Generic(String),
    Core(Error),
}

impl IfaceError {
    pub fn explain(&self) -> &str {
        match self {
            IfaceError::Parse(message) | IfaceError::Execution(message) | IfaceError::Generic(message) => message,
            IfaceError::Core(err) => err.explain(),
        }
    }
}

impl From<Error> for IfaceError {
    fn from(err: Error) -> IfaceError {
        IfaceError::Core(err)
    }
}

pub type IfaceResult<T> = std::result::Result<T, IfaceError>;

fn is_stream_space(byte: u8) -> bool {
    matches!(byte, b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r')
}

#[derive(Clone, Debug)]
pub struct IStream {
    data: Vec<u8>,
    pos: usize,
    eofbit: bool,
    failbit: bool,
    basefield: Basefield,
}

impl IStream {
    pub fn new(text: &str) -> IStream {
        IStream::from_bytes(text.as_bytes().to_vec())
    }

    pub fn from_bytes(data: Vec<u8>) -> IStream {
        IStream {
            data,
            pos: 0,
            eofbit: false,
            failbit: false,
            basefield: Basefield::Dec,
        }
    }

    pub fn good(&self) -> bool {
        !self.eofbit && !self.failbit
    }

    pub fn eof(&self) -> bool {
        self.eofbit
    }

    pub fn fail(&self) -> bool {
        self.failbit
    }

    pub fn position(&self) -> usize {
        self.pos
    }

    pub fn remaining(&self) -> &[u8] {
        &self.data[self.pos..]
    }

    pub fn hex(&mut self) -> &mut IStream {
        self.basefield = Basefield::Hex;
        self
    }

    pub fn dec(&mut self) -> &mut IStream {
        self.basefield = Basefield::Dec;
        self
    }

    pub fn unset_basefield(&mut self) -> &mut IStream {
        self.basefield = Basefield::Auto;
        self
    }

    fn sentry(&mut self, noskipws: bool) -> bool {
        if !self.good() {
            self.failbit = true;
            return false;
        }
        if !noskipws {
            while self.pos < self.data.len() && is_stream_space(self.data[self.pos]) {
                self.pos += 1;
            }
            if self.pos == self.data.len() {
                self.eofbit = true;
                self.failbit = true;
                return false;
            }
        }
        true
    }

    pub fn ws(&mut self) -> &mut IStream {
        if !self.sentry(true) {
            return self;
        }
        while self.pos < self.data.len() && is_stream_space(self.data[self.pos]) {
            self.pos += 1;
        }
        if self.pos == self.data.len() {
            self.eofbit = true;
        }
        self
    }

    pub fn read_word(&mut self) -> Option<String> {
        if !self.sentry(false) {
            return None;
        }
        let start = self.pos;
        while self.pos < self.data.len() && !is_stream_space(self.data[self.pos]) {
            self.pos += 1;
        }
        if self.pos == self.data.len() {
            self.eofbit = true;
        }
        Some(String::from_utf8_lossy(&self.data[start..self.pos]).into_owned())
    }

    pub fn read_word_into(&mut self, word: &mut String) -> &mut IStream {
        if let Some(value) = self.read_word() {
            *word = value;
        }
        self
    }

    pub fn get(&mut self) -> Option<u8> {
        if !self.sentry(true) {
            return None;
        }
        if self.pos == self.data.len() {
            self.eofbit = true;
            self.failbit = true;
            return None;
        }
        let byte = self.data[self.pos];
        self.pos += 1;
        Some(byte)
    }

    pub fn read_char(&mut self) -> Option<u8> {
        if !self.sentry(false) {
            return None;
        }
        let byte = self.data[self.pos];
        self.pos += 1;
        Some(byte)
    }

    pub fn getline_into(&mut self, line: &mut String, delim: u8) -> &mut IStream {
        if !self.sentry(true) {
            return self;
        }
        let start = self.pos;
        let mut found = false;
        while self.pos < self.data.len() {
            if self.data[self.pos] == delim {
                found = true;
                break;
            }
            self.pos += 1;
        }
        *line = String::from_utf8_lossy(&self.data[start..self.pos]).into_owned();
        if found {
            self.pos += 1;
        } else {
            self.eofbit = true;
            if self.pos == start {
                self.failbit = true;
            }
        }
        self
    }

    pub fn peek(&mut self) -> Option<u8> {
        if !self.sentry(true) {
            return None;
        }
        if self.pos == self.data.len() {
            self.eofbit = true;
            return None;
        }
        Some(self.data[self.pos])
    }

    fn extract_number(
        &mut self,
        extractor: fn(&str, Basefield) -> Option<IntegerExtraction>,
    ) -> Option<IntegerExtraction> {
        if !self.sentry(false) {
            return None;
        }
        let text = String::from_utf8_lossy(&self.data[self.pos..]).into_owned();
        let extraction = extractor(&text, self.basefield)?;
        self.pos += extraction.consumed;
        if self.pos >= self.data.len() {
            self.pos = self.data.len();
            self.eofbit = true;
        }
        if extraction.failed {
            self.failbit = true;
        }
        Some(extraction)
    }

    pub fn read_u64(&mut self, value: &mut u64) -> &mut IStream {
        if let Some(extraction) = self.extract_number(extract_u64) {
            *value = extraction.value;
        }
        self
    }

    pub fn read_i64(&mut self, value: &mut i64) -> &mut IStream {
        if let Some(extraction) = self.extract_number(extract_i64) {
            *value = extraction.value as i64;
        }
        self
    }

    pub fn read_u32(&mut self, value: &mut u32) -> &mut IStream {
        if let Some(extraction) = self.extract_number(extract_u32) {
            *value = extraction.value as u32;
        }
        self
    }

    pub fn read_i32(&mut self, value: &mut i32) -> &mut IStream {
        if let Some(extraction) = self.extract_number(extract_i32) {
            *value = extraction.value as u32 as i32;
        }
        self
    }
}

impl Read for IStream {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let available = self.fill_buf()?;
        let count = available.len().min(buf.len());
        buf[..count].copy_from_slice(&available[..count]);
        self.consume(count);
        Ok(count)
    }
}

impl BufRead for IStream {
    fn fill_buf(&mut self) -> std::io::Result<&[u8]> {
        if self.pos >= self.data.len() {
            self.eofbit = true;
        }
        Ok(&self.data[self.pos..])
    }

    fn consume(&mut self, amt: usize) {
        self.pos = (self.pos + amt).min(self.data.len());
    }
}

#[derive(Clone, Debug, Default)]
pub struct IfaceCommandBase {
    pub com: Vec<String>,
}

pub trait IfaceCommand {
    fn base(&self) -> &IfaceCommandBase;

    fn base_mut(&mut self) -> &mut IfaceCommandBase;

    fn execute(&mut self, args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()>;

    fn get_module(&self) -> String;

    fn create_data(&self) -> Option<Box<dyn Any>>;

    fn add_word(&mut self, temp: &str) {
        self.base_mut().com.push(temp.to_string());
    }

    fn remove_word(&mut self) {
        self.base_mut().com.pop();
    }

    fn get_command_word(&self, index: i32) -> &str {
        &self.base().com[index as usize]
    }

    fn add_words(&mut self, wordlist: &[String]) {
        self.base_mut().com.extend(wordlist.iter().cloned());
    }

    fn num_words(&self) -> i32 {
        self.base().com.len() as i32
    }

    fn command_string(&self, res: &mut String) {
        IfaceStatus::words_to_string(res, &self.base().com);
    }

    fn compare(&self, op2: &dyn IfaceCommand) -> i32 {
        compare_word_lists(
            &self
                .base()
                .com
                .iter()
                .map(|word| word.as_bytes().to_vec())
                .collect::<Vec<_>>(),
            &op2.base()
                .com
                .iter()
                .map(|word| word.as_bytes().to_vec())
                .collect::<Vec<_>>(),
        )
    }
}

fn compare_word_lists(first: &[Vec<u8>], second: &[Vec<u8>]) -> i32 {
    let mut index = 0;
    loop {
        if index == first.len() {
            if index == second.len() {
                return 0;
            }
            return -1;
        }
        if index == second.len() {
            return 1;
        }
        match first[index].cmp(&second[index]) {
            Ordering::Less => return -1,
            Ordering::Greater => return 1,
            Ordering::Equal => {}
        }
        index += 1;
    }
}

pub type CommandFunction = fn(&mut IStream, &mut IfaceStatus) -> IfaceResult<()>;

pub type DataFactory = fn() -> Box<dyn Any>;

pub struct FunctionCommand {
    base: IfaceCommandBase,
    module: &'static str,
    run: CommandFunction,
    factory: Option<DataFactory>,
}

impl FunctionCommand {
    pub fn new(module: &'static str, run: CommandFunction, factory: Option<DataFactory>) -> FunctionCommand {
        FunctionCommand {
            base: IfaceCommandBase::default(),
            module,
            run,
            factory,
        }
    }
}

impl IfaceCommand for FunctionCommand {
    fn base(&self) -> &IfaceCommandBase {
        &self.base
    }

    fn base_mut(&mut self) -> &mut IfaceCommandBase {
        &mut self.base
    }

    fn execute(&mut self, args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
        (self.run)(args, status)
    }

    fn get_module(&self) -> String {
        self.module.to_string()
    }

    fn create_data(&self) -> Option<Box<dyn Any>> {
        self.factory.map(|factory| factory())
    }
}

pub fn base_command(run: CommandFunction) -> Box<dyn IfaceCommand> {
    Box::new(FunctionCommand::new("base", run, None))
}

pub struct CharSource {
    reader: Box<dyn BufRead>,
    eof: bool,
}

impl CharSource {
    pub fn new(reader: Box<dyn BufRead>) -> CharSource {
        CharSource { reader, eof: false }
    }

    pub fn from_bytes(data: Vec<u8>) -> CharSource {
        CharSource::new(Box::new(std::io::Cursor::new(data)))
    }

    pub fn get(&mut self) -> Option<u8> {
        if self.eof {
            return None;
        }
        let byte = match self.reader.fill_buf() {
            Ok(buffer) if !buffer.is_empty() => Some(buffer[0]),
            _ => None,
        };
        match byte {
            Some(value) => {
                self.reader.consume(1);
                Some(value)
            }
            None => {
                self.eof = true;
                None
            }
        }
    }

    pub fn eof(&self) -> bool {
        self.eof
    }
}

pub struct TermInput {
    sptr: CharSource,
    inputstack: Vec<CharSource>,
    pending_echo: Vec<u8>,
}

pub struct CommandsInput {
    pub commands: Vec<String>,
    pub pos: usize,
}

pub enum IfaceInput {
    Term(TermInput),
    Commands(CommandsInput),
}

pub struct IfaceStatus {
    promptstack: Vec<String>,
    flagstack: Vec<u32>,
    prompt: String,
    maxhistory: i32,
    curhistory: i32,
    history: Vec<String>,
    sorted: bool,
    errorisdone: bool,
    pub inerror: bool,
    comlist: Vec<Option<Box<dyn IfaceCommand>>>,
    datamap: BTreeMap<String, Option<Box<dyn Any>>>,
    pub done: bool,
    pub optr: OutStream,
    pub fileoptr: OutStream,
    input: IfaceInput,
    sinks: Vec<(OutStream, Box<dyn Write>)>,
}

impl IfaceStatus {
    pub fn new(prmpt: &str, os: OutStream, input: IfaceInput, mxhist: i32) -> IfaceStatus {
        IfaceStatus {
            promptstack: Vec::new(),
            flagstack: Vec::new(),
            prompt: prmpt.to_string(),
            maxhistory: mxhist,
            curhistory: 0,
            history: Vec::new(),
            sorted: false,
            errorisdone: false,
            inerror: false,
            comlist: Vec::new(),
            datamap: BTreeMap::new(),
            done: false,
            fileoptr: os.clone(),
            optr: os,
            input,
            sinks: Vec::new(),
        }
    }

    pub fn new_term(prmpt: &str, is: Box<dyn BufRead>, os: OutStream) -> IfaceStatus {
        IfaceStatus::new(
            prmpt,
            os,
            IfaceInput::Term(TermInput {
                sptr: CharSource::new(is),
                inputstack: Vec::new(),
                pending_echo: Vec::new(),
            }),
            10,
        )
    }

    pub fn new_commands(prmpt: &str, os: OutStream, comms: Vec<String>) -> IfaceStatus {
        IfaceStatus::new(
            prmpt,
            os,
            IfaceInput::Commands(CommandsInput {
                commands: comms,
                pos: 0,
            }),
            10,
        )
    }

    pub fn attach_sink(&mut self, stream: &OutStream, sink: Box<dyn Write>) {
        self.sinks.push((stream.clone(), sink));
    }

    pub fn flush_stream(&mut self, stream: &OutStream) {
        for (buffer, sink) in self.sinks.iter_mut() {
            if Arc::ptr_eq(buffer, stream) {
                let text = std::mem::take(&mut *buffer.lock().expect("poisoned output stream lock"));
                let _ = sink.write_all(text.as_bytes());
                let _ = sink.flush();
            }
        }
    }

    pub fn flush_all(&mut self) {
        for (buffer, sink) in self.sinks.iter_mut() {
            let text = std::mem::take(&mut *buffer.lock().expect("poisoned output stream lock"));
            let _ = sink.write_all(text.as_bytes());
            let _ = sink.flush();
        }
    }

    fn close_sink(&mut self, stream: &OutStream) {
        self.flush_stream(stream);
        self.sinks.retain(|(buffer, _)| !Arc::ptr_eq(buffer, stream));
    }

    pub fn commands_mut(&mut self) -> Option<&mut CommandsInput> {
        match &mut self.input {
            IfaceInput::Commands(input) => Some(input),
            IfaceInput::Term(_) => None,
        }
    }

    pub fn set_error_is_done(&mut self, val: bool) {
        self.errorisdone = val;
    }

    pub fn push_script_file(&mut self, filename: &str, newprompt: &str) -> IfaceResult<()> {
        let Ok(file) = std::fs::File::open(filename) else {
            return Err(IfaceError::Parse(format!("Unable to open script file: {filename}")));
        };
        self.push_script(Some(CharSource::new(Box::new(BufReader::new(file)))), newprompt)
    }

    pub fn push_script(&mut self, iptr: Option<CharSource>, newprompt: &str) -> IfaceResult<()> {
        match &mut self.input {
            IfaceInput::Term(term) => {
                if let Some(source) = iptr {
                    let previous = std::mem::replace(&mut term.sptr, source);
                    term.inputstack.push(previous);
                }
                self.push_script_base(newprompt);
                Ok(())
            }
            IfaceInput::Commands(_) => {
                if iptr.is_some() {
                    return Err(IfaceError::Execution(
                        "Unable to read script from stream on this interface".to_string(),
                    ));
                }
                self.push_script_base(newprompt);
                Ok(())
            }
        }
    }

    fn push_script_base(&mut self, newprompt: &str) {
        self.promptstack.push(self.prompt.clone());
        let mut flags = 0u32;
        if self.errorisdone {
            flags |= 1;
        }
        self.flagstack.push(flags);
        self.errorisdone = true;
        self.prompt = newprompt.to_string();
    }

    pub fn pop_script(&mut self) {
        if let IfaceInput::Term(term) = &mut self.input
            && let Some(previous) = term.inputstack.pop()
        {
            term.sptr = previous;
        }
        self.pop_script_base();
    }

    fn pop_script_base(&mut self) {
        if let Some(prompt) = self.promptstack.pop() {
            self.prompt = prompt;
        }
        let flags = self.flagstack.pop().unwrap_or(0);
        self.errorisdone = (flags & 1) != 0;
        self.inerror = false;
    }

    pub fn reset(&mut self) {
        match &mut self.input {
            IfaceInput::Commands(input) => {
                input.pos = 0;
                self.inerror = false;
                self.done = false;
            }
            IfaceInput::Term(_) => {
                while !self.promptstack.is_empty() {
                    self.pop_script();
                }
                self.errorisdone = false;
                self.done = false;
            }
        }
    }

    pub fn get_num_input_stream_size(&self) -> i32 {
        self.promptstack.len() as i32
    }

    pub fn write_prompt(&mut self) {
        out_write(&self.optr, &self.prompt);
    }

    pub fn register_com(&mut self, mut fptr: Box<dyn IfaceCommand>, words: &[&str]) {
        for word in words {
            fptr.add_word(word);
        }
        let nm = fptr.get_module();
        self.datamap.entry(nm).or_insert_with(|| fptr.create_data());
        self.comlist.push(Some(fptr));
        self.sorted = false;
    }

    pub fn get_data(&self, nm: &str) -> Option<&dyn Any> {
        self.datamap.get(nm).and_then(|data| data.as_deref())
    }

    pub fn get_data_mut(&mut self, nm: &str) -> Option<&mut (dyn Any + 'static)> {
        match self.datamap.get_mut(nm) {
            Some(Some(data)) => Some(data.as_mut()),
            _ => None,
        }
    }

    fn command(&self, index: usize) -> &dyn IfaceCommand {
        self.comlist[index]
            .as_deref()
            .expect("command is taken out of the command list")
    }

    fn save_history(&mut self, line: &str) {
        if (self.history.len() as i32) < self.maxhistory {
            self.history.push(line.to_string());
        } else {
            self.history[self.curhistory as usize] = line.to_string();
        }
        self.curhistory += 1;
        if self.curhistory == self.maxhistory {
            self.curhistory = 0;
        }
    }

    pub fn get_history(&self, line: &mut String, index: i32) {
        if index >= self.history.len() as i32 {
            return;
        }
        let mut slot = self.curhistory - 1 - index;
        if slot < 0 {
            slot += self.maxhistory;
        }
        *line = self.history[slot as usize].clone();
    }

    pub fn get_history_size(&self) -> i32 {
        self.history.len() as i32
    }

    pub fn is_stream_finished(&self) -> bool {
        match &self.input {
            IfaceInput::Term(term) => {
                if self.done || self.inerror {
                    return true;
                }
                term.sptr.eof()
            }
            IfaceInput::Commands(input) => input.pos == input.commands.len(),
        }
    }

    pub fn is_in_error(&self) -> bool {
        self.inerror
    }

    pub fn evaluate_error(&mut self) {
        if self.errorisdone {
            out_write(&self.optr, "Aborting process\n");
            self.inerror = true;
            self.done = true;
            return;
        }
        if self.get_num_input_stream_size() != 0 {
            let message = format!("Aborting {}\n", self.prompt);
            out_write(&self.optr, &message);
            self.inerror = true;
            return;
        }
        self.inerror = false;
    }

    pub fn words_to_string(res: &mut String, list: &[String]) {
        res.clear();
        for (index, word) in list.iter().enumerate() {
            if index != 0 {
                res.push(' ');
            }
            res.push_str(word);
        }
    }

    fn sort_commands(&mut self) {
        let mut list: Vec<Box<dyn IfaceCommand>> = self
            .comlist
            .drain(..)
            .map(|command| command.expect("command is taken out of the command list"))
            .collect();
        list.sort_by(|first, second| first.compare(second.as_ref()).cmp(&0));
        self.comlist = list.into_iter().map(Some).collect();
    }

    pub fn run_command(&mut self) -> IfaceResult<bool> {
        if !self.sorted {
            self.sort_commands();
            self.sorted = true;
        }
        let line = self.read_line();
        if line.is_empty() {
            return Ok(false);
        }
        self.save_history(&line);
        let mut fullcommand = Vec::new();
        let mut first = 0usize;
        let mut last = self.comlist.len();
        let mut is = IStream::new(&line);
        let matched = self.expand_com(&mut fullcommand, &mut is, &mut first, &mut last);
        if matched == 0 {
            out_write(&self.optr, "ERROR: Invalid command\n");
            return Ok(false);
        } else if fullcommand.is_empty() {
            return Ok(false);
        } else if matched > 1 {
            if self.command(first).num_words() != fullcommand.len() as i32 {
                out_write(&self.optr, "ERROR: Incomplete command\n");
                return Ok(false);
            }
        } else if matched < 0 {
            out_write(&self.optr, "ERROR: Incomplete command\n");
        }
        let mut command = self.comlist[first]
            .take()
            .expect("command is taken out of the command list");
        let result = command.execute(&mut is, self);
        self.comlist[first] = Some(command);
        result.map(|_| true)
    }

    fn restrict_com(&self, first: &mut usize, last: &mut usize, input: &[String]) {
        let mut dummy: Vec<Vec<u8>> = input.iter().map(|word| word.as_bytes().to_vec()).collect();
        let compare_at = |index: usize, dummy: &[Vec<u8>]| -> i32 {
            let words: Vec<Vec<u8>> = self
                .command(index)
                .base()
                .com
                .iter()
                .map(|word| word.as_bytes().to_vec())
                .collect();
            compare_word_lists(&words, dummy)
        };
        let mut low = *first;
        let mut high = *last;
        while low < high {
            let mid = low + (high - low) / 2;
            if compare_at(mid, &dummy) < 0 {
                low = mid + 1;
            } else {
                high = mid;
            }
        }
        let newfirst = low;
        let mut temp = dummy.pop().unwrap_or_default();
        if let Some(lastbyte) = temp.last_mut() {
            *lastbyte = lastbyte.wrapping_add(1);
        }
        dummy.push(temp);
        let mut low = *first;
        let mut high = *last;
        while low < high {
            let mid = low + (high - low) / 2;
            if compare_word_lists(&dummy, &{
                self.command(mid)
                    .base()
                    .com
                    .iter()
                    .map(|word| word.as_bytes().to_vec())
                    .collect::<Vec<_>>()
            }) < 0
            {
                high = mid;
            } else {
                low = mid + 1;
            }
        }
        *first = newfirst;
        *last = low;
    }

    fn maxmatch(res: &mut String, op1: &str, op2: &str) -> bool {
        let first = op1.as_bytes();
        let second = op2.as_bytes();
        let len = first.len().min(second.len());
        let mut common = Vec::new();
        let mut complete = true;
        for index in 0..len {
            if first[index] == second[index] {
                common.push(first[index]);
            } else {
                complete = false;
                break;
            }
        }
        *res = String::from_utf8_lossy(&common).into_owned();
        complete
    }

    pub fn expand_com(&self, expand: &mut Vec<String>, args: &mut IStream, first: &mut usize, last: &mut usize) -> i32 {
        expand.clear();
        let mut res = true;
        if *first == *last {
            return 0;
        }
        let mut tok = String::new();
        let mut pos: i32 = 0;
        loop {
            args.ws();
            if *first == *last - 1 {
                if args.eof() {
                    let command = self.command(*first);
                    while pos < command.num_words() {
                        expand.push(command.get_command_word(pos).to_string());
                        pos += 1;
                    }
                }
                if self.command(*first).num_words() == pos {
                    return 1;
                }
            }
            if !res {
                if !args.eof() {
                    return (*last - *first) as i32;
                }
                return *first as i32 - *last as i32;
            }
            if args.eof() {
                if expand.is_empty() {
                    return *first as i32 - *last as i32;
                }
                return (*last - *first) as i32;
            }
            args.read_word_into(&mut tok);
            expand.push(tok.clone());
            self.restrict_com(first, last, expand);
            if *first == *last {
                return 0;
            }
            let firstword = self.command(*first).get_command_word(pos).to_string();
            let lastword = self.command(*last - 1).get_command_word(pos).to_string();
            res = IfaceStatus::maxmatch(&mut tok, &firstword, &lastword);
            if let Some(back) = expand.last_mut() {
                *back = tok.clone();
            }
            pos += 1;
        }
    }

    fn echo_byte(&mut self, byte: u8) {
        let IfaceInput::Term(term) = &mut self.input else {
            return;
        };
        term.pending_echo.push(byte);
        match std::str::from_utf8(&term.pending_echo) {
            Ok(text) => {
                self.optr.lock().expect("poisoned output stream lock").push_str(text);
                term.pending_echo.clear();
            }
            Err(err) => {
                if err.error_len().is_some() {
                    let text = String::from_utf8_lossy(&term.pending_echo).into_owned();
                    self.optr.lock().expect("poisoned output stream lock").push_str(&text);
                    term.pending_echo.clear();
                }
            }
        }
    }

    fn read_char(&mut self) -> Option<u8> {
        match &mut self.input {
            IfaceInput::Term(term) => term.sptr.get(),
            IfaceInput::Commands(_) => None,
        }
    }

    fn source_eof(&self) -> bool {
        match &self.input {
            IfaceInput::Term(term) => term.sptr.eof(),
            IfaceInput::Commands(_) => true,
        }
    }

    fn do_completion(&mut self, line: &mut Vec<u8>, cursor: i32) -> i32 {
        let mut fullcommand = Vec::new();
        let mut args = IStream::from_bytes(line.clone());
        let mut first = 0usize;
        let mut last = self.comlist.len();
        let mut matched = self.expand_com(&mut fullcommand, &mut args, &mut first, &mut last);
        if matched == 0 {
            out_write(&self.optr, "\nInvalid command\n");
            return cursor;
        }
        let oldsize = line.len();
        let mut joined = String::new();
        IfaceStatus::words_to_string(&mut joined, &fullcommand);
        *line = joined.into_bytes();
        if matched < 0 {
            matched = -matched;
        } else {
            line.push(b' ');
        }
        let mut tok = String::new();
        if !args.eof() {
            args.read_word_into(&mut tok);
            args.ws();
            line.extend_from_slice(tok.as_bytes());
        }
        while !args.eof() {
            line.push(b' ');
            args.read_word_into(&mut tok);
            args.ws();
            line.extend_from_slice(tok.as_bytes());
        }
        if oldsize < line.len() {
            return line.len() as i32;
        }
        if matched > 1 {
            out_write(&self.optr, "\n");
            for index in first..last {
                let mut complete = String::new();
                self.command(index).command_string(&mut complete);
                let text = format!("{complete}\n");
                out_write(&self.optr, &text);
            }
        } else {
            out_write(&self.optr, "\nCommand is complete\n");
        }
        line.len() as i32
    }

    fn read_line(&mut self) -> String {
        if let IfaceInput::Commands(input) = &mut self.input {
            if input.pos >= input.commands.len() {
                return String::new();
            }
            let line = input.commands[input.pos].clone();
            input.pos += 1;
            return line;
        }
        let mut line: Vec<u8> = Vec::new();
        let mut cursor: i32 = 0;
        let mut hist: i32 = 0;
        let mut saveline: Vec<u8> = Vec::new();
        loop {
            let mut onecharecho = false;
            let mut history_up = false;
            let mut history_down = false;
            let lastlen = line.len() as i32;
            let mut val = self.read_char().unwrap_or(0xff);
            if self.source_eof() {
                val = b'\n';
            }
            match val {
                0x01 => cursor = 0,
                0x02 => {
                    if cursor > 0 {
                        cursor -= 1;
                    }
                }
                0x03 => {
                    line.clear();
                    cursor = 0;
                    val = 0x0a;
                    onecharecho = true;
                }
                0x04 => {
                    if (cursor as usize) < line.len() {
                        line.remove(cursor as usize);
                    }
                }
                0x05 => cursor = line.len() as i32,
                0x06 => {
                    if (cursor as usize) < line.len() {
                        cursor += 1;
                    }
                }
                0x07 => {}
                0x09 => cursor = self.do_completion(&mut line, cursor),
                0x0a | 0x0d => {
                    cursor = line.len() as i32;
                    onecharecho = true;
                }
                0x0b => line.truncate(cursor as usize),
                0x0c => {}
                0x0e => history_down = true,
                0x10 => history_up = true,
                0x12 => {}
                0x15 => {
                    line.drain(0..cursor as usize);
                    cursor = 0;
                }
                0x1b => {
                    let high = self.read_char().map(|byte| byte as i32).unwrap_or(-1);
                    let low = self.read_char().map(|byte| byte as i32).unwrap_or(-1);
                    let escval = (high << 8).wrapping_add(low);
                    match escval {
                        0x5b41 => history_up = true,
                        0x5b42 => history_down = true,
                        0x5b43 if (cursor as usize) < line.len() => {
                            cursor += 1;
                        }
                        0x5b44 if cursor > 0 => {
                            cursor -= 1;
                        }
                        _ => {}
                    }
                }
                0x08 | 0x7f => {
                    if cursor != 0 {
                        cursor -= 1;
                        line.remove(cursor as usize);
                    }
                }
                _ => {
                    line.insert(cursor as usize, val);
                    cursor += 1;
                    if cursor as usize == line.len() {
                        onecharecho = true;
                    }
                }
            }
            if history_down {
                if hist > 0 {
                    hist -= 1;
                    if hist > 0 {
                        let mut text = String::from_utf8_lossy(&line).into_owned();
                        self.get_history(&mut text, hist - 1);
                        line = text.into_bytes();
                    } else {
                        line = saveline.clone();
                    }
                    cursor = line.len() as i32;
                }
            } else if history_up && hist < self.get_history_size() {
                hist += 1;
                if hist == 1 {
                    saveline = line.clone();
                }
                let mut text = String::from_utf8_lossy(&line).into_owned();
                self.get_history(&mut text, hist - 1);
                line = text.into_bytes();
                cursor = line.len() as i32;
            }
            if onecharecho {
                self.echo_byte(val);
            } else {
                out_write(&self.optr, "\r");
                self.write_prompt();
                let text = String::from_utf8_lossy(&line).into_owned();
                out_write(&self.optr, &text);
                let mut index = line.len() as i32;
                while index < lastlen {
                    out_write(&self.optr, " ");
                    index += 1;
                }
                let mut back = index - cursor;
                while back > 0 {
                    out_write(&self.optr, "\x08");
                    back -= 1;
                }
            }
            if val == b'\n' {
                break;
            }
        }
        String::from_utf8_lossy(&line).into_owned()
    }
}

impl Drop for IfaceStatus {
    fn drop(&mut self) {
        self.flush_all();
    }
}

pub fn ifc_quit(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    if !args.eof() {
        return Err(IfaceError::Parse("Too many parameters to quit".to_string()));
    }
    status.done = true;
    Ok(())
}

pub fn ifc_history(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let mut num: i32 = 0;
    if !args.eof() {
        args.read_i32(&mut num).ws();
        if !args.eof() {
            return Err(IfaceError::Parse("Too many parameters to history".to_string()));
        }
    } else {
        num = 10;
    }
    if num > status.get_history_size() {
        num = status.get_history_size();
    }
    let mut index = num - 1;
    while index >= 0 {
        let mut historyline = String::new();
        status.get_history(&mut historyline, index);
        let mut text = String::new();
        let _ = writeln!(text, "{historyline}");
        out_write(&status.optr, &text);
        index -= 1;
    }
    Ok(())
}

fn open_output_file(args: &mut IStream, status: &mut IfaceStatus, append: bool) -> IfaceResult<()> {
    if !Arc::ptr_eq(&status.optr, &status.fileoptr) {
        return Err(IfaceError::Execution("Output file already opened".to_string()));
    }
    let mut filename = String::new();
    args.read_word_into(&mut filename);
    if filename.is_empty() {
        return Err(IfaceError::Parse("No filename specified".to_string()));
    }
    let file = std::fs::OpenOptions::new()
        .write(true)
        .create(true)
        .append(append)
        .truncate(!append)
        .open(&filename);
    let Ok(file) = file else {
        return Err(IfaceError::Execution(format!("Unable to open file: {filename}")));
    };
    let stream = new_out_stream();
    status.attach_sink(&stream, Box::new(file));
    status.fileoptr = stream;
    Ok(())
}

pub fn ifc_openfile(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    open_output_file(args, status, false)
}

pub fn ifc_openfile_append(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    open_output_file(args, status, true)
}

pub fn ifc_closefile(_args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    if Arc::ptr_eq(&status.optr, &status.fileoptr) {
        return Err(IfaceError::Execution("No file open".to_string()));
    }
    let stream = status.fileoptr.clone();
    status.close_sink(&stream);
    status.fileoptr = status.optr.clone();
    Ok(())
}

pub fn ifc_echo(args: &mut IStream, status: &mut IfaceStatus) -> IfaceResult<()> {
    let mut bytes = Vec::new();
    while let Some(byte) = args.get() {
        bytes.push(byte);
    }
    let mut text = String::from_utf8_lossy(&bytes).into_owned();
    text.push('\n');
    out_write(&status.fileoptr, &text);
    Ok(())
}
