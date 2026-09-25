mod tables;

use std::collections::BTreeMap;
use std::io::BufRead;

use crate::address::Address;
use crate::architecture::Architecture;
use crate::error::{Error, Result};
use crate::fspec::{ModelId, PrototypePieces};
use crate::istream::{Basefield, extract_i32, extract_i64, extract_u32};
use crate::types::{Datatype, TypeBitField, TypeFactory, TypeField, TypeId, TypeMetatype};

use tables::{
    YYCHECK, YYDEFACT, YYDEFGOTO, YYFINAL, YYLAST, YYMAXUTOK, YYNTOKENS, YYPACT, YYPACT_NINF, YYPGOTO, YYR1, YYR2,
    YYTABLE, YYTABLE_NINF, YYTRANSLATE,
};

pub const TOKEN_DOTDOTDOT: i32 = 258;
pub const TOKEN_BADTOKEN: i32 = 259;
pub const TOKEN_STRUCT: i32 = 260;
pub const TOKEN_UNION: i32 = 261;
pub const TOKEN_ENUM: i32 = 262;
pub const TOKEN_DECLARATION_RESULT: i32 = 263;
pub const TOKEN_PARAM_RESULT: i32 = 264;
pub const TOKEN_SCOPERES: i32 = 265;
pub const TOKEN_NUMBER: i32 = 266;
pub const TOKEN_IDENTIFIER: i32 = 267;
pub const TOKEN_STORAGE_CLASS_SPECIFIER: i32 = 268;
pub const TOKEN_TYPE_QUALIFIER: i32 = 269;
pub const TOKEN_FUNCTION_SPECIFIER: i32 = 270;
pub const TOKEN_TYPE_NAME: i32 = 271;

const YYEMPTY: i32 = -2;
const YYEOF: i32 = 0;
const YYTERROR: i32 = 1;
const YYUNDEFTOK: i32 = 2;
const YYMAXDEPTH: usize = 10000;

fn yytranslate(token: i32) -> i32 {
    if (0..=YYMAXUTOK).contains(&token) {
        YYTRANSLATE[token as usize] as i32
    } else {
        YYUNDEFTOK
    }
}

fn types_ref(glb: &Architecture) -> &TypeFactory {
    glb.types.as_deref().expect("type factory is not initialized")
}

fn types_mut(glb: &mut Architecture) -> &mut TypeFactory {
    glb.types.as_deref_mut().expect("type factory is not initialized")
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum TokenValue {
    #[default]
    None,
    Integer(u64),
    Text(String),
}

#[derive(Clone, Debug, Default)]
pub struct GrammarToken {
    pub tp: u32,
    pub value: TokenValue,
    pub lineno: i32,
    pub colno: i32,
    pub filenum: i32,
}

impl GrammarToken {
    pub const OPENPAREN: u32 = 0x28;
    pub const CLOSEPAREN: u32 = 0x29;
    pub const STAR: u32 = 0x2a;
    pub const COMMA: u32 = 0x2c;
    pub const SEMICOLON: u32 = 0x3b;
    pub const OPENBRACKET: u32 = 0x5b;
    pub const CLOSEBRACKET: u32 = 0x5d;
    pub const OPENBRACE: u32 = 0x7b;
    pub const CLOSEBRACE: u32 = 0x7d;
    pub const BADTOKEN: u32 = 0x100;
    pub const ENDOFFILE: u32 = 0x101;
    pub const DOTDOTDOT: u32 = 0x102;
    pub const SCOPERES: u32 = 0x103;
    pub const INTEGER: u32 = 0x104;
    pub const CHARCONSTANT: u32 = 0x105;
    pub const IDENTIFIER: u32 = 0x106;
    pub const STRINGVAL: u32 = 0x107;

    pub fn new() -> GrammarToken {
        GrammarToken {
            tp: 0,
            value: TokenValue::Integer(0),
            lineno: -1,
            colno: -1,
            filenum: -1,
        }
    }

    pub fn set(&mut self, tp: u32) -> Result<()> {
        self.tp = tp;
        Ok(())
    }

    pub fn set_text(&mut self, tp: u32, text: &[u8]) -> Result<()> {
        self.tp = tp;
        match tp {
            GrammarToken::INTEGER => {
                let charstring = String::from_utf8_lossy(text).to_string();
                let val = extract_i64(&charstring, Basefield::Auto).map_or(0, |extraction| extraction.value as i64);
                self.value = TokenValue::Integer(val as u64);
            }
            GrammarToken::IDENTIFIER | GrammarToken::STRINGVAL => {
                self.value = TokenValue::Text(String::from_utf8_lossy(text).to_string());
            }
            GrammarToken::CHARCONSTANT => {
                let first = text.first().copied().unwrap_or(0);
                if text.len() == 1 {
                    self.value = TokenValue::Integer(first as i8 as i64 as u64);
                } else {
                    let second = text.get(1).copied().unwrap_or(0);
                    let value = match second {
                        b'n' => 10,
                        b'0' => 0,
                        b'a' => 7,
                        b'b' => 8,
                        b't' => 9,
                        b'v' => 11,
                        b'f' => 12,
                        b'r' => 13,
                        other => other as i8 as i64 as u64,
                    };
                    self.value = TokenValue::Integer(value);
                }
            }
            _ => return Err(Error::Lowlevel("Bad internal grammar token set".to_string())),
        }
        Ok(())
    }

    pub fn set_position(&mut self, file: i32, line: i32, col: i32) {
        self.filenum = file;
        self.lineno = line;
        self.colno = col;
    }

    pub fn get_type(&self) -> u32 {
        self.tp
    }

    pub fn get_integer(&self) -> u64 {
        match self.value {
            TokenValue::Integer(integer) => integer,
            _ => 0,
        }
    }

    pub fn get_string(&self) -> Option<&str> {
        match &self.value {
            TokenValue::Text(text) => Some(text),
            _ => None,
        }
    }

    pub fn get_line_no(&self) -> i32 {
        self.lineno
    }

    pub fn get_col_no(&self) -> i32 {
        self.colno
    }

    pub fn get_file_num(&self) -> i32 {
        self.filenum
    }
}

pub struct GrammarLexer<'s> {
    pub filenamemap: BTreeMap<i32, String>,
    pub streammap: BTreeMap<i32, Box<dyn BufRead + 's>>,
    pub filestack: Vec<i32>,
    pub buffersize: i32,
    pub buffer: Vec<u8>,
    pub bufstart: i32,
    pub bufend: i32,
    pub curlineno: i32,
    pub in_stream: Option<i32>,
    pub endoffile: bool,
    pub state: u32,
    pub error: String,
}

impl<'s> GrammarLexer<'s> {
    pub const START: u32 = 0;
    pub const SLASH: u32 = 1;
    pub const DOT1: u32 = 2;
    pub const DOT2: u32 = 3;
    pub const DOT3: u32 = 4;
    pub const SCOPERES1: u32 = 5;
    pub const SCOPERES2: u32 = 6;
    pub const PUNCTUATION: u32 = 7;
    pub const ENDOFLINE_COMMENT: u32 = 8;
    pub const C_COMMENT: u32 = 9;
    pub const DOUBLEQUOTE: u32 = 10;
    pub const DOUBLEQUOTEEND: u32 = 11;
    pub const SINGLEQUOTE: u32 = 12;
    pub const SINGLEQUOTEEND: u32 = 13;
    pub const SINGLEBACKSLASH: u32 = 14;
    pub const NUMBER: u32 = 15;
    pub const IDENTIFIER: u32 = 16;

    pub fn new(maxbuffer: i32) -> GrammarLexer<'s> {
        GrammarLexer {
            filenamemap: BTreeMap::new(),
            streammap: BTreeMap::new(),
            filestack: Vec::new(),
            buffersize: maxbuffer,
            buffer: vec![0u8; maxbuffer.max(0) as usize + 1],
            bufstart: 0,
            bufend: 0,
            curlineno: 0,
            in_stream: None,
            endoffile: true,
            state: GrammarLexer::START,
            error: String::new(),
        }
    }

    fn buffer_at(&self, index: i32) -> u8 {
        if index < 0 {
            return 0;
        }
        self.buffer.get(index as usize).copied().unwrap_or(0)
    }

    fn buffer_store(&mut self, byte: u8) {
        let index = self.bufend as usize;
        if index >= self.buffer.len() {
            self.buffer.resize(index + 1, 0);
        }
        self.buffer[index] = byte;
        self.bufend += 1;
    }

    fn bump_line(&mut self) {
        self.curlineno += 1;
        self.bufstart = 0;
        self.bufend = 0;
    }

    fn move_state(&mut self, lookahead: u8) -> u32 {
        let mut lookahead = lookahead as i8;
        let mut newline = false;
        if lookahead < 32 {
            if lookahead == 9 || lookahead == 11 || lookahead == 12 || lookahead == 13 {
                lookahead = b' ' as i8;
            } else if lookahead == b'\n' as i8 {
                newline = true;
                lookahead = b' ' as i8;
            } else {
                self.set_error("Illegal character");
                return GrammarToken::BADTOKEN;
            }
        } else if lookahead == 127 {
            self.set_error("Illegal character");
            return GrammarToken::BADTOKEN;
        }
        let lookahead = lookahead as u8;
        let mut res: u32 = 0;
        let mut syntaxerror = false;
        match self.state {
            GrammarLexer::START => match lookahead {
                b'/' => self.state = GrammarLexer::SLASH,
                b'.' => self.state = GrammarLexer::DOT1,
                b'*' | b',' | b'(' | b')' | b'[' | b']' | b'{' | b'}' | b';' | b'=' => {
                    self.state = GrammarLexer::PUNCTUATION;
                    self.bufstart = self.bufend - 1;
                }
                b':' => self.state = GrammarLexer::SCOPERES1,
                b'-' | b'0'..=b'9' => {
                    self.state = GrammarLexer::NUMBER;
                    self.bufstart = self.bufend - 1;
                }
                b' ' => {}
                b'"' => {
                    self.state = GrammarLexer::DOUBLEQUOTE;
                    self.bufstart = self.bufend - 1;
                }
                b'\'' => self.state = GrammarLexer::SINGLEQUOTE,
                b'a'..=b'z' | b'A'..=b'Z' | b'_' => {
                    self.state = GrammarLexer::IDENTIFIER;
                    self.bufstart = self.bufend - 1;
                }
                _ => {
                    self.set_error("Illegal character");
                    return GrammarToken::BADTOKEN;
                }
            },
            GrammarLexer::SLASH => {
                if lookahead == b'*' {
                    self.state = GrammarLexer::C_COMMENT;
                } else if lookahead == b'/' {
                    self.state = GrammarLexer::ENDOFLINE_COMMENT;
                } else {
                    syntaxerror = true;
                }
            }
            GrammarLexer::DOT1 => {
                if lookahead == b'.' {
                    self.state = GrammarLexer::DOT2;
                } else {
                    syntaxerror = true;
                }
            }
            GrammarLexer::DOT2 => {
                if lookahead == b'.' {
                    self.state = GrammarLexer::DOT3;
                } else {
                    syntaxerror = true;
                }
            }
            GrammarLexer::DOT3 => {
                self.state = GrammarLexer::START;
                res = GrammarToken::DOTDOTDOT;
            }
            GrammarLexer::SCOPERES1 => {
                if lookahead == b':' {
                    self.state = GrammarLexer::SCOPERES2;
                } else {
                    self.state = GrammarLexer::START;
                    res = b':' as u32;
                }
            }
            GrammarLexer::SCOPERES2 => {
                self.state = GrammarLexer::START;
                res = GrammarToken::SCOPERES;
            }
            GrammarLexer::PUNCTUATION => {
                self.state = GrammarLexer::START;
                res = self.buffer_at(self.bufstart) as i8 as i32 as u32;
            }
            GrammarLexer::ENDOFLINE_COMMENT if newline => {
                self.state = GrammarLexer::START;
            }
            GrammarLexer::C_COMMENT
                if lookahead == b'/' && self.bufend > 1 && self.buffer_at(self.bufend - 2) == b'*' =>
            {
                self.state = GrammarLexer::START;
            }
            GrammarLexer::DOUBLEQUOTE if lookahead == b'"' => {
                self.state = GrammarLexer::DOUBLEQUOTEEND;
            }
            GrammarLexer::DOUBLEQUOTEEND => {
                self.state = GrammarLexer::START;
                res = GrammarToken::STRINGVAL;
            }
            GrammarLexer::SINGLEQUOTE => {
                if lookahead == b'\\' {
                    self.state = GrammarLexer::SINGLEBACKSLASH;
                } else if lookahead == b'\'' {
                    self.state = GrammarLexer::SINGLEQUOTEEND;
                }
            }
            GrammarLexer::SINGLEQUOTEEND => {
                self.state = GrammarLexer::START;
                res = GrammarToken::CHARCONSTANT;
            }
            GrammarLexer::SINGLEBACKSLASH => {
                self.state = GrammarLexer::SINGLEQUOTE;
            }
            GrammarLexer::NUMBER => {
                if lookahead == b'x' {
                    if (self.bufend - self.bufstart) != 2 || self.buffer_at(self.bufstart) != b'0' {
                        syntaxerror = true;
                    }
                } else if lookahead.is_ascii_digit()
                    || lookahead.is_ascii_uppercase()
                    || lookahead.is_ascii_lowercase()
                    || lookahead == b'_'
                {
                } else {
                    self.state = GrammarLexer::START;
                    res = GrammarToken::INTEGER;
                }
            }
            GrammarLexer::IDENTIFIER => {
                if lookahead.is_ascii_digit()
                    || lookahead.is_ascii_uppercase()
                    || lookahead.is_ascii_lowercase()
                    || lookahead == b'_'
                {
                } else {
                    self.state = GrammarLexer::START;
                    res = GrammarToken::IDENTIFIER;
                }
            }
            _ => {}
        }
        if syntaxerror {
            self.set_error("Syntax error");
            return GrammarToken::BADTOKEN;
        }
        if newline {
            self.bump_line();
        }
        res
    }

    fn establish_token(&mut self, token: &mut GrammarToken, val: u32) -> Result<()> {
        if val < GrammarToken::INTEGER {
            token.set(val)?;
        } else {
            let len = (self.bufend - self.bufstart) - 1;
            let text: Vec<u8> = if val == GrammarToken::CHARCONSTANT && len != 1 {
                vec![self.buffer_at(self.bufstart), self.buffer_at(self.bufstart + 1)]
            } else {
                (0..len.max(0))
                    .map(|index| self.buffer_at(self.bufstart + index))
                    .collect()
            };
            token.set_text(val, &text)?;
        }
        let file = self.filestack.last().copied().unwrap_or(-1);
        token.set_position(file, self.curlineno, self.bufstart);
        Ok(())
    }

    fn set_error(&mut self, err: &str) {
        self.error = err.to_string();
    }

    pub fn clear(&mut self) {
        self.filenamemap.clear();
        self.streammap.clear();
        self.filestack.clear();
        self.bufstart = 0;
        self.bufend = 0;
        self.curlineno = 0;
        self.state = GrammarLexer::START;
        self.in_stream = None;
        self.endoffile = true;
        self.error.clear();
    }

    pub fn get_cur_stream(&mut self) -> Option<&mut (dyn BufRead + 's)> {
        let key = self.in_stream?;
        self.streammap.get_mut(&key).map(|stream| stream.as_mut())
    }

    pub fn push_file(&mut self, filename: &str, input: Box<dyn BufRead + 's>) {
        let filenum = self.filenamemap.len() as i32;
        self.filenamemap.insert(filenum, filename.to_string());
        self.streammap.insert(filenum, input);
        self.filestack.push(filenum);
        self.in_stream = Some(filenum);
        self.endoffile = false;
    }

    pub fn pop_file(&mut self) {
        self.filestack.pop();
        match self.filestack.last() {
            None => {
                self.endoffile = true;
            }
            Some(filenum) => {
                self.in_stream = Some(*filenum);
            }
        }
    }

    fn read_byte(&mut self) -> Option<u8> {
        let stream = self.get_cur_stream()?;
        let byte = match stream.fill_buf() {
            Ok(available) => available.first().copied(),
            Err(_) => None,
        };
        if byte.is_some() {
            stream.consume(1);
        }
        byte
    }

    pub fn get_next_token(&mut self, token: &mut GrammarToken) -> Result<()> {
        let mut tok = GrammarToken::BADTOKEN;
        let mut firsttimethru = true;
        if self.endoffile {
            token.set(GrammarToken::ENDOFFILE)?;
            return Ok(());
        }
        loop {
            let nextchar;
            if !firsttimethru || self.bufend == 0 {
                if self.bufend >= self.buffersize {
                    self.set_error("Line too long");
                    tok = GrammarToken::BADTOKEN;
                    break;
                }
                match self.read_byte() {
                    Some(byte) => nextchar = byte,
                    None => {
                        self.endoffile = true;
                        break;
                    }
                }
                self.buffer_store(nextchar);
            } else {
                nextchar = self.buffer_at(self.bufend - 1);
            }
            tok = self.move_state(nextchar);
            firsttimethru = false;
            if tok != 0 {
                break;
            }
        }
        if self.endoffile {
            self.buffer_store(b' ');
            tok = self.move_state(b' ');
            if tok == 0 && self.state != GrammarLexer::START && self.state != GrammarLexer::ENDOFLINE_COMMENT {
                self.set_error("Incomplete token");
                tok = GrammarToken::BADTOKEN;
            }
        }
        self.establish_token(token, tok)
    }

    pub fn write_location(&self, out: &mut String, line: i32, filenum: i32) {
        out.push_str(&format!(" at line {}", line));
        out.push_str(" in ");
        if let Some(name) = self.filenamemap.get(&filenum) {
            out.push_str(name);
        }
    }

    pub fn write_token_location(&self, out: &mut String, line: i32, colno: i32) {
        if line != self.curlineno {
            return;
        }
        let bytes: Vec<u8> = (0..self.bufend).map(|index| self.buffer_at(index)).collect();
        out.push_str(&String::from_utf8_lossy(&bytes));
        out.push('\n');
        for _ in 0..colno {
            out.push(' ');
        }
        out.push_str("^--\n");
    }

    pub fn get_error(&self) -> &str {
        &self.error
    }
}

pub const POINTER_MOD: u32 = 0;
pub const ARRAY_MOD: u32 = 1;
pub const FUNCTION_MOD: u32 = 2;
pub const STRUCT_MOD: u32 = 3;
pub const ENUM_MOD: u32 = 4;

#[derive(Clone, Debug)]
pub enum TypeModifier {
    Pointer {
        flags: u32,
    },
    Array {
        flags: u32,
        arraysize: i32,
    },
    Function {
        paramlist: Vec<TypeDeclarator>,
        dotdotdot: bool,
    },
}

impl TypeModifier {
    pub fn new_pointer(fl: u32) -> TypeModifier {
        TypeModifier::Pointer { flags: fl }
    }

    pub fn new_array(fl: u32, arraysize: i32) -> TypeModifier {
        TypeModifier::Array { flags: fl, arraysize }
    }

    pub fn new_function(declarators: Vec<TypeDeclarator>, dtdtdt: bool, types: &TypeFactory) -> TypeModifier {
        let mut paramlist = declarators;
        if paramlist.len() == 1 {
            let decl = &paramlist[0];
            if decl.num_modifiers() == 0
                && let Some(ct) = decl.get_base_type()
                && types.get(ct).get_metatype() == TypeMetatype::Void
            {
                paramlist.clear();
            }
        }
        TypeModifier::Function {
            paramlist,
            dotdotdot: dtdtdt,
        }
    }

    pub fn get_type(&self) -> u32 {
        match self {
            TypeModifier::Pointer { .. } => POINTER_MOD,
            TypeModifier::Array { .. } => ARRAY_MOD,
            TypeModifier::Function { .. } => FUNCTION_MOD,
        }
    }

    pub fn is_valid(&self, types: &TypeFactory) -> Result<bool> {
        match self {
            TypeModifier::Pointer { .. } => Ok(true),
            TypeModifier::Array { arraysize, .. } => Ok(*arraysize > 0),
            TypeModifier::Function { paramlist, .. } => {
                for decl in paramlist.iter() {
                    if !decl.is_valid(types)? {
                        return Ok(false);
                    }
                    if decl.num_modifiers() == 0
                        && let Some(ct) = decl.get_base_type()
                        && types.get(ct).get_metatype() == TypeMetatype::Void
                    {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
        }
    }

    pub fn mod_type(&self, base: Option<TypeId>, decl: &TypeDeclarator, glb: &mut Architecture) -> Result<TypeId> {
        match self {
            TypeModifier::Pointer { .. } => {
                let spc = match glb.manager.get_default_data_space() {
                    Some(spc) => spc,
                    None => return Err(Error::Lowlevel("No default data space".to_string())),
                };
                let base = base.ok_or_else(|| Error::Parse("Parsed type is invalid".to_string()))?;
                let addrsize = spc.get_addr_size() as i32;
                types_mut(glb).get_type_pointer(addrsize, base, spc.get_word_size())
            }
            TypeModifier::Array { arraysize, .. } => {
                let base = base.ok_or_else(|| Error::Parse("Parsed type is invalid".to_string()))?;
                types_mut(glb).get_type_array(*arraysize, base)
            }
            TypeModifier::Function { .. } => {
                let mut proto = PrototypePieces::default();
                proto.outtype = match base {
                    None => Some(types_mut(glb).get_type_void()?),
                    Some(base) => Some(base),
                };
                proto.first_var_arg_slot = -1;
                self.get_in_types(&mut proto.intypes, glb)?;
                proto.model = decl.get_model(glb);
                TypeFactory::get_type_code_proto(glb, &proto)
            }
        }
    }

    pub fn get_in_types(&self, intypes: &mut Vec<TypeId>, glb: &mut Architecture) -> Result<()> {
        if let TypeModifier::Function { paramlist, .. } = self {
            for decl in paramlist.iter() {
                let ct = decl.build_type(glb)?;
                intypes.push(ct);
            }
        }
        Ok(())
    }

    pub fn get_in_names(&self, innames: &mut Vec<String>) {
        if let TypeModifier::Function { paramlist, .. } = self {
            for decl in paramlist.iter() {
                innames.push(decl.get_identifier().to_string());
            }
        }
    }

    pub fn is_dotdotdot(&self) -> bool {
        match self {
            TypeModifier::Function { dotdotdot, .. } => *dotdotdot,
            _ => false,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct TypeDeclarator {
    pub mods: Vec<TypeModifier>,
    pub basetype: Option<TypeId>,
    pub ident: String,
    pub model: String,
    pub flags: u32,
    pub num_bits: i32,
}

impl TypeDeclarator {
    pub fn new() -> TypeDeclarator {
        TypeDeclarator {
            mods: Vec::new(),
            basetype: None,
            ident: String::new(),
            model: String::new(),
            flags: 0,
            num_bits: 0,
        }
    }

    pub fn new_named(nm: &str) -> TypeDeclarator {
        TypeDeclarator {
            mods: Vec::new(),
            basetype: None,
            ident: nm.to_string(),
            model: String::new(),
            flags: 0,
            num_bits: 0,
        }
    }

    pub fn get_base_type(&self) -> Option<TypeId> {
        self.basetype
    }

    pub fn num_modifiers(&self) -> i32 {
        self.mods.len() as i32
    }

    pub fn get_num_bits(&self) -> i32 {
        self.num_bits
    }

    pub fn set_num_bits(&mut self, val: i32) {
        self.num_bits = val;
    }

    pub fn get_identifier(&self) -> &str {
        &self.ident
    }

    pub fn get_model(&self, glb: &Architecture) -> Option<ModelId> {
        let mut protomodel = None;
        if !self.model.is_empty() {
            protomodel = glb.get_model(&self.model);
        }
        if protomodel.is_none() {
            protomodel = glb.defaultfp;
        }
        protomodel
    }

    pub fn get_prototype(&self, pieces: &mut PrototypePieces, glb: &mut Architecture) -> Result<bool> {
        let fmod = match self.mods.first() {
            Some(modifier) if modifier.get_type() == FUNCTION_MOD => modifier,
            _ => return Ok(false),
        };
        pieces.model = self.get_model(glb);
        pieces.name = self.ident.clone();
        pieces.intypes.clear();
        fmod.get_in_types(&mut pieces.intypes, glb)?;
        pieces.innames.clear();
        fmod.get_in_names(&mut pieces.innames);
        pieces.first_var_arg_slot = if fmod.is_dotdotdot() {
            pieces.intypes.len() as i32
        } else {
            -1
        };
        pieces.outtype = self.basetype;
        let mut index = self.mods.len() - 1;
        while index != 0 {
            pieces.outtype = Some(self.mods[index].mod_type(pieces.outtype, self, glb)?);
            index -= 1;
        }
        Ok(true)
    }

    pub fn has_property(&self, mask: u32) -> bool {
        (self.flags & mask) != 0
    }

    pub fn build_type(&self, glb: &mut Architecture) -> Result<TypeId> {
        let mut restype = self.basetype;
        for modifier in self.mods.iter().rev() {
            restype = Some(modifier.mod_type(restype, self, glb)?);
        }
        restype.ok_or_else(|| Error::Parse("Parsed type is invalid".to_string()))
    }

    pub fn is_valid(&self, types: &TypeFactory) -> Result<bool> {
        if self.basetype.is_none() {
            return Ok(false);
        }
        let mut count = 0;
        for flag in [
            CParse::F_TYPEDEF,
            CParse::F_EXTERN,
            CParse::F_STATIC,
            CParse::F_AUTO,
            CParse::F_REGISTER,
        ] {
            if (self.flags & flag) != 0 {
                count += 1;
            }
        }
        if count > 1 {
            return Err(Error::Parse("Multiple storage specifiers".to_string()));
        }
        count = 0;
        for flag in [CParse::F_CONST, CParse::F_RESTRICT, CParse::F_VOLATILE] {
            if (self.flags & flag) != 0 {
                count += 1;
            }
        }
        if count > 1 {
            return Err(Error::Parse("Multiple type qualifiers".to_string()));
        }
        for modifier in self.mods.iter() {
            if !modifier.is_valid(types)? {
                return Ok(false);
            }
        }
        Ok(true)
    }
}

#[derive(Clone, Debug, Default)]
pub struct TypeSpecifiers {
    pub type_specifier: Option<TypeId>,
    pub function_specifier: String,
    pub flags: u32,
}

impl TypeSpecifiers {
    pub fn new() -> TypeSpecifiers {
        TypeSpecifiers {
            type_specifier: None,
            function_specifier: String::new(),
            flags: 0,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Enumerator {
    pub enumconstant: String,
    pub constantassigned: bool,
    pub value: u64,
}

impl Enumerator {
    pub fn new(nm: &str) -> Enumerator {
        Enumerator {
            enumconstant: nm.to_string(),
            constantassigned: false,
            value: 0,
        }
    }

    pub fn new_value(nm: &str, val: u64) -> Enumerator {
        Enumerator {
            enumconstant: nm.to_string(),
            constantassigned: true,
            value: val,
        }
    }
}

#[derive(Clone, Debug, Default)]
enum SemValue {
    #[default]
    Empty,
    Flags(u32),
    Dec(TypeDeclarator),
    DecList(Vec<Option<TypeDeclarator>>),
    Spec(TypeSpecifiers),
    PtrSpec(Vec<u32>),
    Type(Option<TypeId>),
    Enumer(Enumerator),
    VecEnum(Vec<Enumerator>),
    Str(String),
    Num(u64),
}

impl SemValue {
    fn flags(self) -> u32 {
        match self {
            SemValue::Flags(flags) => flags,
            _ => 0,
        }
    }

    fn dec(self) -> TypeDeclarator {
        match self {
            SemValue::Dec(dec) => dec,
            _ => TypeDeclarator::new(),
        }
    }

    fn declist(self) -> Vec<Option<TypeDeclarator>> {
        match self {
            SemValue::DecList(list) => list,
            _ => Vec::new(),
        }
    }

    fn spec(self) -> TypeSpecifiers {
        match self {
            SemValue::Spec(spec) => spec,
            _ => TypeSpecifiers::new(),
        }
    }

    fn ptrspec(self) -> Vec<u32> {
        match self {
            SemValue::PtrSpec(list) => list,
            _ => Vec::new(),
        }
    }

    fn datatype(self) -> Option<TypeId> {
        match self {
            SemValue::Type(tp) => tp,
            _ => None,
        }
    }

    fn enumer(self) -> Enumerator {
        match self {
            SemValue::Enumer(enumer) => enumer,
            _ => Enumerator::new(""),
        }
    }

    fn vecenum(self) -> Vec<Enumerator> {
        match self {
            SemValue::VecEnum(list) => list,
            _ => Vec::new(),
        }
    }

    fn text(self) -> String {
        match self {
            SemValue::Str(text) => text,
            _ => String::new(),
        }
    }

    fn num(self) -> u64 {
        match self {
            SemValue::Num(num) => num,
            _ => 0,
        }
    }
}

fn flatten_declist(list: Vec<Option<TypeDeclarator>>) -> Vec<TypeDeclarator> {
    list.into_iter().flatten().collect()
}

pub struct CParse<'s> {
    pub keywords: BTreeMap<String, u32>,
    pub lexer: GrammarLexer<'s>,
    pub lineno: i32,
    pub colno: i32,
    pub filenum: i32,
    pub lastdecls: Option<Vec<TypeDeclarator>>,
    pub firsttoken: i32,
    pub lasterror: String,
}

impl<'s> CParse<'s> {
    pub const F_TYPEDEF: u32 = 1;
    pub const F_EXTERN: u32 = 2;
    pub const F_STATIC: u32 = 4;
    pub const F_AUTO: u32 = 8;
    pub const F_REGISTER: u32 = 16;
    pub const F_CONST: u32 = 32;
    pub const F_RESTRICT: u32 = 64;
    pub const F_VOLATILE: u32 = 128;
    pub const F_INLINE: u32 = 256;
    pub const F_STRUCT: u32 = 512;
    pub const F_UNION: u32 = 1024;
    pub const F_ENUM: u32 = 2048;

    pub const DOC_DECLARATION: u32 = 0;
    pub const DOC_PARAMETER_DECLARATION: u32 = 1;

    pub fn new(maxbuf: i32) -> CParse<'s> {
        let mut keywords = BTreeMap::new();
        keywords.insert("typedef".to_string(), CParse::F_TYPEDEF);
        keywords.insert("extern".to_string(), CParse::F_EXTERN);
        keywords.insert("static".to_string(), CParse::F_STATIC);
        keywords.insert("auto".to_string(), CParse::F_AUTO);
        keywords.insert("register".to_string(), CParse::F_REGISTER);
        keywords.insert("const".to_string(), CParse::F_CONST);
        keywords.insert("restrict".to_string(), CParse::F_RESTRICT);
        keywords.insert("volatile".to_string(), CParse::F_VOLATILE);
        keywords.insert("inline".to_string(), CParse::F_INLINE);
        keywords.insert("struct".to_string(), CParse::F_STRUCT);
        keywords.insert("union".to_string(), CParse::F_UNION);
        keywords.insert("enum".to_string(), CParse::F_ENUM);
        CParse {
            keywords,
            lexer: GrammarLexer::new(maxbuf),
            lineno: -1,
            colno: -1,
            filenum: -1,
            lastdecls: None,
            firsttoken: -1,
            lasterror: String::new(),
        }
    }

    fn set_error(&mut self, msg: &str) {
        let mut text = String::from(msg);
        self.lexer.write_location(&mut text, self.lineno, self.filenum);
        text.push('\n');
        self.lexer.write_token_location(&mut text, self.lineno, self.colno);
        self.lasterror = text;
    }

    fn lookup_identifier(&mut self, glb: &mut Architecture, nm: &str) -> (i32, Option<TypeId>) {
        if let Some(flag) = self.keywords.get(nm) {
            match *flag {
                CParse::F_TYPEDEF | CParse::F_EXTERN | CParse::F_STATIC | CParse::F_AUTO | CParse::F_REGISTER => {
                    return (TOKEN_STORAGE_CLASS_SPECIFIER, None);
                }
                CParse::F_CONST | CParse::F_RESTRICT | CParse::F_VOLATILE => return (TOKEN_TYPE_QUALIFIER, None),
                CParse::F_INLINE => return (TOKEN_FUNCTION_SPECIFIER, None),
                CParse::F_STRUCT => return (TOKEN_STRUCT, None),
                CParse::F_UNION => return (TOKEN_UNION, None),
                CParse::F_ENUM => return (TOKEN_ENUM, None),
                _ => {}
            }
        }
        if let Some(tp) = types_mut(glb).find_by_name(nm) {
            return (TOKEN_TYPE_NAME, Some(tp));
        }
        if glb.has_model(nm) {
            return (TOKEN_FUNCTION_SPECIFIER, None);
        }
        (TOKEN_IDENTIFIER, None)
    }

    fn run_parse(&mut self, glb: &mut Architecture, doctype: u32) -> Result<bool> {
        match doctype {
            CParse::DOC_DECLARATION => self.firsttoken = TOKEN_DECLARATION_RESULT,
            CParse::DOC_PARAMETER_DECLARATION => self.firsttoken = TOKEN_PARAM_RESULT,
            _ => return Err(Error::Lowlevel("Bad document type".to_string())),
        }
        let res = self.grammarparse(glb)?;
        if res != 0 {
            if self.lasterror.is_empty() {
                self.set_error("Syntax error");
            }
            return Ok(false);
        }
        Ok(true)
    }

    fn grammarparse(&mut self, glb: &mut Architecture) -> Result<i32> {
        let mut states: Vec<i32> = Vec::with_capacity(200);
        let mut values: Vec<SemValue> = Vec::with_capacity(200);
        let mut yystate: i32 = 0;
        let mut yyerrstatus = 0;
        let mut yychar = YYEMPTY;
        let mut yylval = SemValue::Empty;
        states.push(yystate);
        values.push(SemValue::Empty);
        enum Step {
            SetState,
            Backup,
            Default,
            Reduce(i32),
            ErrorLab,
            ErrorLab1,
        }
        let mut step = Step::SetState;
        loop {
            match step {
                Step::SetState => {
                    if states.len() >= YYMAXDEPTH {
                        return Ok(2);
                    }
                    if yystate == YYFINAL {
                        return Ok(0);
                    }
                    step = Step::Backup;
                }
                Step::Backup => {
                    let mut yyn = YYPACT[yystate as usize] as i32;
                    if yyn == YYPACT_NINF {
                        step = Step::Default;
                        continue;
                    }
                    if yychar == YYEMPTY {
                        yychar = self.lex(glb, &mut yylval)?;
                    }
                    let yytoken = if yychar <= YYEOF {
                        yychar = YYEOF;
                        YYEOF
                    } else {
                        yytranslate(yychar)
                    };
                    yyn += yytoken;
                    if !(0..=YYLAST).contains(&yyn) || YYCHECK[yyn as usize] as i32 != yytoken {
                        step = Step::Default;
                        continue;
                    }
                    yyn = YYTABLE[yyn as usize] as i32;
                    if yyn <= 0 {
                        if yyn == YYTABLE_NINF {
                            step = Step::ErrorLab;
                            continue;
                        }
                        step = Step::Reduce(-yyn);
                        continue;
                    }
                    if yyerrstatus > 0 {
                        yyerrstatus -= 1;
                    }
                    yystate = yyn;
                    values.push(yylval.clone());
                    states.push(yystate);
                    yychar = YYEMPTY;
                    step = Step::SetState;
                }
                Step::Default => {
                    let yyn = YYDEFACT[yystate as usize] as i32;
                    if yyn == 0 {
                        step = Step::ErrorLab;
                        continue;
                    }
                    step = Step::Reduce(yyn);
                }
                Step::Reduce(rule) => {
                    let yylen = YYR2[rule as usize] as usize;
                    let args = values.split_off(values.len() - yylen);
                    states.truncate(states.len() - yylen);
                    let value = self.reduce(rule, args, glb)?;
                    values.push(value);
                    let top = *states.last().unwrap_or(&0);
                    let yylhs = YYR1[rule as usize] as i32 - YYNTOKENS;
                    let yyi = YYPGOTO[yylhs as usize] as i32 + top;
                    yystate = if (0..=YYLAST).contains(&yyi) && YYCHECK[yyi as usize] as i32 == top {
                        YYTABLE[yyi as usize] as i32
                    } else {
                        YYDEFGOTO[yylhs as usize] as i32
                    };
                    states.push(yystate);
                    step = Step::SetState;
                }
                Step::ErrorLab => {
                    if yyerrstatus == 3 {
                        if yychar <= YYEOF {
                            if yychar == YYEOF {
                                return Ok(1);
                            }
                        } else {
                            yychar = YYEMPTY;
                        }
                    }
                    step = Step::ErrorLab1;
                }
                Step::ErrorLab1 => {
                    yyerrstatus = 3;
                    let shift_state = loop {
                        let mut yyn = YYPACT[yystate as usize] as i32;
                        if yyn != YYPACT_NINF {
                            yyn += YYTERROR;
                            if (0..=YYLAST).contains(&yyn) && YYCHECK[yyn as usize] as i32 == YYTERROR {
                                yyn = YYTABLE[yyn as usize] as i32;
                                if 0 < yyn {
                                    break Some(yyn);
                                }
                            }
                        }
                        if states.len() <= 1 {
                            return Ok(1);
                        }
                        states.pop();
                        values.pop();
                        yystate = *states.last().unwrap_or(&0);
                    };
                    if let Some(next) = shift_state {
                        values.push(yylval.clone());
                        yystate = next;
                        states.push(yystate);
                    }
                    step = Step::SetState;
                }
            }
        }
    }

    fn reduce(&mut self, rule: i32, args: Vec<SemValue>, glb: &mut Architecture) -> Result<SemValue> {
        let mut args: Vec<Option<SemValue>> = args.into_iter().map(Some).collect();
        let default_value = args.first().and_then(|value| value.clone()).unwrap_or_default();
        let mut arg = |index: usize| -> SemValue { args[index].take().unwrap_or_default() };
        let value = match rule {
            2 => {
                let decls = flatten_declist(arg(1).declist());
                self.set_result_declarations(Some(decls));
                default_value
            }
            3 => {
                let dec = arg(1).dec();
                self.set_result_declarations(Some(vec![dec]));
                default_value
            }
            4 => SemValue::DecList(self.merge_spec_dec_vec(&arg(0).spec())),
            5 => {
                let spec = arg(0).spec();
                let list = arg(1).declist();
                SemValue::DecList(self.merge_spec_dec_vec_list(&spec, list))
            }
            6 | 8 => {
                let text = arg(0).text();
                let spec = self.new_specifier();
                SemValue::Spec(self.add_specifier(spec, &text))
            }
            7 => {
                let tp = arg(0).datatype();
                let spec = self.new_specifier();
                SemValue::Spec(self.add_type_specifier(spec, tp))
            }
            9 => {
                let text = arg(0).text();
                let spec = self.new_specifier();
                SemValue::Spec(self.add_func_specifier(spec, &text))
            }
            10 | 12 => {
                let text = arg(0).text();
                let spec = arg(1).spec();
                SemValue::Spec(self.add_specifier(spec, &text))
            }
            11 => {
                let tp = arg(0).datatype();
                let spec = arg(1).spec();
                SemValue::Spec(self.add_type_specifier(spec, tp))
            }
            13 => {
                let text = arg(0).text();
                let spec = arg(1).spec();
                SemValue::Spec(self.add_func_specifier(spec, &text))
            }
            14 | 33 => {
                let dec = arg(0).dec();
                let mut list = self.new_vec_declarator();
                list.push(Some(dec));
                SemValue::DecList(list)
            }
            15 | 34 => {
                let mut list = arg(0).declist();
                list.push(Some(arg(2).dec()));
                SemValue::DecList(list)
            }
            16 | 17 | 18 | 19 | 26 | 35 | 46 | 48 | 61 | 69 | 74 => arg(0),
            20 => {
                let list = arg(2).declist();
                SemValue::Type(self.new_struct(glb, "", list)?)
            }
            21 => {
                let ident = arg(1).text();
                let list = arg(3).declist();
                SemValue::Type(self.new_struct(glb, &ident, list)?)
            }
            22 => {
                let ident = arg(1).text();
                SemValue::Type(self.old_struct(glb, &ident))
            }
            23 => {
                let list = arg(2).declist();
                SemValue::Type(self.new_union(glb, "", list)?)
            }
            24 => {
                let ident = arg(1).text();
                let list = arg(3).declist();
                SemValue::Type(self.new_union(glb, &ident, list)?)
            }
            25 => {
                let ident = arg(1).text();
                SemValue::Type(self.old_union(glb, &ident))
            }
            27 => {
                let mut list = arg(0).declist();
                list.extend(arg(1).declist());
                SemValue::DecList(list)
            }
            28 => {
                let spec = arg(0).spec();
                let list = arg(1).declist();
                SemValue::DecList(self.merge_spec_dec_vec_list(&spec, list))
            }
            29 => {
                let tp = arg(0).datatype();
                let spec = self.new_specifier();
                SemValue::Spec(self.add_type_specifier(spec, tp))
            }
            30 => {
                let tp = arg(0).datatype();
                let spec = arg(1).spec();
                SemValue::Spec(self.add_type_specifier(spec, tp))
            }
            31 => {
                let text = arg(0).text();
                let spec = self.new_specifier();
                SemValue::Spec(self.add_specifier(spec, &text))
            }
            32 => {
                let text = arg(0).text();
                let spec = arg(1).spec();
                SemValue::Spec(self.add_specifier(spec, &text))
            }
            36 => {
                let mut dec = arg(0).dec();
                let num = arg(2).num();
                dec.set_num_bits(num as i32);
                SemValue::Dec(dec)
            }
            37 | 39 => {
                let ident = arg(1).text();
                let list = arg(3).vecenum();
                SemValue::Type(self.new_enum(glb, &ident, list)?)
            }
            38 | 40 => {
                let list = arg(2).vecenum();
                SemValue::Type(self.new_enum(glb, "", list)?)
            }
            41 => {
                let ident = arg(1).text();
                SemValue::Type(self.old_enum(glb, &ident))
            }
            42 => {
                let enumer = arg(0).enumer();
                let mut list = self.new_vec_enumerator();
                list.push(enumer);
                SemValue::VecEnum(list)
            }
            43 => {
                let mut list = arg(0).vecenum();
                list.push(arg(2).enumer());
                SemValue::VecEnum(list)
            }
            44 => {
                let ident = arg(0).text();
                SemValue::Enumer(self.new_enumerator(&ident))
            }
            45 => {
                let ident = arg(0).text();
                let num = arg(2).num();
                SemValue::Enumer(self.new_enumerator_value(&ident, num))
            }
            47 => {
                let ptr = arg(0).ptrspec();
                let dec = arg(1).dec();
                SemValue::Dec(self.merge_pointer(ptr, dec))
            }
            49 => {
                let mut text = arg(0).text();
                text.push_str("::");
                text.push_str(&arg(2).text());
                SemValue::Str(text)
            }
            50 => {
                let text = arg(0).text();
                SemValue::Dec(self.new_declarator_named(&text))
            }
            51 | 71 => arg(1),
            52 => {
                let dec = arg(0).dec();
                let flags = arg(2).flags();
                let num = arg(3).num();
                SemValue::Dec(self.new_array(dec, flags, num))
            }
            53 | 72 => {
                let dec = arg(0).dec();
                let num = arg(2).num();
                SemValue::Dec(self.new_array(dec, 0, num))
            }
            54 | 73 => {
                let dec = arg(0).dec();
                let list = arg(2).declist();
                SemValue::Dec(self.new_func(dec, list, types_ref(glb)))
            }
            55 => {
                let mut ptr = self.new_pointer();
                ptr.push(0);
                SemValue::PtrSpec(ptr)
            }
            56 => {
                let flags = arg(1).flags();
                let mut ptr = self.new_pointer();
                ptr.push(flags);
                SemValue::PtrSpec(ptr)
            }
            57 => {
                let mut ptr = arg(1).ptrspec();
                ptr.push(0);
                SemValue::PtrSpec(ptr)
            }
            58 => {
                let flags = arg(1).flags();
                let mut ptr = arg(2).ptrspec();
                ptr.push(flags);
                SemValue::PtrSpec(ptr)
            }
            59 => {
                let text = arg(0).text();
                SemValue::Flags(self.convert_flag(&text))
            }
            60 => {
                let mut flags = arg(0).flags();
                let text = arg(1).text();
                flags |= self.convert_flag(&text);
                SemValue::Flags(flags)
            }
            62 => {
                let mut list = arg(0).declist();
                list.push(None);
                SemValue::DecList(list)
            }
            63 => {
                let dec = arg(0).dec();
                let mut list = self.new_vec_declarator();
                list.push(Some(dec));
                SemValue::DecList(list)
            }
            64 => {
                let mut list = arg(0).declist();
                list.push(Some(arg(2).dec()));
                SemValue::DecList(list)
            }
            65 | 67 => {
                let spec = arg(0).spec();
                let dec = arg(1).dec();
                SemValue::Dec(self.merge_spec_dec_with(&spec, dec))
            }
            66 => {
                let spec = arg(0).spec();
                SemValue::Dec(self.merge_spec_dec(&spec))
            }
            68 => {
                let ptr = arg(0).ptrspec();
                let dec = self.new_declarator();
                SemValue::Dec(self.merge_pointer(ptr, dec))
            }
            70 => {
                let ptr = arg(0).ptrspec();
                let dec = arg(1).dec();
                SemValue::Dec(self.merge_pointer(ptr, dec))
            }
            _ => default_value,
        };
        Ok(value)
    }

    pub fn clear(&mut self) {
        self.clear_allocation();
        self.lasterror.clear();
        self.lastdecls = None;
        self.lexer.clear();
        self.firsttoken = -1;
    }

    pub fn merge_spec_dec_vec(&mut self, spec: &TypeSpecifiers) -> Vec<Option<TypeDeclarator>> {
        let declist = vec![Some(TypeDeclarator::new())];
        self.merge_spec_dec_vec_list(spec, declist)
    }

    pub fn merge_spec_dec_vec_list(
        &mut self,
        spec: &TypeSpecifiers,
        declist: Vec<Option<TypeDeclarator>>,
    ) -> Vec<Option<TypeDeclarator>> {
        declist
            .into_iter()
            .map(|dec| dec.map(|dec| self.merge_spec_dec_with(spec, dec)))
            .collect()
    }

    pub fn merge_spec_dec(&mut self, spec: &TypeSpecifiers) -> TypeDeclarator {
        let dec = TypeDeclarator::new();
        self.merge_spec_dec_with(spec, dec)
    }

    pub fn merge_spec_dec_with(&mut self, spec: &TypeSpecifiers, dec: TypeDeclarator) -> TypeDeclarator {
        let mut dec = dec;
        dec.basetype = spec.type_specifier;
        dec.model = spec.function_specifier.clone();
        dec.flags |= spec.flags;
        dec
    }

    pub fn add_specifier(&mut self, spec: TypeSpecifiers, text: &str) -> TypeSpecifiers {
        let mut spec = spec;
        let flag = self.convert_flag(text);
        spec.flags |= flag;
        spec
    }

    pub fn add_type_specifier(&mut self, spec: TypeSpecifiers, tp: Option<TypeId>) -> TypeSpecifiers {
        let mut spec = spec;
        if spec.type_specifier.is_some() {
            self.set_error("Multiple type specifiers");
        }
        spec.type_specifier = tp;
        spec
    }

    pub fn add_func_specifier(&mut self, spec: TypeSpecifiers, text: &str) -> TypeSpecifiers {
        let mut spec = spec;
        match self.keywords.get(text) {
            Some(flag) => spec.flags |= *flag,
            None => {
                if !spec.function_specifier.is_empty() {
                    self.set_error("Multiple parameter models");
                }
                spec.function_specifier = text.to_string();
            }
        }
        spec
    }

    pub fn merge_pointer(&mut self, ptr: Vec<u32>, dec: TypeDeclarator) -> TypeDeclarator {
        let mut dec = dec;
        for flags in ptr {
            dec.mods.push(TypeModifier::new_pointer(flags));
        }
        dec
    }

    pub fn new_declarator_named(&mut self, text: &str) -> TypeDeclarator {
        TypeDeclarator::new_named(text)
    }

    pub fn new_declarator(&mut self) -> TypeDeclarator {
        TypeDeclarator::new()
    }

    pub fn new_specifier(&mut self) -> TypeSpecifiers {
        TypeSpecifiers::new()
    }

    pub fn new_vec_declarator(&mut self) -> Vec<Option<TypeDeclarator>> {
        Vec::new()
    }

    pub fn new_pointer(&mut self) -> Vec<u32> {
        Vec::new()
    }

    pub fn new_array(&mut self, dec: TypeDeclarator, flags: u32, num: u64) -> TypeDeclarator {
        let mut dec = dec;
        dec.mods.push(TypeModifier::new_array(flags, num as i32));
        dec
    }

    pub fn new_func(
        &mut self,
        dec: TypeDeclarator,
        declist: Vec<Option<TypeDeclarator>>,
        types: &TypeFactory,
    ) -> TypeDeclarator {
        let mut dec = dec;
        let mut declist = declist;
        let mut dotdotdot = false;
        if let Some(last) = declist.last()
            && last.is_none()
        {
            dotdotdot = true;
            declist.pop();
        }
        dec.mods
            .push(TypeModifier::new_function(flatten_declist(declist), dotdotdot, types));
        dec
    }

    pub fn new_struct(
        &mut self,
        glb: &mut Architecture,
        ident: &str,
        declist: Vec<Option<TypeDeclarator>>,
    ) -> Result<Option<TypeId>> {
        let res = types_mut(glb).get_type_struct(ident)?;
        let mut sublist: Vec<TypeField> = Vec::new();
        let mut bitlist: Vec<TypeBitField> = Vec::new();
        let is_big_endian = match glb.manager.get_default_data_space() {
            Some(spc) => spc.is_big_endian(),
            None => false,
        };
        for decl in flatten_declist(declist) {
            if !decl.is_valid(types_ref(glb))? {
                self.set_error("Invalid structure declarator");
                types_mut(glb).destroy_type(res)?;
                return Ok(None);
            }
            let ct = decl.build_type(glb)?;
            if decl.get_num_bits() != 0 {
                bitlist.push(TypeBitField::new(
                    sublist.len() as i32,
                    decl.get_num_bits(),
                    is_big_endian,
                    decl.get_identifier(),
                    ct,
                ));
            } else {
                sublist.push(TypeField::new(0, -1, decl.get_identifier(), ct));
            }
        }
        if let Err(err) = types_mut(glb).assign_raw_fields_struct(res, &mut sublist, &mut bitlist) {
            if !err.is_lowlevel() {
                return Err(err);
            }
            self.set_error(err.explain());
            types_mut(glb).destroy_type(res)?;
            return Ok(None);
        }
        Ok(Some(res))
    }

    pub fn old_struct(&mut self, glb: &mut Architecture, ident: &str) -> Option<TypeId> {
        let res = types_mut(glb).find_by_name(ident);
        let valid = match res {
            Some(tp) => types_ref(glb).get(tp).get_metatype() == TypeMetatype::Struct,
            None => false,
        };
        if !valid {
            self.set_error("Identifier does not represent a struct as required");
        }
        res
    }

    pub fn new_union(
        &mut self,
        glb: &mut Architecture,
        ident: &str,
        declist: Vec<Option<TypeDeclarator>>,
    ) -> Result<Option<TypeId>> {
        let res = types_mut(glb).get_type_union(ident)?;
        let mut sublist: Vec<TypeField> = Vec::new();
        for (index, decl) in flatten_declist(declist).into_iter().enumerate() {
            if !decl.is_valid(types_ref(glb))? {
                self.set_error("Invalid union declarator");
                types_mut(glb).destroy_type(res)?;
                return Ok(None);
            }
            let ct = decl.build_type(glb)?;
            sublist.push(TypeField::new(index as i32, 0, decl.get_identifier(), ct));
        }
        if let Err(err) = types_mut(glb).assign_raw_fields_union(res, &mut sublist) {
            if !err.is_lowlevel() {
                return Err(err);
            }
            self.set_error(err.explain());
            types_mut(glb).destroy_type(res)?;
            return Ok(None);
        }
        Ok(Some(res))
    }

    pub fn old_union(&mut self, glb: &mut Architecture, ident: &str) -> Option<TypeId> {
        let res = types_mut(glb).find_by_name(ident);
        let valid = match res {
            Some(tp) => types_ref(glb).get(tp).get_metatype() == TypeMetatype::Union,
            None => false,
        };
        if !valid {
            self.set_error("Identifier does not represent a union as required");
        }
        res
    }

    pub fn new_enumerator(&mut self, ident: &str) -> Enumerator {
        Enumerator::new(ident)
    }

    pub fn new_enumerator_value(&mut self, ident: &str, val: u64) -> Enumerator {
        Enumerator::new_value(ident, val)
    }

    pub fn new_vec_enumerator(&mut self) -> Vec<Enumerator> {
        Vec::new()
    }

    pub fn new_enum(
        &mut self,
        glb: &mut Architecture,
        ident: &str,
        vecenum: Vec<Enumerator>,
    ) -> Result<Option<TypeId>> {
        let res = types_mut(glb).get_type_enum(ident)?;
        let mut namelist: Vec<String> = Vec::new();
        let mut vallist: Vec<u64> = Vec::new();
        let mut assignlist: Vec<bool> = Vec::new();
        for enumer in vecenum.iter() {
            namelist.push(enumer.enumconstant.clone());
            vallist.push(enumer.value);
            assignlist.push(enumer.constantassigned);
        }
        let mut namemap: BTreeMap<u64, String> = BTreeMap::new();
        let assigned = Datatype::assign_values(
            &mut namemap,
            &namelist,
            &mut vallist,
            &assignlist,
            types_ref(glb).get(res),
        );
        if let Err(err) = assigned {
            if !err.is_lowlevel() {
                return Err(err);
            }
            self.set_error(err.explain());
            types_mut(glb).destroy_type(res)?;
            return Ok(None);
        }
        types_mut(glb).set_enum_values(&namemap, res);
        Ok(Some(res))
    }

    pub fn old_enum(&mut self, glb: &mut Architecture, ident: &str) -> Option<TypeId> {
        let res = types_mut(glb).find_by_name(ident);
        let valid = match res {
            Some(tp) => types_ref(glb).get(tp).is_enum_type(),
            None => false,
        };
        if !valid {
            self.set_error("Identifier does not represent an enum as required");
        }
        res
    }

    pub fn convert_flag(&mut self, text: &str) -> u32 {
        if let Some(flag) = self.keywords.get(text) {
            return *flag;
        }
        self.set_error("Unknown qualifier");
        0
    }

    pub fn clear_allocation(&mut self) {}

    fn lex(&mut self, glb: &mut Architecture, yylval: &mut SemValue) -> Result<i32> {
        if self.firsttoken != -1 {
            let retval = self.firsttoken;
            self.firsttoken = -1;
            return Ok(retval);
        }
        if !self.lasterror.is_empty() {
            return Ok(TOKEN_BADTOKEN);
        }
        let mut tok = GrammarToken::new();
        self.lexer.get_next_token(&mut tok)?;
        self.lineno = tok.get_line_no();
        self.colno = tok.get_col_no();
        self.filenum = tok.get_file_num();
        match tok.get_type() {
            GrammarToken::INTEGER | GrammarToken::CHARCONSTANT => {
                *yylval = SemValue::Num(tok.get_integer());
                Ok(TOKEN_NUMBER)
            }
            GrammarToken::IDENTIFIER => {
                let text = tok.get_string().unwrap_or("").to_string();
                *yylval = SemValue::Str(text.clone());
                let (token, tp) = self.lookup_identifier(glb, &text);
                if token == TOKEN_TYPE_NAME {
                    *yylval = SemValue::Type(tp);
                }
                Ok(token)
            }
            GrammarToken::STRINGVAL => {
                self.set_error("Illegal string constant");
                Ok(TOKEN_BADTOKEN)
            }
            GrammarToken::DOTDOTDOT => Ok(TOKEN_DOTDOTDOT),
            GrammarToken::SCOPERES => Ok(TOKEN_SCOPERES),
            GrammarToken::BADTOKEN => {
                let message = self.lexer.get_error().to_string();
                self.set_error(&message);
                Ok(TOKEN_BADTOKEN)
            }
            GrammarToken::ENDOFFILE => Ok(-1),
            other => Ok(other as i32),
        }
    }

    pub fn parse_file(&mut self, glb: &mut Architecture, filename: &str, doctype: u32) -> Result<bool> {
        self.clear();
        let file = match std::fs::File::open(filename) {
            Ok(file) => file,
            Err(_) => {
                return Err(Error::Lowlevel(format!(
                    "Unable to open file for parsing: {}",
                    filename
                )));
            }
        };
        self.lexer.push_file(filename, Box::new(std::io::BufReader::new(file)));
        self.run_parse(glb, doctype)
    }

    pub fn parse_stream(&mut self, glb: &mut Architecture, reader: &'s mut dyn BufRead, doctype: u32) -> Result<bool> {
        self.clear();
        self.lexer.push_file("stream", Box::new(reader));
        self.run_parse(glb, doctype)
    }

    pub fn get_error(&self) -> &str {
        &self.lasterror
    }

    pub fn set_result_declarations(&mut self, val: Option<Vec<TypeDeclarator>>) {
        self.lastdecls = val;
    }

    pub fn get_result_declarations(&self) -> Option<&Vec<TypeDeclarator>> {
        self.lastdecls.as_ref()
    }
}

fn parse_single_declaration(reader: &mut dyn BufRead, glb: &mut Architecture, doctype: u32) -> Result<TypeDeclarator> {
    let mut parser = CParse::new(4096);
    if !parser.parse_stream(glb, reader, doctype)? {
        return Err(Error::Parse(parser.get_error().to_string()));
    }
    let decls = match parser.get_result_declarations() {
        Some(decls) if !decls.is_empty() => decls,
        _ => return Err(Error::Parse("Did not parse a datatype".to_string())),
    };
    if decls.len() > 1 {
        return Err(Error::Parse("Parsed multiple declarations".to_string()));
    }
    let decl = decls[0].clone();
    if !decl.is_valid(types_ref(glb))? {
        return Err(Error::Parse("Parsed type is invalid".to_string()));
    }
    Ok(decl)
}

pub fn parse_type(reader: &mut dyn BufRead, name: &mut String, glb: &mut Architecture) -> Result<TypeId> {
    let decl = parse_single_declaration(reader, glb, CParse::DOC_PARAMETER_DECLARATION)?;
    *name = decl.get_identifier().to_string();
    decl.build_type(glb)
}

pub fn parse_protopieces(pieces: &mut PrototypePieces, reader: &mut dyn BufRead, glb: &mut Architecture) -> Result<()> {
    let decl = parse_single_declaration(reader, glb, CParse::DOC_DECLARATION)?;
    if !decl.get_prototype(pieces, glb)? {
        return Err(Error::Parse("Did not parse a prototype".to_string()));
    }
    Ok(())
}

pub fn parse_c(glb: &mut Architecture, reader: &mut dyn BufRead) -> Result<()> {
    let decl = parse_single_declaration(reader, glb, CParse::DOC_DECLARATION)?;
    if decl.has_property(CParse::F_EXTERN) {
        let mut pieces = PrototypePieces::default();
        if !decl.get_prototype(&mut pieces, glb)? {
            return Err(Error::Parse("Did not parse prototype as expected".to_string()));
        }
        glb.set_prototype(&pieces)?;
    } else if decl.has_property(CParse::F_TYPEDEF) {
        let ct = decl.build_type(glb)?;
        if decl.get_identifier().is_empty() {
            return Err(Error::Parse("Missing identifier for typedef".to_string()));
        }
        if types_ref(glb).get(ct).get_metatype() == TypeMetatype::Struct {
            types_mut(glb).set_name(ct, decl.get_identifier())?;
        } else {
            types_mut(glb).get_typedef(ct, decl.get_identifier(), 0, 0)?;
        }
    } else {
        let base = decl.get_base_type().expect("valid declaration has a base type");
        let datatype = types_ref(glb).get(base);
        if datatype.get_metatype() == TypeMetatype::Struct
            || datatype.get_metatype() == TypeMetatype::Union
            || datatype.is_enum_type()
        {
        } else {
            return Err(Error::Lowlevel("Not sure what to do with this type".to_string()));
        }
    }
    Ok(())
}

struct StreamReader<'r> {
    stream: &'r mut dyn BufRead,
    failed: bool,
}

impl<'r> StreamReader<'r> {
    fn new(stream: &'r mut dyn BufRead) -> StreamReader<'r> {
        StreamReader { stream, failed: false }
    }

    fn peek(&mut self) -> i32 {
        if self.failed {
            return -1;
        }
        match self.stream.fill_buf() {
            Ok(available) if !available.is_empty() => available[0] as i8 as i32,
            _ => {
                self.failed = true;
                -1
            }
        }
    }

    fn peek_raw(&mut self) -> Option<u8> {
        match self.stream.fill_buf() {
            Ok(available) if !available.is_empty() => Some(available[0]),
            _ => None,
        }
    }

    fn skip_ws(&mut self) {
        if self.failed {
            return;
        }
        while let Some(byte) = self.peek_raw() {
            if !is_space(byte) {
                return;
            }
            self.stream.consume(1);
        }
    }

    fn read_char(&mut self, tok: &mut u8) {
        if self.failed {
            return;
        }
        self.skip_ws();
        match self.peek_raw() {
            Some(byte) => {
                self.stream.consume(1);
                *tok = byte;
            }
            None => self.failed = true,
        }
    }

    fn read_word(&mut self, word: &mut String) {
        if self.failed {
            return;
        }
        self.skip_ws();
        let mut bytes: Vec<u8> = Vec::new();
        while let Some(byte) = self.peek_raw() {
            if is_space(byte) {
                break;
            }
            bytes.push(byte);
            self.stream.consume(1);
        }
        if bytes.is_empty() {
            self.failed = true;
            return;
        }
        *word = String::from_utf8_lossy(&bytes).to_string();
    }

    fn integer_text(&mut self) -> String {
        match self.stream.fill_buf() {
            Ok(available) => String::from_utf8_lossy(available).to_string(),
            Err(_) => String::new(),
        }
    }

    fn read_i32(&mut self, val: &mut i32, basefield: Basefield) {
        if self.failed {
            return;
        }
        let text = self.integer_text();
        match extract_i32(&text, basefield) {
            None => self.failed = true,
            Some(extraction) => {
                self.stream.consume(extraction.consumed);
                *val = extraction.value as u32 as i32;
                if extraction.failed {
                    self.failed = true;
                }
            }
        }
    }

    fn read_u32(&mut self, val: &mut u32, basefield: Basefield) {
        if self.failed {
            return;
        }
        let text = self.integer_text();
        match extract_u32(&text, basefield) {
            None => self.failed = true,
            Some(extraction) => {
                self.stream.consume(extraction.consumed);
                *val = extraction.value as u32;
                if extraction.failed {
                    self.failed = true;
                }
            }
        }
    }
}

fn is_space(byte: u8) -> bool {
    matches!(byte, b' ' | b'\t' | b'\n' | 0x0b | 0x0c | b'\r')
}

fn is_alnum(tok: i32) -> bool {
    (0..128).contains(&tok) && (tok as u8).is_ascii_alphanumeric()
}

fn parse_toseparator_reader(reader: &mut StreamReader<'_>, name: &mut String) {
    name.clear();
    reader.skip_ws();
    let mut tok = reader.peek();
    while is_alnum(tok) || tok == b'_' as i32 {
        let mut byte = tok as u8;
        reader.read_char(&mut byte);
        name.push(byte as char);
        tok = reader.peek();
    }
}

pub fn parse_toseparator(reader_2: &mut dyn BufRead, name: &mut String) {
    let mut reader = StreamReader::new(reader_2);
    parse_toseparator_reader(&mut reader, name);
}

fn parse_machaddr_reader(
    reader: &mut StreamReader<'_>,
    defaultsize: &mut i32,
    glb: &Architecture,
    ignorecolon: bool,
) -> Result<Address> {
    let mut token = String::new();
    let mut size: i32 = -1;
    let manage = &glb.manager;
    reader.skip_ws();
    let peeked = reader.peek();
    let mut tok: u8 = peeked as u8;
    let space;
    if peeked == b'[' as i32 {
        reader.read_char(&mut tok);
        parse_toseparator_reader(reader, &mut token);
        space = match manage.get_space_by_name(&token) {
            Some(space) => space,
            None => return Err(Error::Parse("Bad address base".to_string())),
        };
        reader.read_char(&mut tok);
        if tok != b',' {
            return Err(Error::Parse("Missing ',' in address".to_string()));
        }
        parse_toseparator_reader(reader, &mut token);
        reader.read_char(&mut tok);
        if tok == b',' {
            reader.read_i32(&mut size, Basefield::Auto);
            reader.read_char(&mut tok);
        }
        if tok != b']' {
            return Err(Error::Parse("Missing ']' in address".to_string()));
        }
    } else if peeked == b'{' as i32 {
        space = match manage.get_join_space() {
            Some(space) => space,
            None => return Err(Error::Parse("Bad machine address".to_string())),
        };
        reader.read_char(&mut tok);
        reader.read_char(&mut tok);
        if tok != b'}' {
            return Err(Error::Parse("Bad machine address".to_string()));
        }
    } else {
        let found = if peeked == b'0' as i32 {
            manage.get_default_code_space()
        } else {
            let shortcut = manage.get_space_by_shortcut(peeked as u8 as char);
            reader.read_char(&mut tok);
            shortcut
        };
        space = match found {
            Some(space) => space,
            None => {
                reader.read_word(&mut token);
                let mut errmsg = String::from("Bad address: ");
                errmsg.push(tok as char);
                errmsg.push_str(&token);
                return Err(Error::Parse(errmsg));
            }
        };
        token.clear();
        reader.skip_ws();
        let mut current = reader.peek();
        loop {
            let accepted = is_alnum(current)
                || current == b'_' as i32
                || current == b'+' as i32
                || (!ignorecolon && current == b':' as i32);
            if !accepted {
                break;
            }
            token.push(current as u8 as char);
            reader.read_char(&mut tok);
            current = reader.peek();
        }
    }
    let mut res = Address::new(space, 0);
    let oversize = res.read(&token, manage, glb.translate.as_deref())?;
    if oversize == -1 {
        return Err(Error::Parse("Bad machine address".to_string()));
    }
    *defaultsize = if size == -1 { oversize } else { size };
    Ok(res)
}

pub fn parse_machaddr(
    reader_2: &mut dyn BufRead,
    defaultsize: &mut i32,
    glb: &Architecture,
    ignorecolon: bool,
) -> Result<Address> {
    let mut reader = StreamReader::new(reader_2);
    parse_machaddr_reader(&mut reader, defaultsize, glb, ignorecolon)
}

pub fn parse_varnode(
    reader_2: &mut dyn BufRead,
    size: &mut i32,
    pc: &mut Address,
    uq: &mut u32,
    glb: &Architecture,
) -> Result<Address> {
    let mut reader = StreamReader::new(reader_2);
    let mut discard: i32 = 0;
    let loc = parse_machaddr_reader(&mut reader, size, glb, false)?;
    let mut tok: u8 = 0;
    reader.read_char(&mut tok);
    if tok != b'(' {
        return Err(Error::Parse("Missing '('".to_string()));
    }
    reader.skip_ws();
    let peeked = reader.peek();
    *pc = Address::default();
    if peeked == b'i' as i32 {
        reader.read_char(&mut tok);
    } else if reader.peek() != b':' as i32 {
        *pc = parse_machaddr_reader(&mut reader, &mut discard, glb, true)?;
    }
    reader.skip_ws();
    if reader.peek() == b':' as i32 {
        reader.read_char(&mut tok);
        reader.skip_ws();
        reader.read_u32(uq, Basefield::Hex);
    } else {
        *uq = u32::MAX;
    }
    reader.read_char(&mut tok);
    if tok != b')' {
        return Err(Error::Parse("Missing ')'".to_string()));
    }
    Ok(loc)
}

pub fn parse_op(reader_2: &mut dyn BufRead, uq: &mut u32, glb: &Architecture) -> Result<Address> {
    let mut reader = StreamReader::new(reader_2);
    let mut size: i32 = 0;
    let loc = parse_machaddr_reader(&mut reader, &mut size, glb, true)?;
    let mut tok: u8 = 0;
    reader.read_char(&mut tok);
    if tok != b':' {
        return Err(Error::Parse("Missing ':'".to_string()));
    }
    reader.skip_ws();
    reader.read_u32(uq, Basefield::Hex);
    Ok(loc)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lex_all(input: &[u8]) -> Vec<(u32, TokenValue, i32, i32)> {
        let mut reader: &[u8] = input;
        let mut lexer = GrammarLexer::new(4096);
        lexer.push_file("stream", Box::new(&mut reader));
        let mut result = Vec::new();
        loop {
            let mut token = GrammarToken::new();
            lexer.get_next_token(&mut token).expect("lexer failure");
            let tp = token.get_type();
            result.push((tp, token.value.clone(), token.get_line_no(), token.get_col_no()));
            if tp == GrammarToken::ENDOFFILE || tp == GrammarToken::BADTOKEN || result.len() > 100 {
                break;
            }
        }
        result
    }

    #[test]
    fn lexer_produces_tokens() {
        let tokens = lex_all(b"int4 *foo(char a, ...);\n");
        let types: Vec<u32> = tokens.iter().map(|token| token.0).collect();
        assert_eq!(
            types,
            vec![
                GrammarToken::IDENTIFIER,
                GrammarToken::STAR,
                GrammarToken::IDENTIFIER,
                GrammarToken::OPENPAREN,
                GrammarToken::IDENTIFIER,
                GrammarToken::IDENTIFIER,
                GrammarToken::COMMA,
                GrammarToken::DOTDOTDOT,
                GrammarToken::CLOSEPAREN,
                GrammarToken::SEMICOLON,
                0,
                GrammarToken::ENDOFFILE,
            ]
        );
        assert_eq!(tokens[0].1, TokenValue::Text("int4".to_string()));
        assert_eq!(tokens[2].1, TokenValue::Text("foo".to_string()));
    }

    #[test]
    fn lexer_reads_numbers_and_scope() {
        let tokens = lex_all(b"0x1F -12 a::b");
        assert_eq!(tokens[0].0, GrammarToken::INTEGER);
        assert_eq!(tokens[0].1, TokenValue::Integer(31));
        assert_eq!(tokens[1].1, TokenValue::Integer((-12i64) as u64));
        assert_eq!(tokens[2].0, GrammarToken::IDENTIFIER);
        assert_eq!(tokens[3].0, GrammarToken::SCOPERES);
        assert_eq!(tokens[4].0, GrammarToken::IDENTIFIER);
    }

    #[test]
    fn lexer_reports_errors() {
        let tokens = lex_all(b"a $");
        assert_eq!(tokens.last().map(|token| token.0), Some(GrammarToken::BADTOKEN));
        let tokens = lex_all(b"\"abc");
        assert_eq!(tokens.last().map(|token| token.0), Some(GrammarToken::BADTOKEN));
        let tokens = lex_all(b"/* comment */ x // tail\ny");
        let types: Vec<u32> = tokens.iter().map(|token| token.0).collect();
        assert_eq!(
            types,
            vec![
                GrammarToken::IDENTIFIER,
                GrammarToken::IDENTIFIER,
                GrammarToken::ENDOFFILE
            ]
        );
        assert_eq!(tokens[1].2, 1);
    }

    #[test]
    fn lexer_line_too_long() {
        let mut reader: &[u8] = b"abcdefghij";
        let mut lexer = GrammarLexer::new(4);
        lexer.push_file("stream", Box::new(&mut reader));
        let mut token = GrammarToken::new();
        lexer.get_next_token(&mut token).expect("lexer failure");
        assert_eq!(token.get_type(), GrammarToken::BADTOKEN);
        assert_eq!(lexer.get_error(), "Line too long");
    }
}
