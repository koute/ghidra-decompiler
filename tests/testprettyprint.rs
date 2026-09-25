use std::path::PathBuf;

use ghidra_decompiler::error::{Error, Result};
use ghidra_decompiler::prettyprint::{BraceStyle, Emit, EmitPrettyPrint, SyntaxHighlight};

fn unescape(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut result = String::new();
    let mut pos = 0;
    while pos < bytes.len() {
        if bytes[pos] == b'\\' && pos + 1 < bytes.len() {
            pos += 1;
            match bytes[pos] {
                b's' => result.push(' '),
                b'n' => result.push('\n'),
                other => result.push(other as char),
            }
        } else {
            result.push(bytes[pos] as char);
        }
        pos += 1;
    }
    result
}

fn highlight(value: &str) -> SyntaxHighlight {
    match value.parse::<i32>().expect("invalid highlight") {
        0 => SyntaxHighlight::KeywordColor,
        1 => SyntaxHighlight::CommentColor,
        2 => SyntaxHighlight::TypeColor,
        3 => SyntaxHighlight::FuncnameColor,
        4 => SyntaxHighlight::VarColor,
        5 => SyntaxHighlight::ConstColor,
        6 => SyntaxHighlight::ParamColor,
        7 => SyntaxHighlight::GlobalColor,
        8 => SyntaxHighlight::NoColor,
        9 => SyntaxHighlight::ErrorColor,
        _ => SyntaxHighlight::SpecialColor,
    }
}

fn brace_style(value: &str) -> BraceStyle {
    match value {
        "0" => BraceStyle::SameLine,
        "1" => BraceStyle::NextLine,
        _ => BraceStyle::SkipLine,
    }
}

struct Session {
    emit: EmitPrettyPrint,
    ids: Vec<i32>,
}

impl Session {
    fn run(&mut self, fields: &[&str], output: &mut Vec<u8>) -> Result<()> {
        let emit = &mut self.emit;
        match fields[0] {
            "P" => emit.print(&unescape(fields[2]), highlight(fields[1]))?,
            "V" => emit.tag_variable(&unescape(fields[2]), highlight(fields[1]), None, None)?,
            "T" => emit.tag_op(&unescape(fields[2]), highlight(fields[1]), None)?,
            "K" => emit.tag_case_label(
                &unescape(fields[3]),
                highlight(fields[1]),
                None,
                fields[2].parse().expect("invalid case value"),
            )?,
            "S" => emit.spaces(
                fields[1].parse().expect("invalid count"),
                fields[2].parse().expect("invalid bump"),
            )?,
            "L" => emit.tag_line()?,
            "LI" => emit.tag_line_indent(fields[1].parse().expect("invalid indent"))?,
            "OP" => {
                let id = emit.open_paren(&unescape(fields[1]), 0)?;
                self.ids.push(id);
            }
            "CP" => {
                let id = self.ids.pop().expect("missing id");
                emit.close_paren(&unescape(fields[1]), id)?;
            }
            "OG" => {
                let id = emit.open_group()?;
                self.ids.push(id);
            }
            "CG" => {
                let id = self.ids.pop().expect("missing id");
                emit.close_group(id)?;
            }
            "SI" => {
                let id = emit.start_indent()?;
                self.ids.push(id);
            }
            "EI" => {
                let id = self.ids.pop().expect("missing id");
                emit.stop_indent(id)?;
            }
            "SC" => {
                let id = emit.start_comment()?;
                self.ids.push(id);
            }
            "EC" => {
                let id = self.ids.pop().expect("missing id");
                emit.stop_comment(id)?;
            }
            "BS" => {
                let id = emit.begin_statement(None)?;
                self.ids.push(id);
            }
            "ES" => {
                let id = self.ids.pop().expect("missing id");
                emit.end_statement(id)?;
            }
            "BP" => {
                let id = emit.begin_func_proto()?;
                self.ids.push(id);
            }
            "EP" => {
                let id = self.ids.pop().expect("missing id");
                emit.end_func_proto(id)?;
            }
            "BD" => {
                let id = emit.begin_document()?;
                self.ids.push(id);
            }
            "ED" => {
                let id = self.ids.pop().expect("missing id");
                emit.end_document(id)?;
            }
            "BR" => {
                let id = emit.begin_return_type(None)?;
                self.ids.push(id);
            }
            "ER" => {
                let id = self.ids.pop().expect("missing id");
                emit.end_return_type(id)?;
            }
            "OB" => emit.open_brace(&unescape(fields[2]), brace_style(fields[1]))?,
            "OBI" => {
                let id = emit.open_brace_indent(&unescape(fields[2]), brace_style(fields[1]))?;
                self.ids.push(id);
            }
            "CBI" => {
                let id = self.ids.pop().expect("missing id");
                emit.close_brace_indent(&unescape(fields[1]), id)?;
            }
            "FILL" => emit.set_comment_fill(&unescape(fields[1])),
            "INC" => emit.set_indent_increment(fields[1].parse().expect("invalid increment")),
            "F" => {
                emit.flush()?;
                let result = emit.get_output_stream().clone();
                output.extend_from_slice(format!("OUT {}\n", result.len()).as_bytes());
                output.extend_from_slice(&result);
                output.extend_from_slice(b"\nEND\n");
            }
            other => panic!("unknown command {}", other),
        }
        Ok(())
    }
}

fn data_path(name: &str) -> PathBuf {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.push("tests");
    path.push("prettyprint_data");
    path.push(name);
    path
}

#[test]
fn prettyprint_matches_reference() {
    let cases_path = std::env::var("PRETTY_CASES")
        .map(PathBuf::from)
        .unwrap_or_else(|_| data_path("cases.txt"));
    let expected_path = std::env::var("PRETTY_EXPECTED")
        .map(PathBuf::from)
        .unwrap_or_else(|_| data_path("expected.txt"));
    let cases = std::fs::read_to_string(cases_path).expect("missing prettyprint cases");
    let expected = std::fs::read(expected_path).expect("missing prettyprint expected output");
    let mut output: Vec<u8> = Vec::new();
    let mut session: Option<Session> = None;
    for line in cases.lines() {
        let fields: Vec<&str> = line.split(' ').filter(|field| !field.is_empty()).collect();
        if fields.is_empty() {
            continue;
        }
        if fields[0] == "C" {
            let mut emit = EmitPrettyPrint::new();
            emit.set_output_stream(Vec::new());
            if fields[2] != "0" {
                emit.set_markup(true);
                emit.set_packed_output(fields[3] != "0");
            }
            let mut next = Session { emit, ids: Vec::new() };
            match next
                .emit
                .set_max_line_size(fields[1].parse().expect("invalid line size"))
            {
                Ok(()) => session = Some(next),
                Err(err) => {
                    output.extend_from_slice(format!("ERR {}\nEND\n", explain(&err)).as_bytes());
                    session = None;
                }
            }
            continue;
        }
        let Some(current) = session.as_mut() else {
            continue;
        };
        if let Err(err) = current.run(&fields, &mut output) {
            output.extend_from_slice(format!("ERR {}\nEND\n", explain(&err)).as_bytes());
            session = None;
        }
    }
    if output != expected {
        let position = output
            .iter()
            .zip(expected.iter())
            .position(|(left, right)| left != right)
            .unwrap_or(0);
        let start = position.saturating_sub(200);
        panic!(
            "prettyprint output differs at byte {}\nexpected: {:?}\nactual: {:?}",
            position,
            String::from_utf8_lossy(&expected[start..(position + 200).min(expected.len())]),
            String::from_utf8_lossy(&output[start..(position + 200).min(output.len())])
        );
    }
}

fn explain(err: &Error) -> String {
    match err {
        Error::Lowlevel(msg) => msg.clone(),
        other => format!("{:?}", other),
    }
}
