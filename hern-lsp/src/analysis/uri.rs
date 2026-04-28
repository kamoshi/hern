use lsp_types::{Position, Range, Uri};
use std::path::{Path, PathBuf};
use std::str::FromStr;

pub(super) fn uri_to_path(uri: &Uri) -> Option<PathBuf> {
    if !uri.scheme()?.as_str().eq_ignore_ascii_case("file") {
        return None;
    }
    let path = percent_decode(uri.path().as_str())?;
    Some(PathBuf::from(path))
}

pub(super) fn path_to_uri(path: &Path) -> Option<Uri> {
    Uri::from_str(&format!("file://{}", percent_encode_path(path))).ok()
}

pub(super) fn source_span_to_range(span: hern_core::ast::SourceSpan) -> Range {
    Range::new(
        span_to_position(span.start_line, span.start_col),
        span_to_position(span.end_line, span.end_col),
    )
}

fn span_to_position(line: usize, col: usize) -> Position {
    Position::new(line.saturating_sub(1) as u32, col.saturating_sub(1) as u32)
}

fn percent_decode(value: &str) -> Option<String> {
    let bytes = value.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut idx = 0;
    while idx < bytes.len() {
        if bytes[idx] == b'%' {
            let hi = *bytes.get(idx + 1)?;
            let lo = *bytes.get(idx + 2)?;
            out.push(hex_val(hi)? << 4 | hex_val(lo)?);
            idx += 3;
        } else {
            out.push(bytes[idx]);
            idx += 1;
        }
    }
    String::from_utf8(out).ok()
}

fn hex_val(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

fn percent_encode_path(path: &Path) -> String {
    let path = path.to_string_lossy();
    let mut out = String::with_capacity(path.len());
    for byte in path.bytes() {
        match byte {
            b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'-' | b'.' | b'_' | b'~' | b'/' => {
                out.push(byte as char)
            }
            _ => out.push_str(&format!("%{byte:02X}")),
        }
    }
    out
}
