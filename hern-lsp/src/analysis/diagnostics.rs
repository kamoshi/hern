use super::uri::{path_to_uri, source_span_to_range};
use hern_core::analysis::{
    CompilerDiagnostic, DiagnosticSeverity as CoreDiagnosticSeverity, DiagnosticSource,
};
use lsp_types::{Diagnostic, DiagnosticSeverity, Position, Range, Uri};
use std::collections::HashMap;

pub(crate) type DiagnosticsByUri = HashMap<Uri, Vec<Diagnostic>>;

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub(super) struct DiagnosticIdentity {
    start_line: u32,
    start_character: u32,
    end_line: u32,
    end_character: u32,
    severity: Option<u8>,
    message: String,
}

pub(super) fn diagnostics_from_compiler_diagnostics(
    entry_uri: &Uri,
    diagnostics: Vec<CompilerDiagnostic>,
) -> DiagnosticsByUri {
    let mut by_uri = DiagnosticsByUri::new();
    by_uri.insert(entry_uri.clone(), Vec::new());
    for diagnostic in diagnostics {
        let uri = diagnostic_source_uri(&diagnostic).unwrap_or_else(|| entry_uri.clone());
        by_uri
            .entry(uri)
            .or_default()
            .push(compiler_diagnostic_to_lsp(diagnostic));
    }
    by_uri
}

pub(super) fn diagnostic_identity(diagnostic: &Diagnostic) -> DiagnosticIdentity {
    let r = &diagnostic.range;
    DiagnosticIdentity {
        start_line: r.start.line,
        start_character: r.start.character,
        end_line: r.end.line,
        end_character: r.end.character,
        severity: diagnostic.severity.map(diagnostic_severity_key),
        message: diagnostic.message.clone(),
    }
}

fn diagnostic_severity_key(severity: DiagnosticSeverity) -> u8 {
    match severity {
        DiagnosticSeverity::ERROR => 1,
        DiagnosticSeverity::WARNING => 2,
        DiagnosticSeverity::INFORMATION => 3,
        DiagnosticSeverity::HINT => 4,
        _ => 0,
    }
}

fn compiler_diagnostic_to_lsp(diagnostic: CompilerDiagnostic) -> Diagnostic {
    let range = diagnostic
        .span
        .map(source_span_to_range)
        .unwrap_or_else(|| Range::new(Position::new(0, 0), Position::new(0, 1)));
    Diagnostic {
        range,
        severity: Some(match diagnostic.severity {
            CoreDiagnosticSeverity::Error => DiagnosticSeverity::ERROR,
        }),
        message: diagnostic.message,
        source: Some("hern".to_string()),
        ..Default::default()
    }
}

fn diagnostic_source_uri(diagnostic: &CompilerDiagnostic) -> Option<Uri> {
    let DiagnosticSource::Path(path) = diagnostic.source.as_ref()? else {
        return None;
    };
    path_to_uri(path)
}
