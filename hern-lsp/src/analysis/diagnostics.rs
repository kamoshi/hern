use super::uri::{path_to_uri, source_span_to_range};
use hern_core::analysis::{
    CompilerDiagnostic, DiagnosticSeverity as CoreDiagnosticSeverity, DiagnosticSource,
};
use lsp_types::{Diagnostic, DiagnosticSeverity, Position, Range, Uri};
use std::collections::HashMap;

pub(crate) type DiagnosticsByUri = HashMap<Uri, Vec<Diagnostic>>;

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

pub(super) fn diagnostic_identity(diagnostic: &Diagnostic) -> String {
    let r = &diagnostic.range;
    format!(
        "{},{},{},{},{:?}:{}",
        r.start.line,
        r.start.character,
        r.end.line,
        r.end.character,
        diagnostic.severity,
        diagnostic.message
    )
}

fn compiler_diagnostic_to_lsp(diagnostic: CompilerDiagnostic) -> Diagnostic {
    let range = diagnostic
        .span
        .map(source_span_to_range)
        .unwrap_or_else(|| Range::new(Position::new(0, 0), Position::new(0, 0)));
    Diagnostic {
        range,
        severity: Some(match diagnostic.severity {
            CoreDiagnosticSeverity::Error => DiagnosticSeverity::ERROR,
        }),
        message: diagnostic.message,
        ..Default::default()
    }
}

fn diagnostic_source_uri(diagnostic: &CompilerDiagnostic) -> Option<Uri> {
    let DiagnosticSource::Path(path) = diagnostic.source.as_ref()? else {
        return None;
    };
    path_to_uri(path)
}
