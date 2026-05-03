use hern_core::analysis::CompilerDiagnostic;
use std::fmt;
use std::io;

#[derive(Debug)]
pub enum ReplError {
    Io(io::Error),
    Lua(mlua::Error),
    Diagnostics(Vec<CompilerDiagnostic>),
    MissingAnalysis(&'static str),
}

impl fmt::Display for ReplError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReplError::Io(err) => write!(f, "{err}"),
            ReplError::Lua(err) => write!(f, "{err}"),
            ReplError::Diagnostics(diagnostics) => {
                for (idx, diagnostic) in diagnostics.iter().enumerate() {
                    if idx > 0 {
                        writeln!(f)?;
                    }
                    write!(f, "{diagnostic}")?;
                }
                Ok(())
            }
            ReplError::MissingAnalysis(message) => write!(f, "{message}"),
        }
    }
}

impl std::error::Error for ReplError {}

impl From<io::Error> for ReplError {
    fn from(err: io::Error) -> Self {
        Self::Io(err)
    }
}

impl From<mlua::Error> for ReplError {
    fn from(err: mlua::Error) -> Self {
        Self::Lua(err)
    }
}
