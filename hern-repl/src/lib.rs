mod app;
mod color;
mod error;
mod highlight;
mod session;
mod style;
mod terminal;
mod terminal_palette;
mod ui;

pub use error::ReplError;
use std::path::PathBuf;

pub fn run() -> Result<(), ReplError> {
    terminal::run(None)
}

pub fn run_with_path(path: PathBuf) -> Result<(), ReplError> {
    terminal::run(Some(path))
}
