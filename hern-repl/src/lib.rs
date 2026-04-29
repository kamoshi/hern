mod app;
mod error;
mod highlight;
mod session;
mod terminal;
mod ui;

pub use error::ReplError;

pub fn run() -> Result<(), ReplError> {
    terminal::run()
}
