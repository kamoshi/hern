use crate::app::{App, EventAction, handle_event, startup_entries};
use crate::error::ReplError;
use crate::ui::{draw, insert_entries};
use crossterm::event::{
    KeyboardEnhancementFlags, PopKeyboardEnhancementFlags, PushKeyboardEnhancementFlags,
};
use crossterm::execute;
use crossterm::terminal::{disable_raw_mode, enable_raw_mode};
use ratatui::backend::CrosstermBackend;
use ratatui::{Terminal, TerminalOptions, Viewport};
use std::io;

const VIEWPORT_HEIGHT: u16 = 12;

type Result<T> = std::result::Result<T, ReplError>;

pub(crate) fn run() -> Result<()> {
    let mut terminal = TerminalGuard::enter()?;
    let mut app = App::new()?;
    insert_entries(&mut terminal, startup_entries())?;

    loop {
        terminal.draw(|frame| draw(frame, &app))?;
        match handle_event(&mut app)? {
            EventAction::Continue => {}
            EventAction::Commit(entries) => insert_entries(&mut terminal, entries)?,
            EventAction::Exit => break,
        }
    }

    Ok(())
}

pub(crate) struct TerminalGuard {
    terminal: Terminal<CrosstermBackend<io::Stdout>>,
}

impl TerminalGuard {
    fn enter() -> Result<Self> {
        enable_raw_mode()?;
        let mut stdout = io::stdout();
        let _ = execute!(
            stdout,
            PushKeyboardEnhancementFlags(
                KeyboardEnhancementFlags::DISAMBIGUATE_ESCAPE_CODES
                    | KeyboardEnhancementFlags::REPORT_EVENT_TYPES
                    | KeyboardEnhancementFlags::REPORT_ALTERNATE_KEYS
                    | KeyboardEnhancementFlags::REPORT_ALL_KEYS_AS_ESCAPE_CODES
            )
        );
        let backend = CrosstermBackend::new(stdout);
        let terminal = Terminal::with_options(
            backend,
            TerminalOptions {
                viewport: Viewport::Inline(VIEWPORT_HEIGHT),
            },
        )?;
        Ok(Self { terminal })
    }
}

impl std::ops::Deref for TerminalGuard {
    type Target = Terminal<CrosstermBackend<io::Stdout>>;

    fn deref(&self) -> &Self::Target {
        &self.terminal
    }
}

impl std::ops::DerefMut for TerminalGuard {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.terminal
    }
}

impl Drop for TerminalGuard {
    fn drop(&mut self) {
        let _ = disable_raw_mode();
        let _ = execute!(self.terminal.backend_mut(), PopKeyboardEnhancementFlags);
        let _ = self.terminal.show_cursor();
    }
}
