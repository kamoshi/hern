use crate::app::{App, EventAction, handle_event, startup_entries};
use crate::error::ReplError;
use crate::terminal_palette;
use crate::ui::{draw, insert_entries};
use crossterm::event::{
    KeyboardEnhancementFlags, PopKeyboardEnhancementFlags, PushKeyboardEnhancementFlags,
};
use crossterm::execute;
use crossterm::terminal::{disable_raw_mode, enable_raw_mode};
use ratatui::backend::CrosstermBackend;
use ratatui::{Terminal, TerminalOptions, Viewport};
use std::io;
use std::path::PathBuf;

// spacer(1) + status(1) + composer(1..3 inner +2 pad) + hint(1) + hint_spacer(1)
// + completions(3..1) + bottom_spacer(1) + footer(1) = always 12
const VIEWPORT_HEIGHT: u16 = 12;

type Result<T> = std::result::Result<T, ReplError>;

pub(crate) fn run(path: Option<PathBuf>) -> Result<()> {
    terminal_palette::warm_cache();
    let mut terminal = TerminalGuard::enter()?;
    let mut app = App::new(path.as_deref(), terminal.enhanced_keys)?;
    insert_entries(&mut terminal, startup_entries(path.as_deref()))?;

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
    pub(crate) enhanced_keys: bool,
}

impl TerminalGuard {
    fn enter() -> Result<Self> {
        enable_raw_mode()?;
        Self::enter_with_raw_mode().inspect_err(|_| {
            let _ = disable_raw_mode();
        })
    }

    fn enter_with_raw_mode() -> Result<Self> {
        let mut stdout = io::stdout();
        let _ = execute!(
            stdout,
            PushKeyboardEnhancementFlags(
                KeyboardEnhancementFlags::DISAMBIGUATE_ESCAPE_CODES
                    | KeyboardEnhancementFlags::REPORT_EVENT_TYPES
                    | KeyboardEnhancementFlags::REPORT_ALTERNATE_KEYS
            )
        );
        let backend = CrosstermBackend::new(stdout);
        let terminal = Terminal::with_options(
            backend,
            TerminalOptions {
                viewport: Viewport::Inline(VIEWPORT_HEIGHT),
            },
        )?;
        Ok(Self { terminal, enhanced_keys: true })
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
        let _ = execute!(self.terminal.backend_mut(), PopKeyboardEnhancementFlags);
        let _ = self.terminal.show_cursor();
        let _ = disable_raw_mode();
    }
}
