use crate::app::{App, EventAction, handle_event, startup_entries};
use crate::error::ReplError;
use crate::terminal_palette;
use crate::ui::{VIEWPORT_HEIGHT, draw, insert_entries};
use crossterm::event::{
    KeyboardEnhancementFlags, PopKeyboardEnhancementFlags, PushKeyboardEnhancementFlags,
};
use crossterm::execute;
use crossterm::terminal::{disable_raw_mode, enable_raw_mode};
use ratatui::backend::CrosstermBackend;
use ratatui::{Terminal, TerminalOptions, Viewport};
use std::io;
use std::path::PathBuf;

type Result<T> = std::result::Result<T, ReplError>;

pub(crate) fn run(path: Option<PathBuf>) -> Result<()> {
    terminal_palette::warm_cache();
    let mut terminal = TerminalGuard::enter()?;
    let mut app = App::new(path.as_deref())?;
    let keyboard_enhancement_error = terminal.keyboard_enhancement_error.clone();
    insert_entries(
        &mut terminal,
        startup_entries(path.as_deref(), keyboard_enhancement_error.as_deref()),
    )?;

    loop {
        app.update_hints();
        terminal.draw(|frame| draw(frame, &app))?;
        match handle_event(&mut app)? {
            EventAction::Continue => {}
            EventAction::Commit(entries) => {
                insert_entries(&mut terminal, entries)?;
                app.mark_hints_dirty();
            }
            EventAction::Exit => break,
        }
    }

    // The inline viewport is only a transient composer surface; committed
    // entries have already been inserted into scrollback.
    terminal.clear()?;
    Ok(())
}

pub(crate) struct TerminalGuard {
    terminal: Terminal<CrosstermBackend<io::Stdout>>,
    keyboard_enhancements_pushed: bool,
    keyboard_enhancement_error: Option<String>,
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
        let keyboard_enhancement_result = execute!(
            stdout,
            PushKeyboardEnhancementFlags(
                KeyboardEnhancementFlags::DISAMBIGUATE_ESCAPE_CODES
                    | KeyboardEnhancementFlags::REPORT_EVENT_TYPES
                    | KeyboardEnhancementFlags::REPORT_ALTERNATE_KEYS
            )
        );
        let keyboard_enhancements_pushed = keyboard_enhancement_result.is_ok();
        let keyboard_enhancement_error =
            keyboard_enhancement_result.err().map(|err| err.to_string());
        let backend = CrosstermBackend::new(stdout);
        let terminal = Terminal::with_options(
            backend,
            TerminalOptions {
                viewport: Viewport::Inline(VIEWPORT_HEIGHT),
            },
        )?;
        Ok(Self {
            terminal,
            keyboard_enhancements_pushed,
            keyboard_enhancement_error,
        })
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
        if self.keyboard_enhancements_pushed {
            let _ = execute!(self.terminal.backend_mut(), PopKeyboardEnhancementFlags);
        }
        let _ = self.terminal.show_cursor();
        let _ = disable_raw_mode();
    }
}
