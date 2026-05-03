use crate::error::ReplError;
use crate::session::{BindingInfo, ReplSession};
use crossterm::event::{self, Event, KeyCode, KeyEvent, KeyEventKind, KeyModifiers};
use std::path::Path;

type Result<T> = std::result::Result<T, ReplError>;

#[derive(Clone)]
pub(crate) struct Entry {
    pub(crate) kind: EntryKind,
    pub(crate) text: String,
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(crate) enum EntryKind {
    Input,
    Output,
    Error,
    Info,
}

pub(crate) struct App {
    pub(crate) input: String,
    pub(crate) cursor: usize,
    pub(crate) enhanced_keys: bool,
    session: ReplSession,
    history: Vec<String>,
    history_cursor: Option<usize>,
    draft_before_history: String,
    pub(crate) bindings_overlay: BindingsOverlay,
}

#[derive(Default)]
pub(crate) struct BindingsOverlay {
    pub(crate) open: bool,
    pub(crate) query: String,
    pub(crate) selected: usize,
}

pub(crate) enum EventAction {
    Continue,
    Commit(Vec<Entry>),
    Exit,
}

impl App {
    pub(crate) fn new(path: Option<&Path>, enhanced_keys: bool) -> Result<Self> {
        Ok(Self {
            input: String::new(),
            cursor: 0,
            enhanced_keys,
            session: ReplSession::new(path)?,
            history: Vec::new(),
            history_cursor: None,
            draft_before_history: String::new(),
            bindings_overlay: BindingsOverlay::default(),
        })
    }

    pub(crate) fn type_hint(&self) -> Option<String> {
        self.session.type_hint(&self.input)
    }

    pub(crate) fn filtered_bindings(&self) -> Vec<BindingInfo> {
        let query = self.bindings_overlay.query.trim().to_lowercase();
        let mut bindings = self.session.bindings();
        if !query.is_empty() {
            bindings.retain(|binding| {
                binding.name.to_lowercase().contains(&query)
                    || binding.ty.to_lowercase().contains(&query)
            });
        }
        bindings
    }

    pub(crate) fn completion_items(&self) -> Vec<BindingInfo> {
        if let Some((base, prefix)) = member_completion_context(&self.input, self.cursor) {
            return self
                .session
                .member_bindings(base, prefix)
                .into_iter()
                .take(8)
                .collect();
        }

        let prefix = current_word(&self.input, self.cursor).trim();
        if prefix.is_empty() {
            return Vec::new();
        }

        let mut scored: Vec<_> = self
            .session
            .bindings()
            .into_iter()
            .filter_map(|binding| completion_score(&binding, prefix).map(|score| (score, binding)))
            .collect();
        scored.sort_by(|(left_score, left), (right_score, right)| {
            left_score
                .cmp(right_score)
                .then_with(|| left.name.cmp(&right.name))
        });
        scored
            .into_iter()
            .map(|(_, binding)| binding)
            .take(8)
            .collect()
    }

    fn submit(&mut self) -> Vec<Entry> {
        let source = self.input.trim().to_string();
        if source.is_empty() {
            self.input.clear();
            self.cursor = 0;
            return Vec::new();
        }

        self.history.push(source.clone());
        self.history_cursor = None;
        self.draft_before_history.clear();

        let mut entries = vec![Entry {
            kind: EntryKind::Input,
            text: source.clone(),
        }];

        match self.session.eval(&source) {
            Ok(out) if out.trim().is_empty() => {
                entries.push(Entry {
                    kind: EntryKind::Output,
                    text: "ok".to_string(),
                });
            }
            Ok(out) => {
                entries.push(Entry {
                    kind: EntryKind::Output,
                    text: out.trim_end().to_string(),
                });
            }
            Err(err) => {
                entries.push(Entry {
                    kind: EntryKind::Error,
                    text: err.to_string(),
                });
            }
        }

        self.input.clear();
        self.cursor = 0;
        entries
    }

    fn insert_newline(&mut self) {
        self.cursor = clamp_to_char_boundary(&self.input, self.cursor);
        self.input.insert(self.cursor, '\n');
        self.cursor += 1;
        self.history_cursor = None;
    }

    fn insert_char(&mut self, ch: char) {
        self.cursor = clamp_to_char_boundary(&self.input, self.cursor);
        self.input.insert(self.cursor, ch);
        self.cursor += ch.len_utf8();
        self.history_cursor = None;
    }

    fn recall_older(&mut self) {
        if self.history.is_empty() {
            return;
        }
        let next = match self.history_cursor {
            None => {
                self.draft_before_history = self.input.clone();
                self.history.len() - 1
            }
            Some(0) => 0,
            Some(idx) => idx - 1,
        };
        self.apply_history_index(next);
    }

    fn recall_newer(&mut self) {
        let Some(idx) = self.history_cursor else {
            return;
        };
        if idx + 1 >= self.history.len() {
            self.history_cursor = None;
            self.input = self.draft_before_history.clone();
            self.cursor = self.input.len();
            return;
        }
        self.apply_history_index(idx + 1);
    }

    fn apply_history_index(&mut self, idx: usize) {
        self.history_cursor = Some(idx);
        self.input = self.history[idx].clone();
        self.cursor = self.input.len();
    }

    fn toggle_bindings_overlay(&mut self) {
        self.bindings_overlay.open = !self.bindings_overlay.open;
        if self.bindings_overlay.open {
            self.bindings_overlay.query = current_word(&self.input, self.cursor).to_string();
            self.bindings_overlay.selected = 0;
        }
    }

    fn close_bindings_overlay(&mut self) {
        self.bindings_overlay.open = false;
    }

    fn insert_binding(&mut self, name: &str) {
        let (start, end) = current_word_range(&self.input, self.cursor);
        self.input.replace_range(start..end, name);
        self.cursor = start + name.len();
        self.bindings_overlay.open = false;
        self.history_cursor = None;
    }
}

pub(crate) fn handle_event(app: &mut App) -> Result<EventAction> {
    let event = event::read()?;
    // Resize events are handled implicitly: the draw loop redraws with the new
    // terminal dimensions on every iteration, so no explicit action is needed.
    let Event::Key(KeyEvent {
        code,
        modifiers,
        kind,
        ..
    }) = event
    else {
        return Ok(EventAction::Continue);
    };
    if !matches!(kind, KeyEventKind::Press | KeyEventKind::Repeat) {
        return Ok(EventAction::Continue);
    }

    Ok(if app.bindings_overlay.open {
        handle_bindings_key(app, code, modifiers)
    } else {
        handle_key(app, code, modifiers)
    })
}

fn handle_bindings_key(app: &mut App, code: KeyCode, modifiers: KeyModifiers) -> EventAction {
    match (code, modifiers) {
        (KeyCode::Char('c' | 'd'), modifiers) if modifiers.contains(KeyModifiers::CONTROL) => {
            EventAction::Exit
        }
        (KeyCode::Char('t'), modifiers) if modifiers.contains(KeyModifiers::CONTROL) => {
            app.toggle_bindings_overlay();
            EventAction::Continue
        }
        (KeyCode::Esc, _) => {
            app.close_bindings_overlay();
            EventAction::Continue
        }
        (KeyCode::Enter, _) => {
            let bindings = app.filtered_bindings();
            let selected = app
                .bindings_overlay
                .selected
                .min(bindings.len().saturating_sub(1));
            if let Some(binding) = bindings.get(selected).cloned() {
                app.insert_binding(&binding.name);
            } else {
                app.close_bindings_overlay();
            }
            EventAction::Continue
        }
        (KeyCode::Backspace, _) => {
            app.bindings_overlay.query.pop();
            app.bindings_overlay.selected = 0;
            EventAction::Continue
        }
        (KeyCode::Up, _) => {
            app.bindings_overlay.selected = app.bindings_overlay.selected.saturating_sub(1);
            EventAction::Continue
        }
        (KeyCode::Down, _) => {
            let max = app.filtered_bindings().len().saturating_sub(1);
            app.bindings_overlay.selected = (app.bindings_overlay.selected + 1).min(max);
            EventAction::Continue
        }
        (KeyCode::PageUp, _) => {
            app.bindings_overlay.selected = app.bindings_overlay.selected.saturating_sub(8);
            EventAction::Continue
        }
        (KeyCode::PageDown, _) => {
            let max = app.filtered_bindings().len().saturating_sub(1);
            app.bindings_overlay.selected = (app.bindings_overlay.selected + 8).min(max);
            EventAction::Continue
        }
        (KeyCode::Char(ch), KeyModifiers::NONE | KeyModifiers::SHIFT) => {
            if !ch.is_ascii_control() {
                app.bindings_overlay.query.push(ch);
                app.bindings_overlay.selected = 0;
            }
            EventAction::Continue
        }
        _ => EventAction::Continue,
    }
}

fn handle_key(app: &mut App, code: KeyCode, modifiers: KeyModifiers) -> EventAction {
    match (code, modifiers) {
        (KeyCode::Char('c' | 'd'), modifiers) if modifiers.contains(KeyModifiers::CONTROL) => {
            EventAction::Exit
        }
        (KeyCode::Char('t'), modifiers) if modifiers.contains(KeyModifiers::CONTROL) => {
            app.toggle_bindings_overlay();
            EventAction::Continue
        }
        (KeyCode::Char('j'), KeyModifiers::CONTROL) | (KeyCode::Char('\n' | '\r'), _) => {
            app.insert_newline();
            EventAction::Continue
        }
        (KeyCode::Enter, modifiers) if modifiers.contains(KeyModifiers::SHIFT) => {
            app.insert_newline();
            EventAction::Continue
        }
        (KeyCode::Enter, _) => EventAction::Commit(app.submit()),
        (KeyCode::Backspace, _) => {
            if app.cursor > 0 {
                let cursor = clamp_to_char_boundary(&app.input, app.cursor);
                let prev = previous_char_boundary(&app.input, cursor);
                app.input.replace_range(prev..cursor, "");
                app.cursor = prev;
            }
            app.history_cursor = None;
            EventAction::Continue
        }
        (KeyCode::Delete, _) => {
            let cursor = clamp_to_char_boundary(&app.input, app.cursor);
            if cursor < app.input.len() {
                let next = next_char_boundary(&app.input, cursor);
                app.input.replace_range(cursor..next, "");
                app.cursor = cursor;
            }
            app.history_cursor = None;
            EventAction::Continue
        }
        (KeyCode::Up, _) => {
            app.recall_older();
            EventAction::Continue
        }
        (KeyCode::Down, _) => {
            app.recall_newer();
            EventAction::Continue
        }
        (KeyCode::Left, _) => {
            app.cursor = previous_char_boundary(&app.input, app.cursor);
            EventAction::Continue
        }
        (KeyCode::Right, _) => {
            app.cursor = next_char_boundary(&app.input, app.cursor);
            EventAction::Continue
        }
        (KeyCode::Home, _) => {
            app.cursor = 0;
            EventAction::Continue
        }
        (KeyCode::End, _) => {
            app.cursor = app.input.len();
            EventAction::Continue
        }
        (KeyCode::Char(ch), KeyModifiers::NONE | KeyModifiers::SHIFT) => {
            app.insert_char(ch);
            EventAction::Continue
        }
        _ => EventAction::Continue,
    }
}

fn current_word(input: &str, cursor: usize) -> &str {
    let (start, end) = current_word_range(input, cursor);
    &input[start..end]
}

fn current_word_range(input: &str, cursor: usize) -> (usize, usize) {
    let cursor = clamp_to_char_boundary(input, cursor);
    let start = input[..cursor]
        .rfind(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_'))
        .map(|idx| idx + 1)
        .unwrap_or(0);
    let end = input[cursor..]
        .find(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_'))
        .map(|idx| cursor + idx)
        .unwrap_or(input.len());
    (start, end)
}

fn member_completion_context(input: &str, cursor: usize) -> Option<(&str, &str)> {
    let cursor = clamp_to_char_boundary(input, cursor);
    let token_start = input[..cursor]
        .rfind(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_' || ch == '.'))
        .map(|idx| idx + 1)
        .unwrap_or(0);
    let token = &input[token_start..cursor];
    let dot = token.rfind('.')?;
    let base = &token[..dot];
    let prefix = &token[dot + 1..];
    if base.is_empty()
        || base.contains('.')
        || !base
            .chars()
            .all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
        || !prefix
            .chars()
            .all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
    {
        return None;
    }
    Some((base, prefix))
}

fn clamp_to_char_boundary(input: &str, cursor: usize) -> usize {
    let mut cursor = cursor.min(input.len());
    while cursor > 0 && !input.is_char_boundary(cursor) {
        cursor -= 1;
    }
    cursor
}

fn previous_char_boundary(input: &str, cursor: usize) -> usize {
    let cursor = clamp_to_char_boundary(input, cursor);
    input[..cursor]
        .char_indices()
        .last()
        .map(|(idx, _)| idx)
        .unwrap_or(0)
}

fn next_char_boundary(input: &str, cursor: usize) -> usize {
    let cursor = clamp_to_char_boundary(input, cursor);
    if cursor >= input.len() {
        return input.len();
    }
    input[cursor..]
        .char_indices()
        .nth(1)
        .map(|(idx, _)| cursor + idx)
        .unwrap_or(input.len())
}

fn completion_score(binding: &BindingInfo, prefix: &str) -> Option<(u8, usize)> {
    let name = binding.name.to_lowercase();
    let prefix = prefix.to_lowercase();
    if name.starts_with(&prefix) {
        Some((0, binding.name.len()))
    } else if name.contains(&prefix) {
        Some((1, binding.name.len()))
    } else {
        None
    }
}

pub(crate) fn startup_entries(path: Option<&Path>) -> Vec<Entry> {
    let mut entries = vec![Entry {
        kind: EntryKind::Info,
        text: "Hern REPL. Enter evaluates, Shift+Enter inserts a newline, Up/Down browse history, Ctrl-D exits.".to_string(),
    }];
    if let Some(path) = path {
        entries.push(Entry {
            kind: EntryKind::Info,
            text: format!("Loaded {}", path.display()),
        });
    }
    entries
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_newline_preserves_cursor_position() {
        let mut app = App::new(None, false).expect("app should initialize");
        app.insert_char('a');
        app.insert_char('c');
        app.cursor = 1;
        app.insert_newline();

        assert_eq!(app.input, "a\nc");
        assert_eq!(app.cursor, 2);
    }

    #[test]
    fn history_navigation_restores_draft_after_newest_entry() {
        let mut app = App::new(None, false).expect("app should initialize");
        app.history.push("let x = 1".to_string());
        app.history.push("x + 1".to_string());
        app.input = "dra".to_string();
        app.cursor = app.input.len();

        app.recall_older();
        assert_eq!(app.input, "x + 1");
        app.recall_older();
        assert_eq!(app.input, "let x = 1");
        app.recall_newer();
        assert_eq!(app.input, "x + 1");
        app.recall_newer();
        assert_eq!(app.input, "dra");
        assert_eq!(app.cursor, 3);
    }

    #[test]
    fn shift_enter_with_extra_modifiers_inserts_newline() {
        let mut app = App::new(None, false).expect("app should initialize");
        app.insert_char('a');

        let action = handle_key(
            &mut app,
            KeyCode::Enter,
            KeyModifiers::SHIFT | KeyModifiers::CONTROL,
        );

        assert!(matches!(action, EventAction::Continue));
        assert_eq!(app.input, "a\n");
    }

    #[test]
    fn current_word_range_finds_identifier_around_cursor() {
        assert_eq!(current_word("foo + bar", 7), "bar");
        assert_eq!(current_word_range("foo + bar", 7), (6, 9));
    }

    #[test]
    fn completion_score_prefers_prefix_matches() {
        let math = BindingInfo {
            name: "math".to_string(),
            ty: "module".to_string(),
        };
        let format = BindingInfo {
            name: "format".to_string(),
            ty: "fn".to_string(),
        };

        assert!(completion_score(&math, "ma") < completion_score(&format, "ma"));
        assert_eq!(completion_score(&math, "zz"), None);
    }

    #[test]
    fn member_completion_context_detects_dot_prefix() {
        assert_eq!(member_completion_context("math.", 5), Some(("math", "")));
        assert_eq!(
            member_completion_context("1 + math.si", 11),
            Some(("math", "si"))
        );
        assert_eq!(member_completion_context("math", 4), None);
    }

    #[test]
    fn editing_keeps_multibyte_input_on_char_boundaries() {
        let mut app = App::new(None, false).expect("app should initialize");
        app.insert_char('é');
        app.insert_char('x');

        let action = handle_key(&mut app, KeyCode::Left, KeyModifiers::NONE);
        assert!(matches!(action, EventAction::Continue));
        assert_eq!(app.cursor, 'é'.len_utf8());

        let action = handle_key(&mut app, KeyCode::Backspace, KeyModifiers::NONE);
        assert!(matches!(action, EventAction::Continue));
        assert_eq!(app.input, "x");
        assert_eq!(app.cursor, 0);
    }

    #[test]
    fn delete_removes_one_multibyte_char() {
        let mut app = App::new(None, false).expect("app should initialize");
        app.insert_char('é');
        app.insert_char('x');
        app.cursor = 0;

        let action = handle_key(&mut app, KeyCode::Delete, KeyModifiers::NONE);

        assert!(matches!(action, EventAction::Continue));
        assert_eq!(app.input, "x");
        assert_eq!(app.cursor, 0);
    }
}
