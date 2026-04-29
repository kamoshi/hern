use crate::app::{App, Entry, EntryKind};
use crate::highlight::{highlight_line, highlight_source_lines};
use crate::terminal::TerminalGuard;
use ratatui::buffer::Buffer;
use ratatui::layout::Margin;
use ratatui::layout::{Alignment, Constraint, Direction, Layout, Rect};
use ratatui::style::{Color, Modifier, Style, Stylize};
use ratatui::text::{Line, Span};
use ratatui::widgets::{Block, BorderType, Borders, Clear, Paragraph, Widget, Wrap};
use std::io;

pub(crate) fn draw(frame: &mut ratatui::Frame<'_>, app: &App) {
    let area = frame.area();
    let [
        status_area,
        spacer_area,
        composer_area,
        hint_area,
        completions_area,
        footer_area,
    ] = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Length(1),
            Constraint::Min(0),
            Constraint::Length(4),
            Constraint::Length(1),
            Constraint::Length(3),
            Constraint::Length(1),
        ])
        .areas(area);

    render_status(frame, status_area);
    let _ = spacer_area;
    let input_area = render_composer(frame, composer_area, app);
    render_type_hint(frame, hint_area, app);
    render_completion_preview(frame, completions_area, app);
    render_footer(frame, footer_area);
    if app.bindings_overlay.open {
        render_bindings_popover(frame, area, app);
    }

    let (cursor_line, cursor_col, scroll) = cursor_metrics(app, input_area.height);
    frame.set_cursor_position((
        input_area.x + 2 + cursor_col.min(input_area.width.saturating_sub(3)),
        input_area.y + cursor_line.saturating_sub(scroll),
    ));
}

fn render_status(frame: &mut ratatui::Frame<'_>, area: Rect) {
    let line = Line::from(vec![
        Span::styled(" Hern ", Style::default().fg(Color::Black).bg(Color::Cyan)),
        Span::raw(" "),
        Span::styled("ready", Style::default().fg(Color::Green)),
        Span::raw(" "),
        Span::styled("interactive session", Style::default().fg(Color::DarkGray)),
    ]);
    frame.render_widget(Paragraph::new(line), area);
}

fn render_composer(frame: &mut ratatui::Frame<'_>, area: Rect, app: &App) -> Rect {
    let block = Block::default()
        .borders(Borders::ALL)
        .border_type(BorderType::Rounded)
        .border_style(Style::default().fg(Color::DarkGray))
        .title(Span::styled(
            " input ",
            Style::default()
                .fg(Color::Cyan)
                .add_modifier(Modifier::BOLD),
        ));
    let inner = block.inner(area).inner(Margin {
        horizontal: 1,
        vertical: 0,
    });
    frame.render_widget(block, area);

    let lines = composer_lines(app);
    let (_, _, scroll) = cursor_metrics(app, inner.height);
    let visible: Vec<Line<'static>> = lines
        .into_iter()
        .skip(scroll as usize)
        .take(inner.height as usize)
        .collect();
    frame.render_widget(Paragraph::new(visible).wrap(Wrap { trim: false }), inner);
    inner
}

fn render_footer(frame: &mut ratatui::Frame<'_>, area: Rect) {
    let footer = Line::from(vec![
        "enter".cyan().bold(),
        " run   ".into(),
        "shift+enter".cyan().bold(),
        " newline   ".into(),
        "up/down".cyan().bold(),
        " history   ".into(),
        "ctrl+t".cyan().bold(),
        " bindings   ".into(),
        "ctrl+d".cyan().bold(),
        " exit".into(),
    ]);
    frame.render_widget(
        Paragraph::new(footer)
            .style(Style::default().fg(Color::DarkGray))
            .alignment(Alignment::Center),
        area,
    );
}

fn render_type_hint(frame: &mut ratatui::Frame<'_>, area: Rect, app: &App) {
    let line = match app.type_hint() {
        Some(ty) => Line::from(vec![
            Span::styled("  : ", Style::default().fg(Color::DarkGray)),
            Span::styled(ty, Style::default().fg(Color::Yellow)),
        ]),
        None => Line::from(Span::styled("  ", Style::default().fg(Color::DarkGray))),
    };
    frame.render_widget(Paragraph::new(line), area);
}

fn render_completion_preview(frame: &mut ratatui::Frame<'_>, area: Rect, app: &App) {
    let completions = app.completion_items();
    let width = area.width.saturating_sub(2) as usize;
    let rows: Vec<Line<'static>> = completions
        .iter()
        .take(area.height as usize)
        .map(|binding| completion_preview_row(binding, width))
        .collect();
    let rows = if rows.is_empty() {
        vec![Line::from(Span::raw(""))]
    } else {
        rows
    };
    frame.render_widget(Paragraph::new(rows), area);
}

fn completion_preview_row(
    binding: &crate::session::BindingInfo,
    row_width: usize,
) -> Line<'static> {
    let prefix = "  ";
    let reserved = prefix.len() + binding.name.len() + 2;
    let ty_width = row_width.saturating_sub(reserved);
    Line::from(vec![
        Span::raw(prefix.to_string()),
        Span::styled(
            binding.name.clone(),
            Style::default()
                .fg(Color::Cyan)
                .add_modifier(Modifier::BOLD),
        ),
        Span::styled("  ", Style::default().fg(Color::DarkGray)),
        Span::styled(
            truncate_to_width(&binding.ty, ty_width),
            Style::default().fg(Color::DarkGray),
        ),
    ])
}

fn render_bindings_popover(frame: &mut ratatui::Frame<'_>, area: Rect, app: &App) {
    let width = area
        .width
        .saturating_sub(2)
        .min((area.width * 3 / 4).max(48))
        .max(1);
    let height = area.height.saturating_sub(2).max(1);
    let x = area.x + area.width.saturating_sub(width) / 2;
    let y = area.y + area.height.saturating_sub(height) / 2;
    let popup = Rect::new(x, y, width, height);
    frame.render_widget(Clear, popup);

    let block = Block::default()
        .borders(Borders::ALL)
        .border_type(BorderType::Rounded)
        .border_style(Style::default().fg(Color::Cyan))
        .title(Span::styled(
            " bindings ",
            Style::default()
                .fg(Color::Cyan)
                .add_modifier(Modifier::BOLD),
        ))
        .title_bottom("type filter  enter insert  pgup/pgdn scroll  esc close");
    let inner = block.inner(popup).inner(Margin {
        horizontal: 1,
        vertical: 0,
    });
    frame.render_widget(block, popup);

    let [query_area, list_area] = Layout::default()
        .direction(Direction::Vertical)
        .constraints([Constraint::Length(2), Constraint::Min(1)])
        .areas(inner);

    let query = if app.bindings_overlay.query.is_empty() {
        "filter..."
    } else {
        app.bindings_overlay.query.as_str()
    };
    let query_style = if app.bindings_overlay.query.is_empty() {
        Style::default().fg(Color::DarkGray)
    } else {
        Style::default().fg(Color::White)
    };
    frame.render_widget(
        Paragraph::new(Line::from(vec![
            Span::styled("> ", Style::default().fg(Color::Cyan)),
            Span::styled(query.to_string(), query_style),
        ])),
        query_area,
    );

    let bindings = app.filtered_bindings();
    let visible_rows = list_area.height as usize;
    let selected = app
        .bindings_overlay
        .selected
        .min(bindings.len().saturating_sub(1));
    let start = selected.saturating_sub(visible_rows.saturating_sub(1));
    let row_width = list_area.width as usize;
    let rows: Vec<Line<'static>> = bindings
        .iter()
        .enumerate()
        .skip(start)
        .take(visible_rows)
        .map(|(idx, binding)| {
            let selected = idx == selected;
            let base = if selected {
                Style::default().fg(Color::Black).bg(Color::Cyan)
            } else {
                Style::default()
            };
            binding_row(binding, selected, base, row_width)
        })
        .collect();
    let rows = if rows.is_empty() {
        vec![Line::from(Span::styled(
            "No bindings",
            Style::default().fg(Color::DarkGray),
        ))]
    } else {
        rows
    };
    frame.render_widget(Paragraph::new(rows), list_area);
}

fn binding_row(
    binding: &crate::session::BindingInfo,
    selected: bool,
    base: Style,
    row_width: usize,
) -> Line<'static> {
    let marker = if selected { "> " } else { "  " };
    let reserved = marker.len() + binding.name.len() + 2;
    let ty_width = row_width.saturating_sub(reserved);
    let ty = truncate_to_width(&binding.ty, ty_width);
    Line::from(vec![
        Span::styled(marker.to_string(), base),
        Span::styled(binding.name.clone(), base.add_modifier(Modifier::BOLD)),
        Span::styled("  ", base),
        Span::styled(
            ty,
            base.fg(if selected {
                Color::Black
            } else {
                Color::DarkGray
            }),
        ),
    ])
}

fn truncate_to_width(text: &str, max_width: usize) -> String {
    if max_width == 0 {
        return String::new();
    }
    let mut out = String::new();
    for ch in text.chars().take(max_width) {
        out.push(ch);
    }
    if text.chars().count() > max_width && max_width > 1 {
        out.pop();
        out.push('~');
    }
    out
}

fn composer_lines(app: &App) -> Vec<Line<'static>> {
    if app.input.is_empty() {
        return vec![Line::from(vec![
            Span::styled("λ ", Style::default().fg(Color::Cyan)),
            Span::styled(
                "Type Hern expression or definition...",
                Style::default().fg(Color::DarkGray),
            ),
        ])];
    }

    app.input
        .split('\n')
        .enumerate()
        .map(|(idx, line)| {
            let prompt = if idx == 0 { "λ " } else { "  " };
            let mut spans = vec![Span::styled(
                prompt.to_string(),
                Style::default().fg(Color::Cyan),
            )];
            spans.extend(highlight_line(line).spans);
            Line::from(spans)
        })
        .collect()
}

fn cursor_metrics(app: &App, height: u16) -> (u16, u16, u16) {
    let before_cursor = &app.input[..app.cursor];
    let cursor_line = before_cursor.chars().filter(|ch| *ch == '\n').count() as u16;
    let cursor_col = before_cursor
        .rsplit('\n')
        .next()
        .map(|line| line.chars().count())
        .unwrap_or(0) as u16;
    let scroll = if height == 0 || cursor_line < height {
        0
    } else {
        cursor_line + 1 - height
    };
    (cursor_line, cursor_col, scroll)
}

pub(crate) fn insert_entries(terminal: &mut TerminalGuard, entries: Vec<Entry>) -> io::Result<()> {
    let lines = entries_to_lines(&entries);
    if lines.is_empty() {
        return Ok(());
    }
    let width = terminal.size()?.width.max(1);
    let height = rendered_height(&lines, width);
    terminal.insert_before(height, |buf| render_history(buf, &lines))
}

fn render_history(buf: &mut Buffer, lines: &[Line<'static>]) {
    let area = buf.area;
    Paragraph::new(lines.to_vec())
        .wrap(Wrap { trim: false })
        .render(area, buf);
}

fn rendered_height(lines: &[Line<'static>], width: u16) -> u16 {
    let width = usize::from(width.max(1));
    lines
        .iter()
        .map(|line| {
            let text_width = line
                .spans
                .iter()
                .map(|span| span.content.chars().count())
                .sum::<usize>();
            text_width.max(1).div_ceil(width) as u16
        })
        .sum::<u16>()
        .max(1)
}

fn entries_to_lines(entries: &[Entry]) -> Vec<Line<'static>> {
    entries
        .iter()
        .flat_map(|entry| {
            let (prefix, style) = match entry.kind {
                EntryKind::Input => ("> ", Style::default().fg(Color::Cyan)),
                EntryKind::Output => ("  ", Style::default().fg(Color::Green)),
                EntryKind::Error => ("! ", Style::default().fg(Color::Red)),
                EntryKind::Info => ("  ", Style::default().fg(Color::Gray)),
            };
            let highlighted_input =
                matches!(entry.kind, EntryKind::Input).then(|| highlight_source_lines(&entry.text));
            entry
                .text
                .lines()
                .enumerate()
                .map(move |(idx, line)| {
                    let prefix = if idx == 0 { prefix } else { "  " };
                    let mut spans = vec![Span::styled(
                        prefix.to_string(),
                        style.add_modifier(Modifier::BOLD),
                    )];
                    if let Some(lines) = highlighted_input.as_ref() {
                        spans.extend(lines.get(idx).cloned().unwrap_or_default().spans);
                    } else {
                        spans.push(Span::styled(line.to_string(), style));
                    }
                    Line::from(spans)
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn truncation_keeps_binding_rows_single_line() {
        assert_eq!(truncate_to_width("abcdefgh", 5), "abcd~");
        assert_eq!(truncate_to_width("abc", 5), "abc");
    }
}
