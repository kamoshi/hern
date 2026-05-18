use crate::app::{App, Entry, EntryKind, clamp_to_char_boundary};
use crate::highlight::{highlight_line, highlight_source_lines};
use crate::style::user_message_style;
use crate::terminal::TerminalGuard;
use ratatui::buffer::Buffer;
use ratatui::layout::Margin;
use ratatui::layout::{Constraint, Direction, Layout, Rect};
use ratatui::style::{Color, Modifier, Style, Stylize};
use ratatui::text::{Line, Span};
use ratatui::widgets::{Block, BorderType, Borders, Clear, Paragraph, Widget, Wrap};
use std::io;
use unicode_width::{UnicodeWidthChar, UnicodeWidthStr};

const MAX_COMPOSER_INNER: u16 = 3;
// spacer(1) + status(1) + composer(1..3 inner +2 pad) + hint(1) + hint_spacer(1)
// + completions(3..1) + bottom_spacer(1) + footer(1) = always 12
pub(crate) const VIEWPORT_HEIGHT: u16 = 12;

fn composer_inner_height(app: &App) -> u16 {
    (app.input.split('\n').count() as u16).clamp(1, MAX_COMPOSER_INNER)
}

pub(crate) fn draw(frame: &mut ratatui::Frame<'_>, app: &App) {
    let area = frame.area();
    let composer_inner = composer_inner_height(app);
    let completions_height = 4 - composer_inner; // 3→1 as composer grows 1→3
    let [
        top_spacer_area,
        status_area,
        composer_area,
        hint_area,
        hint_completions_spacer_area,
        completions_area,
        spacer_area,
        footer_area,
    ] = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Length(1),
            Constraint::Length(1),
            Constraint::Length(composer_inner + 2),
            Constraint::Length(1),
            Constraint::Length(1),
            Constraint::Length(completions_height),
            Constraint::Length(1),
            Constraint::Length(1),
        ])
        .areas(area);

    let _ = top_spacer_area;
    render_status(frame, status_area);
    let input_area = render_composer(frame, composer_area, app);
    render_type_hint(frame, hint_area, app);
    let _ = hint_completions_spacer_area;
    render_completion_preview(frame, completions_area, app);
    let _ = spacer_area;
    render_footer(frame, footer_area);
    if app.bindings_overlay.open {
        let (cursor_x, cursor_y) = render_bindings_popover(frame, area, app);
        frame.set_cursor_position((cursor_x, cursor_y));
        return;
    }

    if input_area.width > 0 && input_area.height > 0 {
        let (cursor_row, cursor_col, _) = cursor_metrics(app, input_area.height, input_area.width);
        frame.set_cursor_position((
            input_area.x + cursor_col.min(input_area.width.saturating_sub(1)),
            input_area.y + cursor_row.min(input_area.height.saturating_sub(1)),
        ));
    }
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
    let inner = Rect {
        x: area.x.saturating_add(2).min(area.right()),
        y: area.y.saturating_add(1),
        width: area.width.saturating_sub(3),
        height: area.height.saturating_sub(2),
    };
    let input_style = user_message_style();
    if area.height > 0 {
        frame.render_widget(Block::default().style(input_style), area);
    }

    let prompt = if app.input.is_empty() {
        Span::styled("λ", Style::default().fg(Color::DarkGray))
    } else {
        Span::styled("λ", Style::default().fg(Color::Cyan).bold())
    };
    frame.render_widget(
        Paragraph::new(Line::from(prompt)),
        Rect {
            x: area.x,
            y: inner.y,
            width: 1,
            height: 1,
        },
    );

    let (_, _, scroll) = cursor_metrics(app, inner.height, inner.width);
    frame.render_widget(
        Paragraph::new(composer_lines(app))
            .wrap(Wrap { trim: false })
            .scroll((scroll, 0))
            .style(input_style),
        inner,
    );
    inner
}

fn render_footer(frame: &mut ratatui::Frame<'_>, area: Rect) {
    let footer = Line::from(vec![
        "  ".into(),
        "enter".cyan().bold(),
        " run   ".into(),
        "ctrl+j".cyan().bold(),
        " newline   ".into(),
        "up/down".cyan().bold(),
        " history   ".into(),
        "ctrl+t".cyan().bold(),
        " bindings   ".into(),
        "ctrl+d".cyan().bold(),
        " exit".into(),
    ]);
    frame.render_widget(
        Paragraph::new(footer).style(Style::default().fg(Color::DarkGray)),
        area,
    );
}

fn render_type_hint(frame: &mut ratatui::Frame<'_>, area: Rect, app: &App) {
    let line = match &app.type_hint {
        Some(ty) => Line::from(vec![
            Span::styled("  : ", Style::default().fg(Color::DarkGray)),
            Span::styled(ty.clone(), Style::default().fg(Color::Yellow)),
        ]),
        None => Line::from(Span::styled("  ", Style::default().fg(Color::DarkGray))),
    };
    frame.render_widget(Paragraph::new(line), area);
}

fn render_completion_preview(frame: &mut ratatui::Frame<'_>, area: Rect, app: &App) {
    let width = area.width.saturating_sub(2) as usize;
    let rows: Vec<Line<'static>> = app
        .completions
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
    let ty_width = binding_type_width(row_width, prefix, &binding.name);
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

fn render_bindings_popover(frame: &mut ratatui::Frame<'_>, area: Rect, app: &App) -> (u16, u16) {
    let width = area
        .width
        .saturating_sub(2)
        .min(((u32::from(area.width) * 3 / 4) as u16).max(48))
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
    let query_cursor_col = 2 + UnicodeWidthStr::width(app.bindings_overlay.query.as_str()) as u16;

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
    (
        query_area.x + query_cursor_col.min(query_area.width.saturating_sub(1)),
        query_area.y,
    )
}

fn binding_row(
    binding: &crate::session::BindingInfo,
    selected: bool,
    base: Style,
    row_width: usize,
) -> Line<'static> {
    let marker = if selected { "> " } else { "  " };
    let ty_width = binding_type_width(row_width, marker, &binding.name);
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

fn binding_type_width(row_width: usize, marker: &str, name: &str) -> usize {
    let reserved = marker.len() + UnicodeWidthStr::width(name) + 2;
    row_width.saturating_sub(reserved)
}

fn truncate_to_width(text: &str, max_width: usize) -> String {
    if max_width == 0 {
        return String::new();
    }
    let mut out = String::new();
    let mut used = 0usize;
    let mut truncated = false;
    for ch in text.chars() {
        let w = ch.width().unwrap_or(0);
        if used + w > max_width {
            truncated = true;
            break;
        }
        out.push(ch);
        used += w;
    }
    if truncated && max_width > 1 {
        while used + 1 > max_width {
            if let Some(ch) = out.pop() {
                used -= ch.width().unwrap_or(0);
            } else {
                break;
            }
        }
        out.push('~');
    }
    out
}

fn composer_lines(app: &App) -> Vec<Line<'static>> {
    if app.input.is_empty() {
        return vec![Line::from(Span::styled(
            "Type Hern expression or definition...",
            Style::default().fg(Color::DarkGray),
        ))];
    }

    app.input
        .split('\n')
        .map(|line| highlight_line(line))
        .collect()
}

// Returns (cursor_row, cursor_col, visual_scroll) where cursor_row and cursor_col
// are relative to the first visible wrapped row after applying visual_scroll.
// All three account for visual line wrapping at `width` columns.
fn cursor_metrics(app: &App, height: u16, width: u16) -> (u16, u16, u16) {
    let cursor = clamp_to_char_boundary(&app.input, app.cursor);
    let w = width.max(1) as usize;
    let before_cursor = &app.input[..cursor];

    let cursor_logical_line = before_cursor.bytes().filter(|&b| b == b'\n').count();
    let cursor_logical_col = before_cursor
        .rsplit('\n')
        .next()
        .map(UnicodeWidthStr::width)
        .unwrap_or(0);

    let visual_rows_per_line: Vec<u16> = app
        .input
        .split('\n')
        .map(|l| (UnicodeWidthStr::width(l).div_ceil(w)).max(1) as u16)
        .collect();

    let cursor_visual_row: u16 = visual_rows_per_line[..cursor_logical_line]
        .iter()
        .sum::<u16>()
        + (cursor_logical_col / w) as u16;
    let visual_col = (cursor_logical_col % w) as u16;

    let visual_scroll = if height == 0 || cursor_visual_row < height {
        0u16
    } else {
        cursor_visual_row.saturating_add(1).saturating_sub(height)
    };

    (
        cursor_visual_row.saturating_sub(visual_scroll),
        visual_col,
        visual_scroll,
    )
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
    for y in area.top()..area.bottom() {
        let row_bg = (area.left()..area.right()).find_map(|x| {
            let cell = buf.cell((x, y))?;
            (cell.bg != Color::Reset).then_some(cell.bg)
        });
        let Some(bg) = row_bg else { continue };
        for x in area.left()..area.right() {
            if let Some(cell) = buf.cell_mut((x, y))
                && cell.bg == Color::Reset
            {
                cell.bg = bg;
            }
        }
    }
}

fn rendered_height(lines: &[Line<'static>], width: u16) -> u16 {
    let width = width.max(1);
    lines
        .iter()
        .map(|line| wrapped_line_height(line, width))
        .sum::<u16>()
        .max(1)
}

fn wrapped_line_height(line: &Line<'static>, width: u16) -> u16 {
    let mut rendered = 0u16;
    let mut line_width = 0u16;
    let mut word_width = 0u16;
    let mut whitespace_width = 0u16;
    let mut non_whitespace_previous = false;

    for grapheme in line.styled_graphemes(Style::default()) {
        let is_whitespace = grapheme.is_whitespace();
        let symbol_width = grapheme.symbol.width() as u16;
        if symbol_width > width {
            continue;
        }

        let word_found = non_whitespace_previous && is_whitespace;
        let untrimmed_overflow = line_width == 0
            && word_width
                .saturating_add(whitespace_width)
                .saturating_add(symbol_width)
                > width;
        if word_found || untrimmed_overflow {
            line_width = line_width
                .saturating_add(whitespace_width)
                .saturating_add(word_width);
            whitespace_width = 0;
            word_width = 0;
        }

        let line_full = line_width >= width;
        let pending_word_overflow = symbol_width > 0
            && line_width
                .saturating_add(whitespace_width)
                .saturating_add(word_width)
                >= width;
        if line_full || pending_word_overflow {
            rendered = rendered.saturating_add(1);
            let mut remaining_width = width.saturating_sub(line_width);
            line_width = 0;

            while whitespace_width > 0 {
                if remaining_width == 0 {
                    break;
                }
                whitespace_width = whitespace_width.saturating_sub(1);
                remaining_width = remaining_width.saturating_sub(1);
            }
            if is_whitespace && whitespace_width == 0 {
                continue;
            }
        }

        if is_whitespace {
            whitespace_width = whitespace_width.saturating_add(symbol_width);
        } else {
            word_width = word_width.saturating_add(symbol_width);
        }
        non_whitespace_previous = !is_whitespace;
    }

    let tail_width = line_width
        .saturating_add(whitespace_width)
        .saturating_add(word_width);
    if tail_width > 0 {
        rendered = rendered.saturating_add(1);
    }
    rendered.max(1)
}

fn entries_to_lines(entries: &[Entry]) -> Vec<Line<'static>> {
    let mut lines: Vec<Line<'static>> = entries
        .iter()
        .flat_map(|entry| {
            let (prefix, style) = match entry.kind {
                EntryKind::Input => ("λ ", Style::default().fg(Color::Cyan)),
                EntryKind::Output => ("  ", Style::default().fg(Color::Green)),
                EntryKind::Error => ("! ", Style::default().fg(Color::Red)),
                EntryKind::Info => ("  ", Style::default().fg(Color::Gray)),
            };
            let is_input = matches!(entry.kind, EntryKind::Input);
            let highlighted_input = is_input.then(|| highlight_source_lines(&entry.text));
            let line_style = if is_input {
                user_message_style()
            } else {
                Style::default()
            };
            entry
                .text
                .split('\n')
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
                    Line::from(spans).style(line_style)
                })
                .collect::<Vec<_>>()
        })
        .collect();
    if !lines.is_empty() {
        lines.push(Line::from(""));
    }
    lines
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn entries_to_lines_includes_all_entries() {
        let entries = vec![
            Entry {
                kind: EntryKind::Input,
                text: "2".to_string(),
            },
            Entry {
                kind: EntryKind::Output,
                text: "2".to_string(),
            },
        ];
        let lines = entries_to_lines(&entries);
        // Input adds 1 line (> 2)
        // Output adds 1 line (  2)
        assert_eq!(lines.len(), 3);
        assert!(lines[0].spans.iter().any(|s| s.content == "λ "));
        assert!(lines[1].spans.iter().any(|s| s.content == "  "));
        assert!(lines[1].spans.iter().any(|s| s.content == "2"));
        assert!(
            lines[2].spans.is_empty() || lines[2].spans.iter().all(|s| s.content.trim().is_empty())
        );
    }

    #[test]
    fn entries_to_lines_handles_multi_line_error() {
        let entries = vec![
            Entry {
                kind: EntryKind::Input,
                text: "bad".to_string(),
            },
            Entry {
                kind: EntryKind::Error,
                text: "error line 1\nerror line 2".to_string(),
            },
        ];
        let lines = entries_to_lines(&entries);
        // Input: 1 line
        // Error: 2 lines
        assert_eq!(lines.len(), 4);
        assert!(lines[1].spans.iter().any(|s| s.content == "! "));
        assert!(lines[1].spans.iter().any(|s| s.content == "error line 1"));
        assert!(lines[2].spans.iter().any(|s| s.content == "  "));
        assert!(lines[2].spans.iter().any(|s| s.content == "error line 2"));
    }

    #[test]
    fn entries_to_lines_preserves_trailing_empty_lines() {
        let entries = vec![Entry {
            kind: EntryKind::Error,
            text: "first\n".to_string(),
        }];
        let lines = entries_to_lines(&entries);
        assert_eq!(lines.len(), 3);
        assert!(lines[0].spans.iter().any(|s| s.content == "first"));
        assert!(lines[1].spans.iter().any(|s| s.content == "  "));
    }

    #[test]
    fn rendered_height_matches_word_wrapping_with_spaces() {
        let lines = vec![Line::from(
            "This is a long line of text that should wrap      and contains a superultramegagigalong word.",
        )];
        assert_eq!(rendered_height(&lines, 20), 6);
        assert_eq!(rendered_height(&lines, 12), 9);
    }

    #[test]
    fn rendered_height_preserves_wrapped_indentation() {
        let lines = vec![Line::from("AAAAAAAAAAAAAAAAAAAA    AAA")];
        assert_eq!(rendered_height(&lines, 20), 2);
    }

    #[test]
    fn rendered_height_handles_highlighted_multi_span_input() {
        let lines = vec![Line::from(vec![
            Span::raw("let "),
            Span::styled("answer", Style::default().fg(Color::Cyan)),
            Span::raw(" = 1234567890"),
        ])];
        assert_eq!(rendered_height(&lines, 10), 3);
    }

    #[test]
    fn truncation_keeps_binding_rows_single_line() {
        assert_eq!(truncate_to_width("abcdefgh", 5), "abcd~");
        assert_eq!(truncate_to_width("abc", 5), "abc");
    }
}
