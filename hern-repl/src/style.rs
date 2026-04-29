use crate::color::{blend, is_light};
use crate::terminal_palette::{best_color, default_bg};
use ratatui::style::Style;

pub(crate) fn user_message_style() -> Style {
    user_message_style_for(default_bg())
}

fn user_message_style_for(terminal_bg: Option<(u8, u8, u8)>) -> Style {
    match terminal_bg {
        Some(bg) => Style::default().bg(user_message_bg(bg)),
        None => Style::default(),
    }
}

fn user_message_bg(terminal_bg: (u8, u8, u8)) -> ratatui::style::Color {
    let (top, alpha) = if is_light(terminal_bg) {
        ((0, 0, 0), 0.04)
    } else {
        ((255, 255, 255), 0.12)
    };
    best_color(blend(top, terminal_bg, alpha))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn style_without_detected_background_is_plain() {
        assert_eq!(user_message_style_for(None), Style::default());
    }
}
