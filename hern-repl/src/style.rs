use crate::color::{blend, is_light};
use crate::terminal_palette::{best_color_if_supported, default_bg};
use ratatui::style::Style;

const LIGHT_OVERLAY: (u8, u8, u8) = (0, 0, 0);
const DARK_OVERLAY: (u8, u8, u8) = (255, 255, 255);
const LIGHT_OVERLAY_ALPHA: f32 = 0.04;
const DARK_OVERLAY_ALPHA: f32 = 0.12;

pub(crate) fn user_message_style() -> Style {
    user_message_style_for(default_bg())
}

fn user_message_style_for(terminal_bg: Option<(u8, u8, u8)>) -> Style {
    match terminal_bg {
        Some(bg) => user_message_bg(bg)
            .map(|color| Style::default().bg(color))
            .unwrap_or_default(),
        None => Style::default(),
    }
}

fn user_message_bg(terminal_bg: (u8, u8, u8)) -> Option<ratatui::style::Color> {
    // The threshold intentionally flips overlay direction so the composer stays
    // subtle on both dark and light terminal themes instead of chasing a fixed
    // luminance delta.
    let (top, alpha) = if is_light(terminal_bg) {
        (LIGHT_OVERLAY, LIGHT_OVERLAY_ALPHA)
    } else {
        (DARK_OVERLAY, DARK_OVERLAY_ALPHA)
    };
    best_color_if_supported(blend(top, terminal_bg, alpha))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ratatui::style::Color;

    #[test]
    fn style_without_detected_background_is_plain() {
        assert_eq!(user_message_style_for(None), Style::default());
    }

    #[test]
    fn user_message_bg_targets_light_and_dark_overlays() {
        let dark = user_message_bg((0, 0, 0));
        let light = user_message_bg((255, 255, 255));
        if let Some(Color::Rgb(r, g, b)) = dark {
            assert_eq!((r, g, b), (31, 31, 31));
        }
        if let Some(Color::Rgb(r, g, b)) = light {
            assert_eq!((r, g, b), (245, 245, 245));
        }
    }

    #[test]
    fn user_message_bg_documents_light_dark_boundary() {
        let dark_side = user_message_bg((128, 128, 128));
        let light_side = user_message_bg((129, 129, 129));
        if let Some(Color::Rgb(r, g, b)) = dark_side {
            assert_eq!((r, g, b), (143, 143, 143));
        }
        if let Some(Color::Rgb(r, g, b)) = light_side {
            assert_eq!((r, g, b), (124, 124, 124));
        }
    }
}
