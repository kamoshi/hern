use crate::color::color_distance;
use ratatui::style::Color;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum StdoutColorLevel {
    TrueColor,
    Ansi256,
    Ansi16,
    Unknown,
}

pub(crate) fn warm_cache() {
    let _ = default_colors();
    let _ = stdout_color_level();
}

pub(crate) fn default_bg() -> Option<(u8, u8, u8)> {
    default_colors().map(|colors| colors.bg)
}

pub(crate) fn best_color(target: (u8, u8, u8)) -> Color {
    match stdout_color_level() {
        StdoutColorLevel::TrueColor => Color::Rgb(target.0, target.1, target.2),
        StdoutColorLevel::Ansi256 => xterm_fixed_colors()
            .min_by_key(|(_, color)| color_distance(*color, target))
            .map(|(idx, _)| Color::Indexed(idx))
            .unwrap_or_default(),
        StdoutColorLevel::Ansi16 | StdoutColorLevel::Unknown => Color::default(),
    }
}

fn stdout_color_level() -> StdoutColorLevel {
    match supports_color::on_cached(supports_color::Stream::Stdout) {
        Some(level) if level.has_16m => StdoutColorLevel::TrueColor,
        Some(level) if level.has_256 => StdoutColorLevel::Ansi256,
        Some(_) => StdoutColorLevel::Ansi16,
        None => StdoutColorLevel::Unknown,
    }
}

#[derive(Clone, Copy)]
struct DefaultColors {
    bg: (u8, u8, u8),
}

fn default_colors() -> Option<DefaultColors> {
    imp::default_colors()
}

fn xterm_fixed_colors() -> impl Iterator<Item = (u8, (u8, u8, u8))> {
    (16u8..=255).map(|idx| (idx, xterm_color(idx)))
}

fn xterm_color(idx: u8) -> (u8, u8, u8) {
    const CUBE: [u8; 6] = [0, 95, 135, 175, 215, 255];
    match idx {
        16..=231 => {
            let n = idx - 16;
            let r = CUBE[(n / 36) as usize];
            let g = CUBE[((n % 36) / 6) as usize];
            let b = CUBE[(n % 6) as usize];
            (r, g, b)
        }
        232..=255 => {
            let v = 8 + (idx - 232) * 10;
            (v, v, v)
        }
        _ => (0, 0, 0),
    }
}

#[cfg(all(unix, not(test)))]
mod imp {
    use super::DefaultColors;
    use std::sync::{Mutex, OnceLock};

    #[derive(Default)]
    struct Cache {
        attempted: bool,
        value: Option<DefaultColors>,
    }

    impl Cache {
        fn get_or_init(&mut self) -> Option<DefaultColors> {
            if !self.attempted {
                self.value = query_default_colors();
                self.attempted = true;
            }
            self.value
        }
    }

    fn cache() -> &'static Mutex<Cache> {
        static CACHE: OnceLock<Mutex<Cache>> = OnceLock::new();
        CACHE.get_or_init(|| Mutex::new(Cache::default()))
    }

    pub(super) fn default_colors() -> Option<DefaultColors> {
        cache().lock().ok()?.get_or_init()
    }

    fn query_default_colors() -> Option<DefaultColors> {
        // Query the terminal's actual background via OSC 11.  Falls back to a
        // dark-terminal assumption when the terminal doesn't support OSC 11 or
        // the query times out.
        let bg = terminal_colorsaurus::background_color(Default::default())
            .ok()
            .map(|c| ((c.r >> 8) as u8, (c.g >> 8) as u8, (c.b >> 8) as u8))
            .unwrap_or((0, 0, 0));
        Some(DefaultColors { bg })
    }
}

#[cfg(not(all(unix, not(test))))]
mod imp {
    use super::DefaultColors;

    pub(super) fn default_colors() -> Option<DefaultColors> {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn xterm_cube_color_is_computed() {
        assert_eq!(xterm_color(16), (0, 0, 0));
        assert_eq!(xterm_color(231), (255, 255, 255));
        assert_eq!(xterm_color(235), (38, 38, 38));
    }
}
