pub(crate) fn is_light(bg: (u8, u8, u8)) -> bool {
    let (r, g, b) = bg;
    // Fast perceived-brightness heuristic for choosing a subtle terminal
    // highlight direction, not a full contrast calculation.
    let y = 0.299 * r as f32 + 0.587 * g as f32 + 0.114 * b as f32;
    y > 128.0
}

pub(crate) fn blend(fg: (u8, u8, u8), bg: (u8, u8, u8), alpha: f32) -> (u8, u8, u8) {
    let alpha = alpha.clamp(0.0, 1.0);
    let r = (fg.0 as f32 * alpha + bg.0 as f32 * (1.0 - alpha)).round() as u8;
    let g = (fg.1 as f32 * alpha + bg.1 as f32 * (1.0 - alpha)).round() as u8;
    let b = (fg.2 as f32 * alpha + bg.2 as f32 * (1.0 - alpha)).round() as u8;
    (r, g, b)
}

pub(crate) fn color_distance(a: (u8, u8, u8), b: (u8, u8, u8)) -> u32 {
    // Raw RGB distance is cheap and deterministic; terminal palette matching
    // favors stability over perceptual color science.
    let dr = i32::from(a.0) - i32::from(b.0);
    let dg = i32::from(a.1) - i32::from(b.1);
    let db = i32::from(a.2) - i32::from(b.2);
    (dr * dr + dg * dg + db * db) as u32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detects_light_backgrounds() {
        assert!(is_light((240, 240, 240)));
        assert!(!is_light((20, 20, 20)));
    }

    #[test]
    fn blend_rounds_and_clamps_alpha() {
        assert_eq!(blend((255, 255, 255), (0, 0, 0), 0.5), (128, 128, 128));
        assert_eq!(blend((255, 0, 0), (0, 0, 255), -1.0), (0, 0, 255));
        assert_eq!(blend((255, 0, 0), (0, 0, 255), 2.0), (255, 0, 0));
    }

    #[test]
    fn color_distance_is_zero_for_equal_colors() {
        assert_eq!(color_distance((1, 2, 3), (1, 2, 3)), 0);
        assert_eq!(color_distance((2, 2, 3), (1, 2, 3)), 1);
    }
}
