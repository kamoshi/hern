mod core_ir;
mod diagnostics;
mod eval;
mod expand;
mod pattern;
mod registry;
mod runtime;
mod source;
mod template;
#[cfg(test)]
mod tests;
mod value;

pub use expand::{MacroExecutionOptions, expand_macros, expand_macros_with_options};
