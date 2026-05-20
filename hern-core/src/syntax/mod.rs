mod category;
mod model;
mod template_check;

pub use category::{
    CategoryMatchMode, category_accepts_source, category_accepts_tokens, category_match_mode,
    syntax_nodes_to_source,
};
pub use model::{
    ScopeSet, Syntax, SyntaxCapture, SyntaxCategory, SyntaxDelimiter, SyntaxKind, SyntaxOrigin,
    SyntaxPattern, SyntaxTemplate, SyntaxTemplateSplice, SyntaxToken,
    collect_syntax_pattern_captures, collect_syntax_template_splices, syntax_pattern_to_lua,
    syntax_to_lua, token_to_syntax,
};
pub use template_check::check_template_splice_categories;
