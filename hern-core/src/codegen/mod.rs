//! Code generation backends and bundle emitters.

pub mod bundle;
#[allow(dead_code)]
pub(crate) mod lua;

pub use bundle::{gen_lua_bundle, gen_lua_iife_bundle, gen_lua_iife_test_bundle};
