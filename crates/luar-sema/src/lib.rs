//! Semantic analysis: module graph, name resolution, type checking, narrowing,
//! exhaustiveness, and decorator expansion.

pub mod init;
pub mod modules;
pub mod names;
pub mod scope;
pub mod types;
