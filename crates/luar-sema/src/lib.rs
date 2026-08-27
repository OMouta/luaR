//! Semantic analysis: name resolution, type checking, narrowing, and
//! exhaustiveness.

pub mod aliases;
pub mod annotations;
pub mod check;
pub mod facts;
pub mod init;
pub mod modules;
pub mod names;
pub mod scope;
pub mod table;
pub mod types;
