//! This crate defines the trait resolution method.
//!
//! - **Traits.** Trait resolution is implemented in the `traits` module.
//!
//! For more information about how rustc works, see the [rustc-dev-guide].
//!
//! [rustc-dev-guide]: https://rustc-dev-guide.rust-lang.org/
//!
//! # Note
//!
//! This API is completely unstable and subject to change.

#![doc(html_root_url = "https://doc.rust-lang.org/nightly/nightly-rustc/")]
#![doc(rust_logo)]
#![feature(rustdoc_internals)]
#![allow(internal_features)]
#![allow(rustc::diagnostic_outside_of_impl)]
#![allow(rustc::untranslatable_diagnostic)]
#![feature(assert_matches)]
#![cfg_attr(bootstrap, feature(associated_type_bounds))]
#![feature(associated_type_defaults)]
#![feature(box_patterns)]
#![feature(control_flow_enum)]
#![feature(extract_if)]
#![feature(if_let_guard)]
#![feature(let_chains)]
#![feature(option_take_if)]
#![feature(never_type)]
#![feature(type_alias_impl_trait)]
#![recursion_limit = "512"] // For rustdoc
#![feature(rustc_private)]

#[macro_use]
extern crate rustc_macros;
#[cfg(target_pointer_width = "64")]
#[macro_use]
extern crate rustc_data_structures;
#[macro_use]
extern crate tracing;
#[macro_use]
extern crate rustc_middle;
#[macro_use]
extern crate smallvec;

extern crate rustc_errors;
extern crate rustc_infer;
extern crate rustc_hir;
extern crate rustc_span;
extern crate rustc_session;
extern crate rustc_next_trait_solver;
extern crate rustc_index;
extern crate rustc_ast;
extern crate rustc_transmute;
extern crate rustc_ast_ir;
extern crate rustc_attr;
extern crate rustc_parse_format;
extern crate rustc_target;
extern crate rustc_fluent_macro;
extern crate rustc_query_system;

pub mod errors;
pub mod infer;
pub mod regions;
pub mod solve;
pub mod traits;

rustc_fluent_macro::fluent_messages! { "../messages.ftl" }