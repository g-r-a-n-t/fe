mod analyses;
mod canon;
mod check;
mod diagnostics;
mod facts;
mod ir;
mod noesc;
mod normalize;
mod verify;

pub use check::{
    SemanticBorrowAnalysisPass, check_semantic_borrows,
    collect_semantic_borrow_diagnostic_vouchers, semantic_borrow_summary,
};
pub use facts::*;
pub use ir::*;
pub use noesc::{check_semantic_noesc, check_semantic_noesc_voucher};
pub use normalize::normalize_semantic_body;
pub use verify::verify_normalized_semantic_body;
