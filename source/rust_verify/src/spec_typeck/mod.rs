#![allow(dead_code)]

mod check_expr;
mod check_ty;
mod check_pat;
mod check_path;
mod unifier;
mod substitutions;

pub struct State<'a, 'tcx> {
    scope_map: air::scope_map::ScopeMap<vir::ast::VarIdent, vir::ast::Typ>,
    unifier: unifier::Unifier,
    bctx: &'a crate::context::BodyCtxt<'tcx>,
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
}

pub fn typecheck<'tcx>(
    bctx: &crate::context::BodyCtxt<'tcx>,
    expr: &rustc_hir::Expr<'tcx>,
    expected_typ: &vir::ast::Typ,
) -> Result<vir::ast::Expr, vir::ast::VirErr>
{
    let mut state = State {
        scope_map: air::scope_map::ScopeMap::new(),
        unifier: unifier::Unifier::new(),
        bctx: bctx,
        tcx: bctx.ctxt.tcx,
    };

    let e = state.check_expr(expr)?;
    state.expect(&e.typ, expected_typ)?;

    // do substitutions
    // match exhaustiveness
    // int literal bounds checking
    // trait checks, impl paths, static resolutions

    todo!();
}