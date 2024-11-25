/*!
Handles monomorphization, where we produce specialized code from a polymorphic function.

For example, if we have
```no_run
spec fn f<A>(a: A) -> A { ... }

proof fn proof1<B>(b: B) {
  let x = f(b);
  let y = f(true);
}
```
we need to generate two functions, `(f Poly Poly)`, and `(f bool bool)` in the
emitted SMT code. This is done to meet 3 design criteria:
1. We want to verify a function exactly once, so we cannot specialize `proof1`
    on demand every time someone calls it.
2. We want to leverage SMT solver's capability as much as possible. Coercing a
primitive type such as `bool` or `int` to poly, even though we know `f(bool)` is
specialized, hinders this.
3. We want to ensure the generated AIR code can be type-checked by AIR.
 */
use crate::ast::Idents;
use crate::ast::IntRange;
use crate::ast::Primitive;
use crate::ast::{Dt, Fun, TypDecoration, TypDecorationArg};
use crate::def::POLY;
use crate::def::{path_to_string, Spanned};
use crate::poly;
use crate::sst::{CallFun, Exp, ExpX, KrateSstX, Stm};
use crate::sst::{Par, ParX};
use crate::sst_util::{subst_exp, subst_typ};
use crate::sst_visitor::{self, Visitor};
use crate::{
    ast::{Ident, Typ, TypX, Typs},
    sst::{FunctionSst, KrateSst},
};
use air::ast_util::str_typ;
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::Arc;

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, Default)]
pub enum PolyStrategy {
    #[default]
    Mono,
    Poly,
}

pub type SpecTyp = Arc<SpecTypX>;
pub type SpecTyps = Arc<Vec<SpecTyp>>;
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum SpecTypX {
    Bool,
    Int(IntRange),
    Datatype(Dt, SpecTyps),
    Decorate(TypDecoration, SpecTyp),
    Decorate2(TypDecoration, SpecTyps),
    Primitive(Primitive, SpecTyps),
    Poly,
}

impl SpecTypX {
    fn mangle_suffix(&self) -> String {
        match &self {
            Self::Bool => "bool".to_owned(),
            Self::Int(IntRange::Int) => "ii".to_owned(),
            Self::Int(IntRange::Nat) => "in".to_owned(),
            Self::Int(IntRange::U(u)) => format!("iu{u}"),
            Self::Int(IntRange::I(i)) => format!("ii{i}"),
            Self::Int(IntRange::USize) => format!("iusize"),
            Self::Int(IntRange::ISize) => format!("iisize"),
            Self::Int(IntRange::Char) => format!("ic"),
            Self::Datatype(Dt::Path(path), _) => format!("dt{}", path_to_string(&path)),
            Self::Datatype(Dt::Tuple(u), spec_typs) => {
                let tail = Self::mangle_typs(spec_typs);
                format!("dt{u}_{tail}")
            }
            Self::Decorate(dec, inner) => {
                let inner = inner.mangle_suffix();
                format!("d1{dec:?}_{inner}")
            }
            Self::Decorate2(dec, inners) => {
                let inners = Self::mangle_typs(inners);
                format!("d2{dec:?}_{inners}")
            }
            Self::Primitive(p, inners) => {
                let inners = Self::mangle_typs(inners);
                format!("p{p:?}_{inners}")
            }
            Self::Poly => "poly".to_owned(),
        }
    }
    fn mangle_typs(typs: &SpecTyps) -> String {
        typs.iter().map(|t| t.mangle_suffix()).collect::<Vec<_>>().join("_")
    }

    fn to_typ(&self) -> Typ {
        match &self {
            Self::Bool => Arc::new(TypX::Bool),
            Self::Int(range) => Arc::new(TypX::Int(*range)),
            Self::Datatype(path, typs) => {
                let typs = typs.iter().map(|t| t.to_typ()).collect();
                Arc::new(TypX::Datatype(path.clone(), Arc::new(typs), Arc::new(vec![])))
            }
            Self::Primitive(name, typs) => {
                let typs = typs.iter().map(|t| t.to_typ()).collect();
                Arc::new(TypX::Primitive(*name, Arc::new(typs)))
            }
            Self::Decorate(d, typ) => Arc::new(TypX::Decorate(*d, None, typ.to_typ())),
            Self::Decorate2(d, typs) => {
                assert!(typs.len() == 2);
                let allocator_typ = typs[0].to_typ();
                let typ = typs[1].to_typ();
                Arc::new(TypX::Decorate(*d, Some(TypDecorationArg { allocator_typ }), typ))
            }
            Self::Poly => Arc::new(TypX::Poly),
        }
    }
}
fn typs_as_spec(typs: &Typs, spec_map: &SpecMap) -> Vec<SpecTyp> {
    let mut spec_typs: Vec<SpecTyp> = Vec::new();
    for typ in typs.iter() {
        let spec_typ = typ_as_spec(typ, spec_map);
        spec_typs.push(spec_typ);
    }
    spec_typs
}

pub(crate) fn typ_as_spec(typ: &Typ, spec_map: &SpecMap) -> SpecTyp {
    match &**typ {
        TypX::Bool => Arc::new(SpecTypX::Bool),
        TypX::Int(range) => Arc::new(SpecTypX::Int(*range)),
        TypX::Datatype(path, typs, _impl_paths) => {
            let monotyps = typs_as_spec(typs, spec_map);
            Arc::new(SpecTypX::Datatype(path.clone(), Arc::new(monotyps)))
        }
        TypX::Decorate(d, None, t) => {
            let spec = typ_as_spec(t, spec_map);
            Arc::new(SpecTypX::Decorate(*d, spec))
        }
        TypX::Decorate(d, Some(TypDecorationArg { allocator_typ }), t) => {
            let m1 = typ_as_spec(allocator_typ, spec_map);
            let m2 = typ_as_spec(t, spec_map);
            Arc::new(SpecTypX::Decorate2(*d, Arc::new(vec![m1, m2])))
        }
        TypX::Primitive(Primitive::Array, _) => Arc::new(SpecTypX::Poly),
        TypX::Primitive(name, typs) => {
            let monotyps = typs_as_spec(typs, spec_map);
            Arc::new(SpecTypX::Primitive(*name, Arc::new(monotyps)))
        }
        TypX::AnonymousClosure(..) => {
            panic!("internal error: AnonymousClosure should be removed by ast_simplify")
        }
        TypX::TypeId => panic!("internal error: TypeId created too soon"),
        TypX::Air(_) => panic!("internal error: Air type created too soon"),
        TypX::TypParam(param) => {
            let Some(spec_typ) = spec_map.get(param) else {
                return Arc::new(SpecTypX::Poly);
            };
            (*spec_typ).clone()
        }
        TypX::Boxed(..) | TypX::SpecFn(..) | TypX::FnDef(..) => Arc::new(SpecTypX::Poly),
        TypX::ConstInt(_) => Arc::new(SpecTypX::Poly),
        TypX::Projection { .. } => Arc::new(SpecTypX::Poly),
        TypX::Poly => Arc::new(SpecTypX::Poly),
    }
}

pub type SpecMap = HashMap<Ident, SpecTyp>;

/**
This stores one instance of specialization of a particular function. This
structure handles deduplication of essentially isomorphic call sites.
 */
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct Specialization {
    pub typs: SpecTyps,
}
impl Specialization {
    pub fn empty() -> Self {
        Self { typs: Arc::new(vec![]) }
    }
    pub fn from_exp<'a>(exp: &'a ExpX, spec_map: &SpecMap) -> Option<(&'a Fun, Self)> {
        let ExpX::Call(CallFun::Fun(fun, _) | CallFun::Recursive(fun), typs, _) = exp else {
            return None;
        };
        let result = Self { typs: Arc::new(typs_as_spec(typs, spec_map)) };
        Some((fun, result))
    }

    fn mangle_path(path: &Dt) -> String {
        match path {
            Dt::Path(path) => {
                path.segments.iter().map(|s| s.to_string()).collect::<Vec<_>>().join("")
            }
            Dt::Tuple(i) => i.to_string(),
        }
    }

    /**
    Adds a mangled suffix to an identifier based on `SpecTypX`
     */
    pub fn transform_ident(&self, ident: Ident) -> Ident {
        if self.typs.is_empty() {
            return ident;
        }
        let suffix = SpecTypX::mangle_typs(&self.typs);
        Arc::new(ident.as_ref().clone() + &suffix)
    }

    pub fn transform_par(&self, typ_params: &Idents, par: &Par) -> Par {
        if self.typs.is_empty() {
            return par.clone();
        }
        let mut trait_typ_substs: HashMap<Ident, Typ> = HashMap::new();
        assert!(typ_params.len() == self.typs.len());
        for (x, t) in typ_params.iter().zip(self.typs.iter()) {
            trait_typ_substs.insert(x.clone(), t.to_typ());
        }
        Arc::new(Spanned {
            span: par.span.clone(), // Assuming `par` has a `span` field that needs to be copied
            x: ParX {
                name: par.x.name.clone(),
                typ: self.transform_typ(typ_params, &par.x.typ),
                mode: par.x.mode,
                is_mut: par.x.is_mut,
                purpose: par.x.purpose,
            },
        })
    }

    pub fn transform_typ(&self, typ_params: &Idents, typ: &Typ) -> Typ {
        if self.typs.is_empty() {
            return typ.clone();
        }
        let mut trait_typ_substs: HashMap<Ident, Typ> = HashMap::new();
        assert!(typ_params.len() == self.typs.len());
        for (x, t) in typ_params.iter().zip(self.typs.iter()) {
            trait_typ_substs.insert(x.clone(), t.to_typ());
        }
        let new_typ = subst_typ(&trait_typ_substs, typ);
        if poly::typ_as_mono(&new_typ).is_none() {
            return typ.clone();
        }
        new_typ
    }

    pub fn transform_exp(&self, typ_params: &Idents, ex: &Exp) -> Exp {
        if self.typs.is_empty() {
            return ex.clone();
        }
        let mut trait_typ_substs: HashMap<Ident, Typ> = HashMap::new();
        assert!(typ_params.len() == self.typs.len());
        for (x, t) in typ_params.iter().zip(self.typs.iter()) {
            trait_typ_substs.insert(x.clone(), t.to_typ());
        }
        let new_body_exp = subst_exp(&trait_typ_substs, &HashMap::new(), ex);
        new_body_exp
    }

    pub fn comment(&self) -> String {
        format!(" specialized to {:?}", &self.typs)
    }

    pub fn is_empty(&self) -> bool {
        self.typs.is_empty()
    }

    pub fn create_spec_map(&self, typ_params: &Idents) -> SpecMap {
        assert!(self.is_empty() || self.typs.len() == typ_params.len());
        std::iter::zip(typ_params.iter().cloned(), self.typs.iter().cloned()).collect()
    }
}
impl Default for Specialization {
    fn default() -> Self {
        return Self::empty();
    }
}

/**
Utility for walking through the expression tree.

This must be doubly recursive on both expressions and statements, hence its
structure mirrors `StmExpVisitorDfs`.
 */
struct SpecializationVisitor<'a> {
    invocations: Vec<(Fun, Specialization)>,
    spec_map: &'a SpecMap,
}
impl<'a> SpecializationVisitor<'a> {
    fn new(spec_map: &'a SpecMap) -> Self {
        Self { invocations: vec![], spec_map }
    }
}
impl<'a> Visitor<sst_visitor::Walk, (), sst_visitor::NoScoper> for SpecializationVisitor<'a> {
    fn visit_exp(&mut self, exp: &Exp) -> Result<(), ()> {
        if let Some((fun, spec)) = Specialization::from_exp(&exp.x, self.spec_map) {
            self.invocations.push((fun.clone(), spec))
        }
        self.visit_exp_rec(exp)
    }
    fn visit_stm(&mut self, stm: &Stm) -> Result<(), ()> {
        self.visit_stm_rec(stm)
    }
}

pub(crate) fn collect_specializations_from_function(
    spec: &Specialization,
    function: &FunctionSst,
) -> Vec<(Fun, Specialization)> {
    let spec_map = spec.create_spec_map(&function.x.typ_params);

    let mut visitor = SpecializationVisitor::new(&spec_map);
    visitor.visit_function(function).unwrap();
    visitor.invocations
}

/**
Collect all polymorphic function invocations in a module
 */
pub fn mono_krate_for_module(krate: &KrateSst) -> HashMap<Fun, HashSet<Specialization>> {
    let KrateSstX { functions, .. } = &**krate;

    let mut to_visit: VecDeque<(Specialization, &FunctionSst)> =
        functions.iter().map(|f| (Default::default(), f)).collect();
    let mut invocations: HashMap<Fun, HashSet<Specialization>> = HashMap::new();

    while let Some((caller_spec, caller_sst)) = to_visit.pop_front() {
        let sites = collect_specializations_from_function(&caller_spec, &caller_sst);
        for (callee, callee_spec) in sites.into_iter() {
            if let Some(fun_specs) = invocations.get(&callee) {
                if fun_specs.contains(&callee_spec) {
                    continue;
                }
            }
            // Push this call site back into queue
            let callee_sst = functions
                .iter()
                .find(|f| f.x.name == callee)
                .unwrap_or_else(|| panic!("Function name not found: {callee}"));
            to_visit.push_back((callee_spec.clone(), callee_sst));

            invocations.entry(callee).or_insert_with(HashSet::new).insert(callee_spec);
        }
    }
    invocations
}