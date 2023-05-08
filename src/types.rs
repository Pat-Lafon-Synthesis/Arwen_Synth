use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::ops::Deref;
use std::rc::Rc;

use itertools::Itertools;
use z3::ast::{Ast, Bool, Datatype, Dynamic, Int};
use z3::{
    Config, Context, DatatypeAccessor, DatatypeBuilder, DatatypeSort, FuncDecl, Solver, Sort,
};

use crate::language::{Constant, InvalidProg};

pub trait TypeSystemBounds:
    PartialEq + Eq + Hash + Clone + Debug + PartialOrd + Ord + From<Constant> + Display
{
}

impl TypeSystemBounds for BaseType {}
impl TypeSystemBounds for RefinementType {}

#[derive(Debug, Clone, Copy, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub enum BaseType {
    Int,
    Bool,
    IntList,
    IntTree,
}

impl Display for BaseType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                BaseType::Int => "int",
                BaseType::Bool => "bool",
                BaseType::IntList => "list",
                BaseType::IntTree => "tree",
            }
        )
    }
}

impl From<Constant> for BaseType {
    fn from(c: Constant) -> Self {
        match c {
            Constant::Int(_) => BaseType::Int,
            Constant::Bool(_) => BaseType::Bool,
            Constant::IntList(_) => BaseType::IntList,
            Constant::IntTree(_) => BaseType::IntTree,
        }
    }
}

#[derive(Clone)]
pub struct PredicateFunction<T> {
    sym: String,
    sig: Signature<T>,
    fun: Rc<dyn Fn(Vec<Constant>) -> Result<Constant, InvalidProg>>,
}

impl BaseType {
    pub fn into_z3_sort<'ctx>(&self, ctx: &'ctx Context) -> Sort<'ctx> {
        match self {
            BaseType::Int => Sort::int(ctx),
            BaseType::Bool => Sort::bool(ctx),
            _ => panic!("Not implemented"),
        }
    }
}

impl PredicateFunction<BaseType> {
    pub fn into_z3_decl<'ctx>(&self, ctx: &'ctx Context) -> FuncDecl<'ctx> {
        let args = self
            .sig
            .input
            .iter()
            .map(|ty| ty.into_z3_sort(ctx))
            .collect::<Vec<_>>();
        FuncDecl::new(
            ctx,
            self.sym.clone(),
            &args.iter().collect::<Vec<_>>(),
            &self.sig.output.into_z3_sort(ctx),
        )
    }
}

impl<T> FnOnce<(Vec<Constant>,)> for PredicateFunction<T> {
    type Output = Constant;

    extern "rust-call" fn call_once(self, args: (Vec<Constant>,)) -> Self::Output {
        (self.fun)(args.0).unwrap()
    }
}

impl<T> FnMut<(Vec<Constant>,)> for PredicateFunction<T> {
    extern "rust-call" fn call_mut(&mut self, args: (Vec<Constant>,)) -> Self::Output {
        (self.fun)(args.0).unwrap()
    }
}

impl<T> Fn<(Vec<Constant>,)> for PredicateFunction<T> {
    extern "rust-call" fn call(&self, args: (Vec<Constant>,)) -> Self::Output {
        (self.fun)(args.0).unwrap()
    }
}

impl<T> Debug for PredicateFunction<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PredicateFunction")
            .field("sym", &self.sym)
            .finish()
    }
}

impl<T> Hash for PredicateFunction<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.sym.hash(state);
    }
}

pub struct Z3Solver<'ctx> {
    pub ctx: &'ctx Context,
    pub solver: Solver<'ctx>,
    pub int_sort: Sort<'ctx>,
    pub bool_sort: Sort<'ctx>,
    pub int_list_sort: DatatypeSort<'ctx>,
    /* pub int_tree_sort: Sort<'ctx>, */
}

impl<'ctx> Z3Solver<'ctx> {
    pub fn new(ctx: &'ctx Context) -> Self {
        let solver = Solver::new(ctx);
        let int_sort = Sort::int(ctx);
        let bool_sort = Sort::bool(ctx);
        let list_sort = DatatypeBuilder::new(ctx, "ListInt")
            .variant("Nil", vec![])
            .variant(
                "Cons",
                vec![
                    ("head", DatatypeAccessor::Sort(Sort::int(ctx))),
                    ("tail", DatatypeAccessor::Datatype("ListInt".into())),
                ],
            )
            .finish();
        Z3Solver {
            ctx,
            solver,
            int_sort,
            bool_sort,
            int_list_sort: list_sort,
        }
    }
}

impl<'ctx> Deref for Z3Solver<'ctx> {
    type Target = Solver<'ctx>;

    fn deref(&self) -> &Self::Target {
        &self.solver
    }
}

// Like is done in https://github.com/liquid-rust/flux#grammar-of-refinements
#[derive(Debug, Clone)]
pub enum PredicateExpression {
    Const(Constant),                                          // -1, 0, 1
    Var(String, RefinementType),                              // x, y, z
    Plus(Box<PredicateExpression>, Box<PredicateExpression>), // e + e
    Sub(Box<PredicateExpression>, Box<PredicateExpression>),  // e - e
    Mul(Box<PredicateExpression>, Box<PredicateExpression>),  // e * e
    ITE(
        Box<Predicate>,
        Box<PredicateExpression>,
        Box<PredicateExpression>,
    ), // If p then e else e
    Func(PredicateFunction<BaseType>, Vec<PredicateExpression>), // Uninterpred Function
}

impl Display for PredicateExpression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PredicateExpression::Const(c) => write!(f, "{c}"),
            PredicateExpression::Var(v, _) => write!(f, "{v}"),
            PredicateExpression::Plus(e1, e2) => write!(f, "({} + {})", e1, e2),
            PredicateExpression::Sub(e1, e2) => write!(f, "({} - {})", e1, e2),
            PredicateExpression::Mul(e1, e2) => write!(f, "({} * {})", e1, e2),
            PredicateExpression::ITE(p, e1, e2) => write!(f, "(if {p} then {e1} else {e2})"),
            PredicateExpression::Func(func, args) => {
                write!(f, "{}({})", func.sym, args.iter().join(", "))
            }
        }
    }
}

impl PredicateExpression {
    pub fn eval(&self, map: &HashMap<String, Constant>) -> Constant {
        match self {
            PredicateExpression::Const(c) => c.clone(),
            PredicateExpression::Var(v, ty) => {
                let c = map.get(v).unwrap().clone();
                assert_eq!(Into::<BaseType>::into(c.clone()), ty.ty);
                c
            }
            PredicateExpression::Plus(e1, e2) => match (e1.eval(map), e2.eval(map)) {
                (Constant::Int(i1), Constant::Int(i2)) => Constant::Int(i1 + i2),
                (..) => panic!(),
            },
            PredicateExpression::Sub(e1, e2) => match (e1.eval(map), e2.eval(map)) {
                (Constant::Int(i1), Constant::Int(i2)) => Constant::Int(i1 - i2),
                (..) => panic!(),
            },
            PredicateExpression::Mul(e1, e2) => match (e1.eval(map), e2.eval(map)) {
                (Constant::Int(i1), Constant::Int(i2)) => Constant::Int(i1 * i2),
                (..) => panic!(),
            },
            PredicateExpression::ITE(e_cond, e1, e2) => {
                if e_cond.eval(map) {
                    e1.eval(map)
                } else {
                    e2.eval(map)
                }
            }
            PredicateExpression::Func(f, c_vec) => f(c_vec.iter().map(|e| e.eval(map)).collect()),
        }
    }

    pub fn into_z3_int<'ctx>(&self, solver: &'ctx Z3Solver) -> Int<'ctx> {
        let ctx = solver.ctx;
        match self {
            PredicateExpression::Const(Constant::Int(i)) => Int::from_i64(ctx, *i),
            PredicateExpression::Var(name, ty) => {
                assert_eq!(ty.ty, BaseType::Int);
                let i = Int::new_const(ctx, name.to_string());
                solver.assert(&ty.p.into_z3(solver));
                i
            }
            PredicateExpression::Const(c) => panic!("Not an Int? : {c}"),
            PredicateExpression::Plus(p1, p2) => p1.into_z3_int(solver) + p2.into_z3_int(solver),
            PredicateExpression::Sub(p1, p2) => p1.into_z3_int(solver) - p2.into_z3_int(solver),
            PredicateExpression::Mul(p1, p2) => p1.into_z3_int(solver) * p2.into_z3_int(solver),
            PredicateExpression::ITE(e, p1, p2) => e
                .into_z3(solver)
                .ite(&p1.into_z3_int(solver), &p2.into_z3_int(solver)),
            PredicateExpression::Func(f, args) => {
                let args = args
                    .iter()
                    .zip(f.sig.input.iter())
                    .map(|(e, t)| match t {
                        BaseType::Int => e.into_z3_int(solver).into(),
                        BaseType::Bool => e.into_z3_bool(solver).into(),
                        BaseType::IntList => todo!(),
                        BaseType::IntTree => todo!(),
                    })
                    .collect::<Vec<Dynamic<'ctx>>>();
                f.into_z3_decl(ctx)
                    .apply(
                        args.iter()
                            .map(|a| a as &dyn Ast<'ctx>)
                            .collect::<Vec<_>>()
                            .as_slice(),
                    )
                    .as_int()
                    .unwrap()
            }
        }
    }

    pub fn into_z3_bool<'ctx>(&self, solver: &'ctx Z3Solver) -> Bool<'ctx> {
        let ctx = solver.ctx;
        match self {
            PredicateExpression::Const(Constant::Bool(b)) => Bool::from_bool(ctx, *b),
            PredicateExpression::Var(name, ty) => {
                assert_eq!(ty.ty, BaseType::Bool);
                let b = Bool::new_const(ctx, name.to_string());
                solver.assert(&ty.p.into_z3(solver));
                b
            }
            PredicateExpression::Const(c) => panic!("Not a Bool? : {c}"),
            PredicateExpression::Plus(..)
            | PredicateExpression::Sub(..)
            | PredicateExpression::Mul(..) => {
                panic!("Not a Bool? : {self:?}")
            }
            PredicateExpression::ITE(e, p1, p2) => e
                .into_z3(solver)
                .ite(&p1.into_z3_bool(solver), &p2.into_z3_bool(solver)),
            PredicateExpression::Func(f, args) => {
                let args = args
                    .iter()
                    .zip(f.sig.input.iter())
                    .map(|(e, t)| match t {
                        BaseType::Int => e.into_z3_int(solver).into(),
                        BaseType::Bool => e.into_z3_bool(solver).into(),
                        BaseType::IntList => e.into_z3_int_list(solver),
                        BaseType::IntTree => todo!(),
                    })
                    .collect::<Vec<Dynamic<'ctx>>>();
                f.into_z3_decl(ctx)
                    .apply(
                        args.iter()
                            .map(|a| a as &dyn Ast<'ctx>)
                            .collect::<Vec<_>>()
                            .as_slice(),
                    )
                    .as_bool()
                    .unwrap()
            }
        }
    }

    pub fn into_z3_int_list<'ctx>(&self, solver: &'ctx Z3Solver) -> Dynamic<'ctx> {
        match self {
            PredicateExpression::Const(Constant::IntList(_)) => todo!(),
            PredicateExpression::Var(name, ty) => {
                assert_eq!(ty.ty, BaseType::IntList);
                let l = Datatype::new_const(solver.ctx, name.as_str(), &solver.int_list_sort.sort);
                solver.assert(&ty.p.into_z3(solver));
                l.into()
            }
            PredicateExpression::Const(_)
            | PredicateExpression::Plus(..)
            | PredicateExpression::Sub(..)
            | PredicateExpression::Mul(..) => panic!("Not a list? : {self:?}"),
            PredicateExpression::ITE(b, t, e) => {
                assert!(t.is_int_list());
                assert!(e.is_int_list());
                b.into_z3(solver)
                    .ite(&t.into_z3_int_list(solver), &e.into_z3_int_list(solver))
            }
            PredicateExpression::Func(..) => todo!(),
        }
    }

    pub fn is_bool(&self) -> bool {
        match self {
            PredicateExpression::Const(Constant::Bool(_)) => true,
            PredicateExpression::Var(_, ty) => ty.ty == BaseType::Bool,
            PredicateExpression::Const(_)
            | PredicateExpression::Plus(..)
            | PredicateExpression::Sub(..)
            | PredicateExpression::Mul(..) => false,
            PredicateExpression::ITE(_, p1, p2) => p1.is_bool() && p2.is_bool(),
            PredicateExpression::Func(PredicateFunction { sig, .. }, _) => {
                sig.output == BaseType::Bool
            }
        }
    }

    pub fn is_int(&self) -> bool {
        match self {
            PredicateExpression::Const(Constant::Int(_)) => true,
            PredicateExpression::Var(_, ty) => ty.ty == BaseType::Int,
            PredicateExpression::Const(_) => false,
            PredicateExpression::Plus(..)
            | PredicateExpression::Sub(..)
            | PredicateExpression::Mul(..) => true,
            PredicateExpression::ITE(_, p1, p2) => p1.is_int() && p2.is_int(),
            PredicateExpression::Func(PredicateFunction { sig, .. }, _) => {
                sig.output == BaseType::Int
            }
        }
    }

    pub fn is_int_list(&self) -> bool {
        match self {
            PredicateExpression::Const(Constant::IntList(_)) => true,
            PredicateExpression::Var(_, ty) => ty.ty == BaseType::IntList,
            PredicateExpression::Const(_) => false,
            PredicateExpression::Plus(..)
            | PredicateExpression::Sub(..)
            | PredicateExpression::Mul(..) => false,
            PredicateExpression::ITE(_, p1, p2) => p1.is_int_list() && p2.is_int_list(),
            PredicateExpression::Func(PredicateFunction { sig, .. }, _) => {
                sig.output == BaseType::IntList
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum Predicate {
    Bool(bool),
    Equal(Box<PredicateExpression>, Box<PredicateExpression>), // e = e
    Less(Box<PredicateExpression>, Box<PredicateExpression>),  // e < e
    Conj(Box<Predicate>, Box<Predicate>),                      // p && p
    Disj(Box<Predicate>, Box<Predicate>),                      // p || p
    Impl(Box<Predicate>, Box<Predicate>),                      // p => p
    Neg(Box<Predicate>),                                       // !p
}

impl Display for Predicate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Predicate::Bool(b) => write!(f, "{b}"),
            Predicate::Equal(e1, e2) => write!(f, "({e1} = {e2})"),
            Predicate::Less(e1, e2) => write!(f, "{e1} < {e2}"),
            Predicate::Conj(p1, p2) => write!(f, "({p1} && {p2})"),
            Predicate::Disj(p1, p2) => write!(f, "({p1} || {p2})"),
            Predicate::Impl(p1, p2) => write!(f, "({p1} => {p2})"),
            Predicate::Neg(b) => write!(f, "!{b}"),
        }
    }
}

impl Predicate {
    pub fn eval(&self, map: &HashMap<String, Constant>) -> bool {
        match self {
            Predicate::Bool(b) => *b,
            Predicate::Equal(e1, e2) => e1.eval(map) == e2.eval(map),
            Predicate::Less(e1, e2) => e1.eval(map) < e2.eval(map),
            Predicate::Conj(e1, e2) => e1.eval(map) && e2.eval(map),
            Predicate::Disj(e1, e2) => e1.eval(map) || e2.eval(map),
            Predicate::Impl(e1, e2) => {
                if e1.eval(map) {
                    e2.eval(map)
                } else {
                    true
                }
            }
            Predicate::Neg(e) => !e.eval(map),
        }
    }

    pub fn into_z3<'ctx>(&self, solver: &'ctx Z3Solver) -> Bool<'ctx> {
        let ctx = solver.get_context();
        match self {
            Predicate::Bool(b) => Bool::from_bool(ctx, *b),
            Predicate::Equal(p1, p2) if p1.is_bool() || p2.is_bool() => {
                p1.into_z3_bool(solver)._eq(&p2.into_z3_bool(solver))
            }
            Predicate::Equal(p1, p2) => p1.into_z3_int(solver)._eq(&p2.into_z3_int(solver)),
            Predicate::Less(p1, p2) => p1.into_z3_int(solver).lt(&p2.into_z3_int(solver)),
            Predicate::Conj(e1, e2) => Bool::and(ctx, &[&e1.into_z3(solver), &e2.into_z3(solver)]),
            Predicate::Disj(e1, e2) => Bool::or(ctx, &[&e1.into_z3(solver), &e2.into_z3(solver)]),
            Predicate::Impl(b1, b2) => b1.into_z3(solver).implies(&b2.into_z3(solver)),
            Predicate::Neg(b) => b.into_z3(solver).not(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct RefinementType {
    pub ty: BaseType,
    pub p: Predicate,
}

impl RefinementType {
    fn prove(solver: &Solver, claim: &Bool) -> bool {
        solver.assert(&claim.not());
        match solver.check() {
            z3::SatResult::Unsat => {
                eprintln!("Proved: {claim}");
                true
            }
            z3::SatResult::Unknown => {
                eprintln!("Error: result unknown");
                false
            }
            z3::SatResult::Sat => {
                eprintln!("False:\n{}", solver.get_model().unwrap());
                false
            }
        }
    }

    pub fn is_sub_type(
        &self,
        RefinementType {
            ty: super_ty,
            p: super_p,
        }: &RefinementType,
    ) -> bool {
        let RefinementType {
            ty: sub_ty,
            p: sub_p,
        } = self;
        if sub_ty != super_ty {
            return false;
        }
        let cfg = Config::new();
        let ctx = &Context::new(&cfg);
        let solver = Z3Solver::new(ctx);

        // goal is to say that something implies something else
        // "Prove" by doing the negation

        let x = RefinementType::prove(
            &solver,
            &sub_p.into_z3(&solver).implies(&super_p.into_z3(&solver)),
        );
        x
    }
}

impl From<Constant> for RefinementType {
    fn from(value: Constant) -> Self {
        match value {
            Constant::Int(i) => RefinementType {
                ty: BaseType::Int,
                p: Predicate::Equal(
                    Box::new(PredicateExpression::Const(Constant::Int(i))),
                    Box::new(PredicateExpression::Var(
                        "v".to_string(),
                        RefinementType {
                            ty: BaseType::Int,
                            p: Predicate::Bool(true),
                        },
                    )),
                ),
            },
            Constant::Bool(b) => RefinementType {
                ty: BaseType::Bool,
                p: Predicate::Equal(
                    Box::new(PredicateExpression::Const(Constant::Bool(b))),
                    Box::new(PredicateExpression::Var(
                        "v".to_string(),
                        RefinementType {
                            ty: BaseType::Bool,
                            p: Predicate::Bool(true),
                        },
                    )),
                ),
            },
            Constant::IntList(l) => RefinementType {
                ty: BaseType::IntList,
                p: Predicate::Equal(
                    Box::new(PredicateExpression::Const(Constant::IntList(l))),
                    Box::new(PredicateExpression::Var(
                        "v".to_string(),
                        RefinementType {
                            ty: BaseType::IntList,
                            p: Predicate::Bool(true),
                        },
                    )),
                ),
            },
            Constant::IntTree(t) => RefinementType {
                ty: BaseType::IntTree,
                p: Predicate::Equal(
                    Box::new(PredicateExpression::Const(Constant::IntTree(t))),
                    Box::new(PredicateExpression::Var(
                        "v".to_string(),
                        RefinementType {
                            ty: BaseType::IntTree,
                            p: Predicate::Bool(true),
                        },
                    )),
                ),
            },
        }
    }
}

impl PartialEq for RefinementType {
    fn eq(&self, other: &Self) -> bool {
        self.ty == other.ty
    }
}

impl Eq for RefinementType {}

impl PartialOrd for RefinementType {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.ty.partial_cmp(&other.ty)
    }
}

impl Ord for RefinementType {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.ty.cmp(&other.ty)
    }
}

impl Hash for RefinementType {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.ty.hash(state);
    }
}

impl Display for RefinementType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{{{} | {}}}",
            match self.ty {
                BaseType::Int => "int",
                BaseType::Bool => "bool",
                BaseType::IntList => "list",
                BaseType::IntTree => "tree",
            },
            self.p
        )
    }
}

impl From<BaseType> for RefinementType {
    fn from(value: BaseType) -> Self {
        RefinementType {
            ty: value,
            p: Predicate::Bool(true),
        }
    }
}

impl From<RefinementType> for BaseType {
    fn from(value: RefinementType) -> Self {
        value.ty
    }
}

#[derive(Debug, Clone)]
pub struct Signature<T> {
    pub input: Vec<T>,
    pub output: T,
}

impl From<Signature<RefinementType>> for Signature<BaseType> {
    fn from(value: Signature<RefinementType>) -> Self {
        Signature {
            input: value.input.into_iter().map(Into::into).collect(),
            output: value.output.into(),
        }
    }
}

impl From<Signature<BaseType>> for Signature<RefinementType> {
    fn from(value: Signature<BaseType>) -> Self {
        Signature {
            input: value.input.into_iter().map(Into::into).collect(),
            output: value.output.into(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diff_base_subtype() {
        let ref1 = RefinementType {
            ty: BaseType::Bool,
            p: Predicate::Bool(true),
        };
        let ref2 = RefinementType {
            ty: BaseType::Int,
            p: Predicate::Bool(true),
        };
        assert!(!ref1.is_sub_type(&ref2));
        assert!(!ref2.is_sub_type(&ref1));
    }

    #[test]
    fn same_base_subtype() {
        let ref1 = RefinementType {
            ty: BaseType::Int,
            p: Predicate::Bool(true),
        };
        let ref2 = RefinementType {
            ty: BaseType::Int,
            p: Predicate::Bool(true),
        };
        assert!(ref1.is_sub_type(&ref2));
        assert!(ref2.is_sub_type(&ref1));
    }

    #[test]
    fn true_false_subtype() {
        let ref1 = RefinementType {
            ty: BaseType::Int,
            p: Predicate::Bool(true),
        };
        let ref2 = RefinementType {
            ty: BaseType::Int,
            p: Predicate::Bool(false),
        };
        assert!(!ref1.is_sub_type(&ref2));
        assert!(ref2.is_sub_type(&ref1));
    }

    #[test]
    fn size_int_subtype() {
        let ref1 = RefinementType {
            ty: BaseType::Int,
            p: Predicate::Less(
                PredicateExpression::Var("v".to_string(), BaseType::Int.into()).into(),
                PredicateExpression::Const(Constant::Int(5)).into(),
            ),
        };
        let ref2 = RefinementType {
            ty: BaseType::Int,
            p: Predicate::Less(
                PredicateExpression::Var("v".to_string(), BaseType::Int.into()).into(),
                PredicateExpression::Const(Constant::Int(6)).into(),
            ),
        };
        assert!(ref1.is_sub_type(&ref2));
        assert!(!ref2.is_sub_type(&ref1));
    }

    #[test]
    fn mixed_pred_subtype() {
        let ref1 = RefinementType {
            ty: BaseType::Int,
            p: Predicate::Bool(true),
        };
        let ref2 = RefinementType {
            ty: BaseType::Int,
            p: Predicate::Equal(
                PredicateExpression::Var("v".to_string(), BaseType::Int.into()).into(),
                PredicateExpression::Const(Constant::Int(0)).into(),
            ),
        };
        assert!(!ref1.is_sub_type(&ref2));
        assert!(ref2.is_sub_type(&ref1));
    }

    #[test]
    fn zero_rules_subtype() {
        let ref1 = RefinementType {
            ty: BaseType::Int,
            p: Predicate::Equal(
                PredicateExpression::Var("v".to_string(), BaseType::Int.into()).into(),
                PredicateExpression::Const(Constant::Int(0)).into(),
            ),
        };
        let ref2 = RefinementType {
            ty: BaseType::Int,
            p: Predicate::Less(
                PredicateExpression::Var("v".to_string(), BaseType::Int.into()).into(),
                PredicateExpression::Const(Constant::Int(100)).into(),
            ),
        };
        let ref3 = RefinementType {
            ty: BaseType::Int,
            p: Predicate::Neg(
                Predicate::Less(
                    PredicateExpression::Const(Constant::Int(0)).into(),
                    PredicateExpression::Var("v".to_string(), BaseType::Int.into()).into(),
                )
                .into(),
            ),
        };
        assert!(ref1.is_sub_type(&ref2));
        assert!(ref1.is_sub_type(&ref3));
        assert!(!ref2.is_sub_type(&ref1));
        assert!(!ref3.is_sub_type(&ref1));
    }

    #[test]
    fn uninterpreted_non_zero_subtype() {
        let is_zero = Rc::new(|args: Vec<Constant>| match args.get(1).unwrap() {
            Constant::Int(0) => Ok(Constant::Bool(true)),
            Constant::Int(_) => Ok(Constant::Bool(false)),
            _ => panic!(),
        });

        let ref1 = RefinementType {
            ty: BaseType::Int,
            p: Predicate::Equal(
                PredicateExpression::Const(Constant::Bool(true)).into(),
                PredicateExpression::Func(
                    PredicateFunction {
                        sym: "is_zero".to_string(),
                        fun: is_zero.clone(),
                        sig: Signature {
                            input: vec![BaseType::Int],
                            output: BaseType::Bool,
                        },
                    },
                    vec![PredicateExpression::Var(
                        "v".to_string(),
                        BaseType::Int.into(),
                    )],
                )
                .into(),
            ),
        };

        let ref_1 = RefinementType {
            ty: BaseType::Int,
            p: Predicate::Equal(
                PredicateExpression::Const(Constant::Bool(true)).into(),
                PredicateExpression::Func(
                    PredicateFunction {
                        sym: "is_zero".to_string(),
                        fun: is_zero.clone(),
                        sig: Signature {
                            input: vec![BaseType::Int],
                            output: BaseType::Bool,
                        },
                    },
                    vec![PredicateExpression::Var(
                        "v".to_string(),
                        BaseType::Int.into(),
                    )],
                )
                .into(),
            ),
        };

        let ref2 = RefinementType {
            ty: BaseType::Int,
            p: Predicate::Bool(true),
        };

        let ref3 = RefinementType {
            ty: BaseType::Int,
            p: Predicate::Equal(
                PredicateExpression::Const(Constant::Bool(true)).into(),
                PredicateExpression::Func(
                    PredicateFunction {
                        sym: "is_zero".to_string(),
                        fun: is_zero,
                        sig: Signature {
                            input: vec![BaseType::Int],
                            output: BaseType::Bool,
                        },
                    },
                    vec![PredicateExpression::Var(
                        "r".to_string(),
                        BaseType::Int.into(),
                    )],
                )
                .into(),
            ),
        };

        assert!(ref1.is_sub_type(&ref1));
        assert!(ref1.is_sub_type(&ref_1));
        assert!(ref_1.is_sub_type(&ref1));
        assert!(ref1.is_sub_type(&ref2));
        assert!(!ref2.is_sub_type(&ref1));
        assert!(!ref1.is_sub_type(&ref3));
        assert!(!ref3.is_sub_type(&ref1));
    }
}
