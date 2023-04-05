use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::rc::Rc;

use z3::ast::{Ast, Bool, Int};
use z3::{Config, Context, Solver};

use crate::language::Constant;

#[derive(Debug, Clone, Copy, PartialEq, Hash, Eq, PartialOrd, Ord)]
pub enum BaseType {
    Int,
    Bool,
    IntList,
    IntTree,
}

impl From<&Constant> for BaseType {
    fn from(c: &Constant) -> Self {
        match c {
            Constant::Int(_) => BaseType::Int,
            Constant::Bool(_) => BaseType::Bool,
            Constant::IntList(_) => BaseType::IntList,
            Constant::IntTree(_) => BaseType::IntTree,
        }
    }
}

#[derive(Clone)]
pub struct PredicateFunction {
    sym: String,
    fun: Rc<dyn Fn(Vec<Constant>) -> Constant>,
}

impl FnOnce<(Vec<Constant>,)> for PredicateFunction {
    type Output = Constant;

    extern "rust-call" fn call_once(self, args: (Vec<Constant>,)) -> Self::Output {
        (self.fun)(args.0)
    }
}

impl FnMut<(Vec<Constant>,)> for PredicateFunction {
    extern "rust-call" fn call_mut(&mut self, args: (Vec<Constant>,)) -> Self::Output {
        (self.fun)(args.0)
    }
}

impl Fn<(Vec<Constant>,)> for PredicateFunction {
    extern "rust-call" fn call(&self, args: (Vec<Constant>,)) -> Self::Output {
        (self.fun)(args.0)
    }
}

impl Debug for PredicateFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PredicateFunction")
            .field("sym", &self.sym)
            .finish()
    }
}

impl Hash for PredicateFunction {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.sym.hash(state);
    }
}

// Like is done in https://github.com/liquid-rust/flux#grammar-of-refinements
#[derive(Debug, Clone)]
pub enum PredicateExpression {
    Const(Constant),                                          // -1, 0, 1
    Var(String),                                              // x, y, z
    Plus(Box<PredicateExpression>, Box<PredicateExpression>), // e + e
    Sub(Box<PredicateExpression>, Box<PredicateExpression>),  // e - e
    Mul(Box<PredicateExpression>, Box<PredicateExpression>),  // e * e
    ITE(
        Box<Predicate>,
        Box<PredicateExpression>,
        Box<PredicateExpression>,
    ), // If p then e else e
    Func(PredicateFunction, Vec<PredicateExpression>),        // Uninterpred Function
}

impl PredicateExpression {
    pub fn eval(&self, map: &HashMap<String, Constant>) -> Constant {
        match self {
            PredicateExpression::Const(c) => c.clone(),
            PredicateExpression::Var(v) => map.get(v).unwrap().clone(),
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

    pub fn into_z3_int<'ctx>(&self, ctx: &'ctx Context) -> Int<'ctx> {
        match self {
            PredicateExpression::Const(Constant::Int(i)) => Int::from_i64(ctx, *i),
            PredicateExpression::Var(name) => Int::new_const(ctx, name.to_string()),
            PredicateExpression::Const(..) => panic!("Not an Int?"),
            PredicateExpression::Plus(p1, p2) => p1.into_z3_int(ctx) + p2.into_z3_int(ctx),
            PredicateExpression::Sub(p1, p2) => p1.into_z3_int(ctx) - p2.into_z3_int(ctx),
            PredicateExpression::Mul(p1, p2) => p1.into_z3_int(ctx) * p2.into_z3_int(ctx),
            PredicateExpression::ITE(e, p1, p2) => e
                .into_z3(ctx)
                .ite(&p1.into_z3_int(ctx), &p2.into_z3_int(ctx)),
            PredicateExpression::Func(..) => todo!(),
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

    pub fn into_z3<'ctx>(&self, ctx: &'ctx Context) -> Bool<'ctx> {
        match self {
            Predicate::Bool(b) => Bool::from_bool(ctx, *b),
            Predicate::Equal(p1, p2) => p1.into_z3_int(ctx)._eq(&p2.into_z3_int(ctx)),
            Predicate::Less(p1, p2) => p1.into_z3_int(ctx).lt(&p2.into_z3_int(ctx)),
            Predicate::Conj(e1, e2) => Bool::and(ctx, &[&e1.into_z3(ctx), &e2.into_z3(ctx)]),
            Predicate::Disj(e1, e2) => Bool::or(ctx, &[&e1.into_z3(ctx), &e2.into_z3(ctx)]),
            Predicate::Impl(b1, b2) => b1.into_z3(ctx).implies(&b2.into_z3(ctx)),
            Predicate::Neg(b) => b.into_z3(ctx).not(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct RefinementType {
    pub ty: BaseType,
    pub p: Predicate,
}

impl RefinementType {
    fn prove(ctx: &Context, claim: &Bool) -> bool {
        let solver = Solver::new(ctx);
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
    // Z3_SYS_Z3_HEADER="/usr/local/bin/z3.h"
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
        let ctx = Context::new(&cfg);

        // goal is to say that something implies something else
        // "Prove" by doing the negation

        let x = RefinementType::prove(&ctx, &sub_p.into_z3(&ctx).implies(&super_p.into_z3(&ctx)));
        x
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
                PredicateExpression::Var("x".to_string()).into(),
                PredicateExpression::Const(Constant::Int(5)).into(),
            ),
        };
        let ref2 = RefinementType {
            ty: BaseType::Int,
            p: Predicate::Less(
                PredicateExpression::Var("x".to_string()).into(),
                PredicateExpression::Const(Constant::Int(6)).into(),
            ),
        };
        assert!(ref1.is_sub_type(&ref2));
        assert!(!ref2.is_sub_type(&ref1));
    }
}
