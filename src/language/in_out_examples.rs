use std::{
    fmt::{Debug, Display},
    ops::Deref,
};

use itertools::Itertools;
use log::info;

use crate::{data_structures::InverseMap, types::TypeSystemBounds};

use super::{Constant, Environment, Operation, Program, Variable};

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub struct TestCase {
    pub inputs: Vec<Constant>,
    pub output: Constant,
}

impl TestCase {
    pub fn into_env<T: TypeSystemBounds>(&self) -> Environment<T> {
        let TestCase { inputs, .. } = self;
        inputs
            .iter()
            .enumerate()
            .map(|(i, c)| {
                (
                    Variable {
                        name: format!("arg{i:?}"),
                        ty: Into::<T>::into(c.clone()),
                    },
                    c.clone(),
                )
            })
            .collect()
    }
}

#[derive(Clone, PartialEq, Eq)]
pub struct Examples(Vec<TestCase>);

impl Deref for Examples {
    type Target = Vec<TestCase>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Debug for Examples {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

impl From<Vec<TestCase>> for Examples {
    fn from(value: Vec<TestCase>) -> Self {
        Examples(value)
    }
}

impl IntoIterator for Examples {
    type Item = TestCase;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl Examples {
    pub fn new(tests: Vec<TestCase>) -> Self {
        Examples(tests)
    }

    pub fn filter_behavior<T: TypeSystemBounds, P: Fn(&Constant) -> bool>(
        &self,
        cond: Program<T>,
        predicate: P,
    ) -> Examples {
        self.clone()
            .into_iter()
            .filter(|t| {
                let e = t.into_env();
                if let Ok(res) = cond.interpret(&e) {
                    assert!(matches!(res, Constant::Bool(_)));
                    predicate(&res)
                } else {
                    info!("Had an invalid program while filtering behaviour");
                    false
                }
            })
            .collect::<Vec<TestCase>>()
            .into()
    }

    /// Provide a list of examples for each argument of the operation.
    /// TODO, this may be a source of confusion... will have to wait and see
    pub fn witness_examples<T: TypeSystemBounds>(
        &self,
        o: &Operation<T>,
        inverse_map: &InverseMap<T>,
    ) -> Vec<Vec<Examples>> {
        (0..o.sig.input.len())
            .map(|idx| inverse_map.inverse_app(o, self, idx))
            .collect()
    }
}

impl Display for TestCase {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({}) -> {}",
            self.inputs.iter().map(ToString::to_string).join(","),
            self.output
        )
    }
}
