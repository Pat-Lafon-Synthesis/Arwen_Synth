use std::collections::HashMap;

use crate::{
    language::Operation,
    types::{BaseType, TypeSystemBounds},
};

pub struct TypeMap<T: TypeSystemBounds> {
    // Will provide a map for each base_type since why not
    int_map: HashMap<Operation<T>, T>,
    bool_map: HashMap<Operation<T>, T>,
    list_map: HashMap<Operation<T>, T>,
    tree_map: HashMap<Operation<T>, T>,
}

impl<T: TypeSystemBounds> TypeMap<T> {
    pub fn new(l: &Vec<Operation<T>>) -> Self {
        let mut int_map = HashMap::new();
        let mut bool_map = HashMap::new();
        let mut list_map = HashMap::new();
        let mut tree_map = HashMap::new();

        l.iter().for_each(|o| {
            let ty = o.sig.output.clone();
            match ty.clone().into() {
                BaseType::Int => &mut int_map,
                BaseType::Bool => &mut bool_map,
                BaseType::IntList => &mut list_map,
                BaseType::IntTree => &mut tree_map,
            }
            .insert(o.clone(), ty);
        });

        Self {
            int_map,
            bool_map,
            list_map,
            tree_map,
        }
    }

    pub fn get_all_subtypes(&self, ty: &T) -> Vec<&Operation<T>> {
        match ty.clone().into() {
            BaseType::Int => &self.int_map,
            BaseType::Bool => &self.bool_map,
            BaseType::IntList => &self.list_map,
            BaseType::IntTree => &self.tree_map,
        }
        .iter()
        .filter_map(|(o, o_ty)| if o_ty.is_subtype(ty) { Some(o) } else { None })
        .collect()
    }
}
