use std::{cmp::Reverse, collections::BinaryHeap, fmt::Display, iter::Map};

use itertools::Itertools;

pub trait SynthCostFunc {
    fn cost(&self) -> usize;
}

#[derive(Clone, Debug)]
pub struct Inner<T> {
    item: T,
    cost: usize,
}

impl<T: SynthCostFunc> Inner<T> {
    fn new(item: T) -> Self {
        let cost = item.cost();
        Inner { item, cost }
    }
}

impl<T> PartialEq for Inner<T> {
    fn eq(&self, other: &Self) -> bool {
        self.cost == other.cost
    }
}

impl<T> Eq for Inner<T> {}

impl<T> PartialOrd for Inner<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.cost.partial_cmp(&other.cost)
    }
}

impl<T> Ord for Inner<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

#[derive(Clone, Default, Debug)]
pub struct MinHeap<T: SynthCostFunc>(BinaryHeap<Reverse<Inner<T>>>);

impl<T: SynthCostFunc> MinHeap<T> {
    pub fn new() -> Self {
        MinHeap(BinaryHeap::new())
    }

    pub fn push(&mut self, item: T) {
        self.0.push(Reverse(Inner::new(item)))
    }

    pub fn pop(&mut self) -> Option<T> {
        self.0.pop().map(|Reverse(Inner { item, .. })| item)
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn extend(&mut self, other: MinHeap<T>) {
        self.0.extend(other.0.into_iter())
    }
}

impl<T: SynthCostFunc> FromIterator<T> for MinHeap<T> {
    fn from_iter<R: IntoIterator<Item = T>>(iter: R) -> Self {
        MinHeap(iter.into_iter().map(|i| Reverse(Inner::new(i))).collect())
    }
}

impl<T: SynthCostFunc> IntoIterator for MinHeap<T> {
    type Item = T;

    type IntoIter = Map<
        std::collections::binary_heap::IntoIter<Reverse<Inner<T>>>,
        impl FnMut(Reverse<Inner<T>>) -> T,
    >;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter().map(|Reverse(Inner { item, .. })| item)
    }
}

impl<T: SynthCostFunc + Display> Display for MinHeap<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[\n\t{}\n]",
            self.0
                .iter()
                .map(|Reverse(Inner { item, .. })| item.to_string())
                .collect_vec()
                .join("\n\t")
        )
    }
}
