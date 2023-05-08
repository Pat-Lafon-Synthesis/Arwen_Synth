use std::{cmp::Reverse, collections::BinaryHeap, iter::Map};

#[derive(Clone, Default)]
pub struct MinHeap<T: Ord>(BinaryHeap<Reverse<T>>);

impl<T: Ord> MinHeap<T> {
    pub fn new() -> Self {
        MinHeap(BinaryHeap::new())
    }

    pub fn push(&mut self, item: T) {
        self.0.push(Reverse(item))
    }

    pub fn pop(&mut self) -> Option<T> {
        self.0.pop().map(|Reverse(item)| item)
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<T: Ord> FromIterator<T> for MinHeap<T> {
    fn from_iter<R: IntoIterator<Item = T>>(iter: R) -> Self {
        MinHeap(iter.into_iter().map(Reverse).collect())
    }
}

impl<T: Ord> IntoIterator for MinHeap<T> {
    type Item = T;

    type IntoIter =
        Map<std::collections::binary_heap::IntoIter<Reverse<T>>, impl FnMut(Reverse<T>) -> T>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter().map(|Reverse(item)| item)
    }
}
