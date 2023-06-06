#![feature(unboxed_closures)]
#![feature(fn_traits)]
#![feature(slice_group_by)]
#![feature(const_option)]
#![feature(impl_trait_in_assoc_type)]

pub mod data_structures;
pub mod language;
pub mod parser_interface;
pub mod types;

use log::{info, warn};
use std::fmt::Display;
use std::hash::Hash;
use std::num::NonZeroU8;

use data_structures::*;
use language::*;
use types::*;

use ecta_rs::{ECTANode, Edge, ECTA};

const IF_DEPTH: usize = 1;
const MAX_FRAG_SIZE: NonZeroU8 = NonZeroU8::new(3).unwrap();

type Libraries<T> = Vec<Operation<T>>;

fn transpose<T>(v: Vec<Vec<T>>) -> Vec<Vec<T>> {
    assert!(!v.is_empty());
    let len = v[0].len();
    let mut iters: Vec<_> = v.into_iter().map(|n| n.into_iter()).collect();
    (0..len)
        .map(|_| {
            iters
                .iter_mut()
                .map(|n| n.next().unwrap())
                .collect::<Vec<T>>()
        })
        .collect()
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum SynthEctaEdge<T: TypeSystemBounds> {
    P(LinearProgramNode<T>),
    T(T),
}

impl<'a, T: TypeSystemBounds> TryFrom<&'a SynthEctaEdge<T>> for &'a LinearProgramNode<T> {
    type Error = ();

    fn try_from(value: &'a SynthEctaEdge<T>) -> Result<Self, Self::Error> {
        match value {
            SynthEctaEdge::P(p) => Ok(p),
            _ => Err(()),
        }
    }
}

impl<T: TypeSystemBounds> Display for SynthEctaEdge<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SynthEctaEdge::P(p) => write!(f, "{}", p),
            SynthEctaEdge::T(t) => write!(f, "{}", t),
        }
    }
}

pub type SynthEcta<T> = ECTA<SynthEctaEdge<T>, ()>;
pub type SynthEdge<T> = Edge<LinearProgramNode<T>, ()>;

#[derive(Clone)]
pub struct SynthesizerState<'a, T: TypeSystemBounds> {
    pub ecta: &'a SynthEcta<T>,
    pub inverse_map: &'a InverseMap<T>,
    /// Fragment candidates for boolean conditions
    pub bool_fragments: &'a Vec<&'a Fragment<T>>,
    /// Signature to reconstruct for a recursive function call
    pub sig: &'a Signature<T>,
    pub fragment_collection: &'a FragmentCollection<T>,
    /* #[cfg(debug_assertions)] */
    /// For debugging purposes
    pub start_node: ECTANode,
    pub type_map: &'a TypeMap<T>,
}

impl<'a, T: TypeSystemBounds> SynthesizerState<'a, T> {
    pub fn new(
        ecta: &'a ECTA<SynthEctaEdge<T>, ()>,
        inverse_map: &'a InverseMap<T>,
        bool_fragments: &'a Vec<&'a Fragment<T>>,
        sig: &'a Signature<T>,
        fragment_collection: &'a FragmentCollection<T>,
        type_map: &'a TypeMap<T>,
        /* #[cfg(debug_assertions)] */ start_node: ECTANode,
    ) -> Self {
        Self {
            ecta,
            inverse_map,
            bool_fragments,
            sig,
            fragment_collection,
            type_map,
            /* #[cfg(debug_assertions)] */
            start_node,
        }
    }
}

fn deduce2<T: TypeSystemBounds>(
    state: SynthesizerState<T>,
    node: ECTANode,
    hole: Examples,
    target_type: T,
) -> Option<Program<T>> {
    info!("start deduction");
    if node == state.ecta.empty_node && !hole.get_positive_examples().is_empty() {
        warn!("Empty node in deduce");
        panic!();
    }

    let well_typed = target_type.is_non_trivial();

    let initial = SketchWithData::from_hole(target_type, node, hole.clone(), well_typed);

    info!("Initial sketch = {initial}");

    let mut queue = MinHeap::new();
    queue.push(initial);

    info!("Hole trying to fill = {hole}");
    while let Some(sketch) = queue.pop() {
        info!("Sketch in consideration = {sketch}");
        for s in sketch.fill_hole(&state, &hole) {
            if s.is_complete() {
                info!("Complete sketch = {s}");
                return s.try_into().ok();
            } else {
                info!("Pushed sketch onto the queue = {s}");
                queue.push(s);
            }
        }
    }

    None
}

fn top_down_prop<T: TypeSystemBounds>(
    hole: Examples,
    traces: Vec<&Fragment<T>>,
    inverse_map: &InverseMap<T>,
    type_map: &TypeMap<T>,
    fragment_collection: &FragmentCollection<T>,
    signature: &Signature<T>,
) -> Option<Program<T>> {
    let target_type = signature.output.clone();

    info!("Starting top down propagation...");

    // Bail out early if there are no traces
    // But we have examples to work off of
    if traces.is_empty() && !hole.get_positive_examples().is_empty() {
        info!("No traces to propagate from");
        return None;
    }

    let mut ecta = ECTA::new();
    let top_node = create_ecta_from_traces(
        &mut ecta,
        &mut traces
            .iter()
            .map(|Fragment { fragment, .. }| fragment)
            .collect::<Vec<_>>(),
    );

    info!(
        "Ecta = {}",
        ecta.get_dot(&[petgraph::dot::Config::NodeIndexLabel])
    );

    // Used in generating if conditions
    // Instead of filtering on whether it contains variables or in additon to, filter if that boolean fragment actually has different behaviour on the examples
    // Or have two lists, one for fragments that work in the inductive case, and one with additional examples for the deductive case
    let bool_fragments = fragment_collection
        .get_all_sorted(&BaseType::Bool.into())
        .into_iter()
        .filter(|f| f.contains_variable())
        .collect();

    /*     cfg_if::cfg_if! {
    if #[cfg(debug_assertions)] { */
    let synthesis_state = SynthesizerState::new(
        &ecta,
        inverse_map,
        &bool_fragments,
        signature,
        fragment_collection,
        type_map,
        top_node,
    );
    /*         } else {
            let synthesis_state = SynthesizerState::new(&ecta, inverse_map, &bool_fragments, signature, fragment_collection, type_map);
        }
    } */

    let prog_iter = deduce2(synthesis_state, top_node, hole.clone(), target_type);

    prog_iter.filter(|p| {
        hole.is_consistent_with(|t| {
            p.interpret(&t.into(), p)
                .map_or(false, |output| output == t.output)
        })
    })
}

pub fn synthesis<T: TypeSystemBounds>(
    sig: Signature<T>,
    l: &Libraries<T>,
    tests: Examples,
    mut size: u8,
) -> Option<Program<T>> {
    use std::io::Write;
    let _ = env_logger::builder()
        .format(|buf, record| {
            writeln!(
                buf,
                "{}:{} [{}] - {}",
                record.file().unwrap_or("unknown"),
                record.line().unwrap_or(0),
                record.level(),
                record.args()
            )
        })
        .try_init();
    let variables = sig
        .input
        .iter()
        .enumerate()
        .map(|(i, ty)| Variable {
            name: format!("arg{i}"),
            ty: ty.clone(),
        })
        .collect();
    let mut frags = FragmentCollection::new(variables, l, tests.clone());

    let type_map = TypeMap::new(l);

    while size > 1 {
        frags.increment(l, &tests.get_all_examples());
        size -= 1;
    }

    info!("Starting synthesis...");
    info!("Incoming tests = {:#?}", tests);

    loop {
        info!("Sample the libraries");

        let inverse_map = InverseMap::new(l, &frags);

        info!("Creating traces");
        let traces: Vec<&Fragment<T>> = frags.find_valid_traces(&tests);

        info!("Printing traces of up to size {}", frags.get_size());
        traces.iter().for_each(|t| info!("trace = {t}"));

        let complete_traces: Vec<_> = traces
            .iter()
            .filter(|Fragment { fragment, .. }| {
                tests.is_consistent_with(|t| {
                    fragment
                        .interpret(&t.into())
                        .map_or(false, |output| output == t.output)
                })
            })
            .collect();
        if !complete_traces.is_empty() {
            info!("Found a complete trace");
            return Some(
                dbg!(complete_traces.first().unwrap())
                    .fragment
                    .clone()
                    .into(),
            );
        }

        // Synthesize candidates topdown propagation (with holes?)
        // work top down, trying to follow the traces?
        if let Some(p) = top_down_prop(tests.clone(), traces, &inverse_map, &type_map, &frags, &sig)
        {
            return Some(p);
        } else {
            frags.increment(l, &tests.get_all_examples());
            if frags.get_size() > MAX_FRAG_SIZE {
                eprintln!("We failed to synthesize anything in a bound of size {MAX_FRAG_SIZE}");
                return None;
            }
        }
    }
}
