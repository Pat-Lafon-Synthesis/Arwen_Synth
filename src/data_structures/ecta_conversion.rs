use ecta_rs::{ECTANode, Node, ECTA};
use log::{info, warn};

use crate::{
    language::{LinearProgram, LinearProgramNode, TypeSystemBounds},
    transpose, SynthEctaEdge,
};

pub fn create_ecta_from_traces<T: TypeSystemBounds>(
    ecta: &mut ECTA<SynthEctaEdge<T>, ()>,
    frags: &mut [&LinearProgram<T>],
) -> ECTANode {
    info!("Starting ECTA creation from traces...");

    if frags.is_empty() {
        warn!("create_ecta_from_traces called with empty fragment list")
    }

    frags.iter().for_each(|p| {
        info!("program in fragments = {}", p);
    });

    frags.sort_by_key(|a| a.node.clone());

    frags.iter().for_each(|p| {
        info!("sorted fragments = {}", p);
    });

    let edge_builder = frags
        .group_by(|p1, p2| p1.node == p2.node)
        .map(|g| {
            info!("Group: {:?}", g);
            let prog_edge = SynthEctaEdge::P(g[0].node.clone());
            let ty_edge = SynthEctaEdge::T(g[0].get_type());

            let type_node =
                ecta.add_node(Node::new(), vec![(ty_edge, None, vec![ecta.empty_node])]);

            let mut node_collector = vec![type_node];
            if let LinearProgramNode::Operation(_) = g[0].node {
                let x = g
                    .iter()
                    .map(|LinearProgram { node, args }| match node {
                        LinearProgramNode::Constant(..) | LinearProgramNode::Variable(..) => {
                            unreachable!()
                        }
                        LinearProgramNode::Operation(_) => args.clone(),
                    })
                    .collect::<Vec<_>>();
                let traces = transpose(x);
                let traces = traces
                    .iter()
                    .map(|a| a.iter().collect::<Vec<_>>())
                    .collect::<Vec<_>>();
                traces.into_iter().for_each(|mut trace| {
                    let inner_node = create_ecta_from_traces(ecta, &mut trace);
                    node_collector.push(inner_node);
                });
            }

            (prog_edge, None, node_collector)
        })
        .collect();

    info!("Edges to add: {edge_builder:?}");

    let program_node = ecta.add_node(Node::new(), edge_builder);

    info!("Done with ECTA creation from traces...");

    program_node
}
