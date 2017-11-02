//Meta-model constraints

//All source and target of an edge must be in the same activity as the edge

fact source_target_same_activity
{
all edge: ActivityEdge | edge.source.activity = edge.activity and edge.target.activity = edge.activity

}

//Activity edges may be owned only by activities or groups

fact edge_owners

{
all e: ActivityEdge | e in Activity.edge
}

//Activity edges may be owned by at most one structured node

//Activity nodes can be owned only by activities or groups

fact node_owners

{
all n: ActivityNode | n in Activity.node
}
