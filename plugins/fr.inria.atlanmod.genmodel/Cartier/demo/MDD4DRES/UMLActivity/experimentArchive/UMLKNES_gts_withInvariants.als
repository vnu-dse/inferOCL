module umlknes

open util/Boolean as Bool

enum VisibilityKind { Private,public,protected,package }

 
 sig Activity  
{ 
	node : set ActivityNode,
	edge : set ActivityEdge,
	isReadOnly : one Bool,
	isSingleExecution : one Bool
}

abstract sig ActivityNode extends RedefinableElement 
{ 
	activity : lone Activity,
	incoming : set ActivityEdge,
	outgoing : set ActivityEdge,
	redefinedElement : set ActivityNode
}

abstract sig ControlNode extends ActivityNode 
{
}

 sig ActivityFinalNode extends ControlNode 
{
}

 sig InitialNode extends ControlNode 
{
}

abstract sig ActivityEdge extends RedefinableElement 
{ 
	target : one ActivityNode,
	source : one ActivityNode,
	activity : lone Activity,
	weight : one ValueSpecification,
	guard : one ValueSpecification
}

 sig ControlFlow extends ActivityEdge 
{
}

 sig DecisionNode extends ControlNode 
{
}

abstract sig Action extends ActivityNode 
{
}

 sig AcceptEventAction extends Action 
{ 
	isUnMarshall : lone Bool,
	trigger : some Trigger
}

abstract sig ValueSpecification extends NamedElement 
{
}

abstract sig NamedElement  
{ 
	visibility : one VisibilityKind
}

abstract sig RedefinableElement extends NamedElement 
{ 
	isLeaf : one Bool
}

 sig Trigger extends NamedElement 
{ 
	event : one Event
}

abstract sig Event  
{
}

 sig ExecutionEvent extends Event 
{
}

 sig CreationEvent extends Event 
{
}

 sig DestructionEvent extends Event 
{
}


fact ActivityNode_containers
{
	(all  o : ActivityNode |o in Activity.node)
}


fact ActivityEdge_containers
{
	(all  o : ActivityEdge |o in Activity.edge)
}


fact ValueSpecification_containers
{
	(all  o : ValueSpecification |o in ActivityEdge.weight or o in ControlFlow.weight or o in ActivityEdge.guard or o in ControlFlow.guard) and (all  o1 : ActivityEdge.weight, o2 : ControlFlow.weight, o3 : ActivityEdge.guard, o4 : ControlFlow.guard |disj [o1,o2,o3,o4])
}


fact Activity_node_composite
{
	all  o1 : Activity, o2 : Activity |all  p1 : o1.node, p2 : o2.node |p1 = p2 implies o1 = o2
}


fact Activity_node_ActivityNode_activity_opposite
{
	all  o1 : Activity, o2 : ActivityNode |o2 in o1.node implies o1 in o2.activity
}


fact Activity_edge_composite
{
	all  o1 : Activity, o2 : Activity |all  p1 : o1.edge, p2 : o2.edge |p1 = p2 implies o1 = o2
}


fact Activity_edge_ActivityEdge_activity_opposite
{
	all  o1 : Activity, o2 : ActivityEdge |o2 in o1.edge implies o1 in o2.activity
}


fact Activity_isReadOnly_composite
{
	all  o1 : Activity, o2 : Activity |all  p1 : o1.isReadOnly, p2 : o2.isReadOnly |p1 = p2 implies o1 = o2
}


fact Activity_isSingleExecution_composite
{
	all  o1 : Activity, o2 : Activity |all  p1 : o1.isSingleExecution, p2 : o2.isSingleExecution |p1 = p2 implies o1 = o2
}


fact ActivityNode_incoming_ActivityEdge_target_opposite
{
	all  o1 : ActivityNode, o2 : ActivityEdge |o2 in o1.incoming implies o1 in o2.target
}


fact ActivityNode_outgoing_ActivityEdge_source_opposite
{
	all  o1 : ActivityNode, o2 : ActivityEdge |o2 in o1.outgoing implies o1 in o2.source
}


fact ActivityEdge_weight_composite
{
	all  o1 : ActivityEdge, o2 : ActivityEdge |all  p1 : o1.weight, p2 : o2.weight |p1 = p2 implies o1 = o2
}


fact ActivityEdge_guard_composite
{
	all  o1 : ActivityEdge, o2 : ActivityEdge |all  p1 : o1.guard, p2 : o2.guard |p1 = p2 implies o1 = o2
}


fact AcceptEventAction_isUnMarshall_composite
{
	all  o1 : AcceptEventAction, o2 : AcceptEventAction |all  p1 : o1.isUnMarshall, p2 : o2.isUnMarshall |p1 = p2 implies o1 = o2
}


fact RedefinableElement_isLeaf_composite
{
	all  o1 : RedefinableElement, o2 : RedefinableElement |all  p1 : o1.isLeaf, p2 : o2.isLeaf |p1 = p2 implies o1 = o2
}
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

pred Activity_node_partition1

{
	some  o : Activity |#o.node = 0
}

pred Activity_node_partition2

{
	some  o : Activity |#o.node = 1
}

pred Activity_node_partition3

{
	some  o : Activity |#o.node >= 5
}

pred Activity_edge_partition1

{
	some  o : Activity |#o.edge = 0
}

pred Activity_edge_partition2

{
	some  o : Activity |#o.edge = 1
}

pred Activity_edge_partition3

{
	some  o : Activity |#o.edge >= 5
}

pred Activity_isReadOnly_partition1

{
	some  o : Activity |#o.isReadOnly = 0
}

pred Activity_isReadOnly_partition2

{
	some  o : Activity |#o.isReadOnly = 1
}

pred Activity_isReadOnly_partition3

{
	some  o : Activity |#o.isReadOnly >= 5
}

pred Activity_isSingleExecution_partition1

{
	some  o : Activity |#o.isSingleExecution = 0
}

pred Activity_isSingleExecution_partition2

{
	some  o : Activity |#o.isSingleExecution = 1
}

pred Activity_isSingleExecution_partition3

{
	some  o : Activity |#o.isSingleExecution >= 5
}

pred ActivityNode_activity_partition1

{
	some  o : ActivityNode |#o.activity = 0
}

pred ActivityNode_activity_partition2

{
	some  o : ActivityNode |#o.activity = 1
}

pred ActivityNode_activity_partition3

{
	some  o : ActivityNode |#o.activity >= 5
}

pred ActivityNode_incoming_partition1

{
	some  o : ActivityNode |#o.incoming = 0
}

pred ActivityNode_incoming_partition2

{
	some  o : ActivityNode |#o.incoming = 1
}

pred ActivityNode_incoming_partition3

{
	some  o : ActivityNode |#o.incoming >= 5
}

pred ActivityNode_outgoing_partition1

{
	some  o : ActivityNode |#o.outgoing = 0
}

pred ActivityNode_outgoing_partition2

{
	some  o : ActivityNode |#o.outgoing = 1
}

pred ActivityNode_outgoing_partition3

{
	some  o : ActivityNode |#o.outgoing >= 5
}

pred ActivityNode_redefinedElement_partition1

{
	some  o : ActivityNode |#o.redefinedElement = 0
}

pred ActivityNode_redefinedElement_partition2

{
	some  o : ActivityNode |#o.redefinedElement = 1
}

pred ActivityNode_redefinedElement_partition3

{
	some  o : ActivityNode |#o.redefinedElement >= 5
}

pred ActivityEdge_target_partition1

{
	some  o : ActivityEdge |#o.target = 0
}

pred ActivityEdge_target_partition2

{
	some  o : ActivityEdge |#o.target = 1
}

pred ActivityEdge_target_partition3

{
	some  o : ActivityEdge |#o.target >= 5
}

pred ActivityEdge_source_partition1

{
	some  o : ActivityEdge |#o.source = 0
}

pred ActivityEdge_source_partition2

{
	some  o : ActivityEdge |#o.source = 1
}

pred ActivityEdge_source_partition3

{
	some  o : ActivityEdge |#o.source >= 5
}

pred ActivityEdge_activity_partition1

{
	some  o : ActivityEdge |#o.activity = 0
}

pred ActivityEdge_activity_partition2

{
	some  o : ActivityEdge |#o.activity = 1
}

pred ActivityEdge_activity_partition3

{
	some  o : ActivityEdge |#o.activity >= 5
}

pred ActivityEdge_weight_partition1

{
	some  o : ActivityEdge |#o.weight = 0
}

pred ActivityEdge_weight_partition2

{
	some  o : ActivityEdge |#o.weight = 1
}

pred ActivityEdge_weight_partition3

{
	some  o : ActivityEdge |#o.weight >= 5
}

pred ActivityEdge_guard_partition1

{
	some  o : ActivityEdge |#o.guard = 0
}

pred ActivityEdge_guard_partition2

{
	some  o : ActivityEdge |#o.guard = 1
}

pred ActivityEdge_guard_partition3

{
	some  o : ActivityEdge |#o.guard >= 5
}

pred AcceptEventAction_isUnMarshall_partition1

{
	some  o : AcceptEventAction |#o.isUnMarshall = 0
}

pred AcceptEventAction_isUnMarshall_partition2

{
	some  o : AcceptEventAction |#o.isUnMarshall = 1
}

pred AcceptEventAction_isUnMarshall_partition3

{
	some  o : AcceptEventAction |#o.isUnMarshall >= 5
}

pred AcceptEventAction_trigger_partition1

{
	some  o : AcceptEventAction |#o.trigger = 0
}

pred AcceptEventAction_trigger_partition2

{
	some  o : AcceptEventAction |#o.trigger = 1
}

pred AcceptEventAction_trigger_partition3

{
	some  o : AcceptEventAction |#o.trigger >= 5
}

pred NamedElement_visibility_partition1

{
	some  o : NamedElement |o.visibility = Private
}

pred NamedElement_visibility_partition2

{
	some  o : NamedElement |o.visibility = public
}

pred NamedElement_visibility_partition3

{
	some  o : NamedElement |o.visibility = protected
}

pred NamedElement_visibility_partition4

{
	some  o : NamedElement |o.visibility = package
}

pred RedefinableElement_isLeaf_partition1

{
	some  o : RedefinableElement |#o.isLeaf = 0
}

pred RedefinableElement_isLeaf_partition2

{
	some  o : RedefinableElement |#o.isLeaf = 1
}

pred RedefinableElement_isLeaf_partition3

{
	some  o : RedefinableElement |#o.isLeaf >= 5
}

pred Trigger_event_partition1

{
	some  o : Trigger |#o.event = 0
}

pred Trigger_event_partition2

{
	some  o : Trigger |#o.event = 1
}

pred Trigger_event_partition3

{
	some  o : Trigger |#o.event >= 5
}

pred mfAllRanges_Activity_node_partition1

{
	Activity_node_partition1
}

pred mfAllRanges_Activity_node_partition2

{
	Activity_node_partition2
}

pred mfAllRanges_Activity_node_partition3

{
	Activity_node_partition3
}

pred mfAllRanges_Activity_edge_partition1

{
	Activity_edge_partition1
}

pred mfAllRanges_Activity_edge_partition2

{
	Activity_edge_partition2
}

pred mfAllRanges_Activity_edge_partition3

{
	Activity_edge_partition3
}

pred mfAllRanges_Activity_isReadOnly_partition1

{
	Activity_isReadOnly_partition1
}

pred mfAllRanges_Activity_isReadOnly_partition2

{
	Activity_isReadOnly_partition2
}

pred mfAllRanges_Activity_isReadOnly_partition3

{
	Activity_isReadOnly_partition3
}

pred mfAllRanges_Activity_isSingleExecution_partition1

{
	Activity_isSingleExecution_partition1
}

pred mfAllRanges_Activity_isSingleExecution_partition2

{
	Activity_isSingleExecution_partition2
}

pred mfAllRanges_Activity_isSingleExecution_partition3

{
	Activity_isSingleExecution_partition3
}

pred mfAllRanges_ActivityNode_activity_partition1

{
	ActivityNode_activity_partition1
}

pred mfAllRanges_ActivityNode_activity_partition2

{
	ActivityNode_activity_partition2
}

pred mfAllRanges_ActivityNode_activity_partition3

{
	ActivityNode_activity_partition3
}

pred mfAllRanges_ActivityNode_incoming_partition1

{
	ActivityNode_incoming_partition1
}

pred mfAllRanges_ActivityNode_incoming_partition2

{
	ActivityNode_incoming_partition2
}

pred mfAllRanges_ActivityNode_incoming_partition3

{
	ActivityNode_incoming_partition3
}

pred mfAllRanges_ActivityNode_outgoing_partition1

{
	ActivityNode_outgoing_partition1
}

pred mfAllRanges_ActivityNode_outgoing_partition2

{
	ActivityNode_outgoing_partition2
}

pred mfAllRanges_ActivityNode_outgoing_partition3

{
	ActivityNode_outgoing_partition3
}

pred mfAllRanges_ActivityNode_redefinedElement_partition1

{
	ActivityNode_redefinedElement_partition1
}

pred mfAllRanges_ActivityNode_redefinedElement_partition2

{
	ActivityNode_redefinedElement_partition2
}

pred mfAllRanges_ActivityNode_redefinedElement_partition3

{
	ActivityNode_redefinedElement_partition3
}

pred mfAllRanges_ActivityEdge_target_partition1

{
	ActivityEdge_target_partition1
}

pred mfAllRanges_ActivityEdge_target_partition2

{
	ActivityEdge_target_partition2
}

pred mfAllRanges_ActivityEdge_target_partition3

{
	ActivityEdge_target_partition3
}

pred mfAllRanges_ActivityEdge_source_partition1

{
	ActivityEdge_source_partition1
}

pred mfAllRanges_ActivityEdge_source_partition2

{
	ActivityEdge_source_partition2
}

pred mfAllRanges_ActivityEdge_source_partition3

{
	ActivityEdge_source_partition3
}

pred mfAllRanges_ActivityEdge_activity_partition1

{
	ActivityEdge_activity_partition1
}

pred mfAllRanges_ActivityEdge_activity_partition2

{
	ActivityEdge_activity_partition2
}

pred mfAllRanges_ActivityEdge_activity_partition3

{
	ActivityEdge_activity_partition3
}

pred mfAllRanges_ActivityEdge_weight_partition1

{
	ActivityEdge_weight_partition1
}

pred mfAllRanges_ActivityEdge_weight_partition2

{
	ActivityEdge_weight_partition2
}

pred mfAllRanges_ActivityEdge_weight_partition3

{
	ActivityEdge_weight_partition3
}

pred mfAllRanges_ActivityEdge_guard_partition1

{
	ActivityEdge_guard_partition1
}

pred mfAllRanges_ActivityEdge_guard_partition2

{
	ActivityEdge_guard_partition2
}

pred mfAllRanges_ActivityEdge_guard_partition3

{
	ActivityEdge_guard_partition3
}

pred mfAllRanges_AcceptEventAction_isUnMarshall_partition1

{
	AcceptEventAction_isUnMarshall_partition1
}

pred mfAllRanges_AcceptEventAction_isUnMarshall_partition2

{
	AcceptEventAction_isUnMarshall_partition2
}

pred mfAllRanges_AcceptEventAction_isUnMarshall_partition3

{
	AcceptEventAction_isUnMarshall_partition3
}

pred mfAllRanges_AcceptEventAction_trigger_partition1

{
	AcceptEventAction_trigger_partition1
}

pred mfAllRanges_AcceptEventAction_trigger_partition2

{
	AcceptEventAction_trigger_partition2
}

pred mfAllRanges_AcceptEventAction_trigger_partition3

{
	AcceptEventAction_trigger_partition3
}

pred mfAllRanges_NamedElement_visibility_partition4

{
	NamedElement_visibility_partition4
}

pred mfAllRanges_RedefinableElement_isLeaf_partition1

{
	RedefinableElement_isLeaf_partition1
}

pred mfAllRanges_RedefinableElement_isLeaf_partition2

{
	RedefinableElement_isLeaf_partition2
}

pred mfAllRanges_RedefinableElement_isLeaf_partition3

{
	RedefinableElement_isLeaf_partition3
}

pred mfAllRanges_Trigger_event_partition1

{
	Trigger_event_partition1
}

pred mfAllRanges_Trigger_event_partition2

{
	Trigger_event_partition2
}

pred mfAllRanges_Trigger_event_partition3

{
	Trigger_event_partition3
}

pred mfAllPartitions_Activity_node_partition1_Activity_node_partition2_Activity_node_partition3

{
	Activity_node_partition1 and Activity_node_partition2 and Activity_node_partition3 
}

pred mfAllPartitions_Activity_edge_partition1_Activity_edge_partition2_Activity_edge_partition3

{
	Activity_edge_partition1 and Activity_edge_partition2 and Activity_edge_partition3 
}

pred mfAllPartitions_Activity_isReadOnly_partition1_Activity_isReadOnly_partition2_Activity_isReadOnly_partition3

{
	Activity_isReadOnly_partition1 and Activity_isReadOnly_partition2 and Activity_isReadOnly_partition3 
}

pred mfAllPartitions_Activity_isSingleExecution_partition1_Activity_isSingleExecution_partition2_Activity_isSingleExecution_partition3

{
	Activity_isSingleExecution_partition1 and Activity_isSingleExecution_partition2 and Activity_isSingleExecution_partition3 
}

pred mfAllPartitions_ActivityNode_activity_partition1_ActivityNode_activity_partition2_ActivityNode_activity_partition3

{
	ActivityNode_activity_partition1 and ActivityNode_activity_partition2 and ActivityNode_activity_partition3 
}

pred mfAllPartitions_ActivityNode_incoming_partition1_ActivityNode_incoming_partition2_ActivityNode_incoming_partition3

{
	ActivityNode_incoming_partition1 and ActivityNode_incoming_partition2 and ActivityNode_incoming_partition3 
}

pred mfAllPartitions_ActivityNode_outgoing_partition1_ActivityNode_outgoing_partition2_ActivityNode_outgoing_partition3

{
	ActivityNode_outgoing_partition1 and ActivityNode_outgoing_partition2 and ActivityNode_outgoing_partition3 
}

pred mfAllPartitions_ActivityNode_redefinedElement_partition1_ActivityNode_redefinedElement_partition2_ActivityNode_redefinedElement_partition3

{
	ActivityNode_redefinedElement_partition1 and ActivityNode_redefinedElement_partition2 and ActivityNode_redefinedElement_partition3 
}

pred mfAllPartitions_ActivityEdge_target_partition1_ActivityEdge_target_partition2_ActivityEdge_target_partition3

{
	ActivityEdge_target_partition1 and ActivityEdge_target_partition2 and ActivityEdge_target_partition3 
}

pred mfAllPartitions_ActivityEdge_source_partition1_ActivityEdge_source_partition2_ActivityEdge_source_partition3

{
	ActivityEdge_source_partition1 and ActivityEdge_source_partition2 and ActivityEdge_source_partition3 
}

pred mfAllPartitions_ActivityEdge_activity_partition1_ActivityEdge_activity_partition2_ActivityEdge_activity_partition3

{
	ActivityEdge_activity_partition1 and ActivityEdge_activity_partition2 and ActivityEdge_activity_partition3 
}

pred mfAllPartitions_ActivityEdge_weight_partition1_ActivityEdge_weight_partition2_ActivityEdge_weight_partition3

{
	ActivityEdge_weight_partition1 and ActivityEdge_weight_partition2 and ActivityEdge_weight_partition3 
}

pred mfAllPartitions_ActivityEdge_guard_partition1_ActivityEdge_guard_partition2_ActivityEdge_guard_partition3

{
	ActivityEdge_guard_partition1 and ActivityEdge_guard_partition2 and ActivityEdge_guard_partition3 
}

pred mfAllPartitions_AcceptEventAction_isUnMarshall_partition1_AcceptEventAction_isUnMarshall_partition2_AcceptEventAction_isUnMarshall_partition3

{
	AcceptEventAction_isUnMarshall_partition1 and AcceptEventAction_isUnMarshall_partition2 and AcceptEventAction_isUnMarshall_partition3 
}

pred mfAllPartitions_AcceptEventAction_trigger_partition1_AcceptEventAction_trigger_partition2_AcceptEventAction_trigger_partition3

{
	AcceptEventAction_trigger_partition1 and AcceptEventAction_trigger_partition2 and AcceptEventAction_trigger_partition3 
}

pred mfAllPartitions_NamedElement_visibility_partition4

{
	NamedElement_visibility_partition4 
}

pred mfAllPartitions_RedefinableElement_isLeaf_partition1_RedefinableElement_isLeaf_partition2_RedefinableElement_isLeaf_partition3

{
	RedefinableElement_isLeaf_partition1 and RedefinableElement_isLeaf_partition2 and RedefinableElement_isLeaf_partition3 
}

pred mfAllPartitions_Trigger_event_partition1_Trigger_event_partition2_Trigger_event_partition3

{
	Trigger_event_partition1 and Trigger_event_partition2 and Trigger_event_partition3 
}

pred GenerateAndTestSimple

{
#Activity=1
}

run GenerateAndTestSimple  for 20
