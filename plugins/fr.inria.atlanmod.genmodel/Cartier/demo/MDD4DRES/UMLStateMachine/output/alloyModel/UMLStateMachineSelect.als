module umlstatemachineselect

open util/Boolean as Bool

enum TransitionKind { internal,local,external }

 enum PseudostateKind { initial,deepHistory,shallowHistory,join,fork,junction,choice,entryPoint,exitPoint,terminate }

  sig StateMachine extends Behavior 
{ 
	region : some Region,
	submachineState : set State,
	connectionPoint : set PseudoState
}
 sig Region  
{ 
	stateMachine : lone StateMachine,
	subvertex : set Vertex,
	transition : set Transition,
	state : lone State
}
 sig Vertex  
{ 
	container : lone Region,
	outgoing : set Transition,
	incoming : set Transition
}
 sig Transition  
{ 
	container : one Region,
	kind : lone TransitionKind,
	target : one Vertex,
	source : one Vertex,
	effect : lone Behavior,
	guard : lone Constraint,
	trigger : set Trigger
}
 sig State extends Vertex 
{ 
	isComposite : lone Bool,
	isOrthogonal : lone Bool,
	isSimple : lone Bool,
	isSubmachineState : lone Bool,
	region : set Region,
	connection : set ConnectionPointReference,
	submachine : lone StateMachine,
	entry : lone Behavior,
	exit : lone Behavior,
	doActivity : lone Behavior,
	stateInvariant : lone Constraint,
	deferrableTrigger : set Trigger
}
 sig FinalState extends State 
{
}
 sig PseudoState extends Vertex 
{ 
	kind : lone PseudostateKind,
	stateMachine : lone StateMachine
}
 sig ConnectionPointReference extends Vertex 
{ 
	state : lone State,
	entry : set PseudoState,
	exit : set PseudoState
}
 sig Behavior  
{
}
 sig Constraint  
{
}
 sig Trigger  
{
}

fact Region_containers
{
	(all  o : Region |o in StateMachine.region or o in State.region or o in FinalState.region) and (all  o1 : StateMachine.region, o2 : State.region, o3 : FinalState.region |disj [o1,o2,o3])
}

fact Vertex_containers
{
	(all  o : Vertex |o in Region.subvertex)
}

fact Transition_containers
{
	(all  o : Transition |o in Region.transition)
}

fact PseudoState_containers
{
	(all  o : PseudoState |o in StateMachine.connectionPoint)
}

fact ConnectionPointReference_containers
{
	(all  o : ConnectionPointReference |o in State.connection or o in FinalState.connection) and (all  o1 : State.connection, o2 : FinalState.connection |disj [o1,o2])
}

fact Behavior_containers
{
	(all  o : Behavior |o in Transition.effect or o in State.entry or o in FinalState.entry or o in State.exit or o in FinalState.exit or o in State.doActivity or o in FinalState.doActivity) and (all  o1 : Transition.effect, o2 : State.entry, o3 : FinalState.entry, o4 : State.exit, o5 : FinalState.exit, o6 : State.doActivity, o7 : FinalState.doActivity |disj [o1,o2,o3,o4,o5,o6,o7])
}

fact Constraint_containers
{
	(all  o : Constraint |o in Transition.guard or o in State.stateInvariant or o in FinalState.stateInvariant) and (all  o1 : Transition.guard, o2 : State.stateInvariant, o3 : FinalState.stateInvariant |disj [o1,o2,o3])
}

fact Trigger_containers
{
	(all  o : Trigger |o in Transition.trigger or o in State.deferrableTrigger or o in FinalState.deferrableTrigger) and (all  o1 : Transition.trigger, o2 : State.deferrableTrigger, o3 : FinalState.deferrableTrigger |disj [o1,o2,o3])
}

fact StateMachine_region_composite
{
	all  o1 : StateMachine, o2 : StateMachine |all  p1 : o1.region, p2 : o2.region |p1 = p2 implies o1 = o2
}

fact StateMachine_region_Region_stateMachine_opposite
{
	all  o1 : StateMachine, o2 : Region |o2 in o1.region implies o1 in o2.stateMachine
}

fact StateMachine_submachineState_State_submachine_opposite
{
	all  o1 : StateMachine, o2 : State |o2 in o1.submachineState implies o1 in o2.submachine
}

fact StateMachine_connectionPoint_composite
{
	all  o1 : StateMachine, o2 : StateMachine |all  p1 : o1.connectionPoint, p2 : o2.connectionPoint |p1 = p2 implies o1 = o2
}

fact Region_subvertex_composite
{
	all  o1 : Region, o2 : Region |all  p1 : o1.subvertex, p2 : o2.subvertex |p1 = p2 implies o1 = o2
}

fact Region_subvertex_Vertex_container_opposite
{
	all  o1 : Region, o2 : Vertex |o2 in o1.subvertex implies o1 in o2.container
}

fact Region_transition_composite
{
	all  o1 : Region, o2 : Region |all  p1 : o1.transition, p2 : o2.transition |p1 = p2 implies o1 = o2
}

fact Region_transition_Transition_container_opposite
{
	all  o1 : Region, o2 : Transition |o2 in o1.transition implies o1 in o2.container
}

fact Region_state_State_region_opposite
{
	all  o1 : Region, o2 : State |o2 in o1.state implies o1 in o2.region
}

fact Vertex_outgoing_Transition_source_opposite
{
	all  o1 : Vertex, o2 : Transition |o2 in o1.outgoing implies o1 in o2.source
}

fact Vertex_incoming_Transition_target_opposite
{
	all  o1 : Vertex, o2 : Transition |o2 in o1.incoming implies o1 in o2.target
}

fact Transition_effect_composite
{
	all  o1 : Transition, o2 : Transition |all  p1 : o1.effect, p2 : o2.effect |p1 = p2 implies o1 = o2
}

fact Transition_guard_composite
{
	all  o1 : Transition, o2 : Transition |all  p1 : o1.guard, p2 : o2.guard |p1 = p2 implies o1 = o2
}

fact Transition_trigger_composite
{
	all  o1 : Transition, o2 : Transition |all  p1 : o1.trigger, p2 : o2.trigger |p1 = p2 implies o1 = o2
}

fact State_region_composite
{
	all  o1 : State, o2 : State |all  p1 : o1.region, p2 : o2.region |p1 = p2 implies o1 = o2
}

fact State_connection_composite
{
	all  o1 : State, o2 : State |all  p1 : o1.connection, p2 : o2.connection |p1 = p2 implies o1 = o2
}

fact State_connection_ConnectionPointReference_state_opposite
{
	all  o1 : State, o2 : ConnectionPointReference |o2 in o1.connection implies o1 in o2.state
}

fact State_entry_composite
{
	all  o1 : State, o2 : State |all  p1 : o1.entry, p2 : o2.entry |p1 = p2 implies o1 = o2
}

fact State_exit_composite
{
	all  o1 : State, o2 : State |all  p1 : o1.exit, p2 : o2.exit |p1 = p2 implies o1 = o2
}

fact State_doActivity_composite
{
	all  o1 : State, o2 : State |all  p1 : o1.doActivity, p2 : o2.doActivity |p1 = p2 implies o1 = o2
}

fact State_stateInvariant_composite
{
	all  o1 : State, o2 : State |all  p1 : o1.stateInvariant, p2 : o2.stateInvariant |p1 = p2 implies o1 = o2
}

fact State_deferrableTrigger_composite
{
	all  o1 : State, o2 : State |all  p1 : o1.deferrableTrigger, p2 : o2.deferrableTrigger |p1 = p2 implies o1 = o2
}

fact PseudoState_stateMachine_StateMachine_connectionPoint_opposite
{
	all  o1 : PseudoState, o2 : StateMachine |o2 in o1.stateMachine implies o1 in o2.connectionPoint
}
pred StateMachine_region_partition1

{
	some  o : StateMachine |#o.region = 0
}
pred StateMachine_region_partition2

{
	some  o : StateMachine |#o.region = 1
}
pred StateMachine_region_partition3

{
	some  o : StateMachine |#o.region >= 5
}
pred StateMachine_submachineState_partition1

{
	some  o : StateMachine |#o.submachineState = 0
}
pred StateMachine_submachineState_partition2

{
	some  o : StateMachine |#o.submachineState = 1
}
pred StateMachine_submachineState_partition3

{
	some  o : StateMachine |#o.submachineState >= 5
}
pred StateMachine_connectionPoint_partition1

{
	some  o : StateMachine |#o.connectionPoint = 0
}
pred StateMachine_connectionPoint_partition2

{
	some  o : StateMachine |#o.connectionPoint = 1
}
pred StateMachine_connectionPoint_partition3

{
	some  o : StateMachine |#o.connectionPoint >= 5
}
pred Region_stateMachine_partition1

{
	some  o : Region |#o.stateMachine = 0
}
pred Region_stateMachine_partition2

{
	some  o : Region |#o.stateMachine = 1
}
pred Region_stateMachine_partition3

{
	some  o : Region |#o.stateMachine >= 5
}
pred Region_subvertex_partition1

{
	some  o : Region |#o.subvertex = 0
}
pred Region_subvertex_partition2

{
	some  o : Region |#o.subvertex = 1
}
pred Region_subvertex_partition3

{
	some  o : Region |#o.subvertex >= 5
}
pred Region_transition_partition1

{
	some  o : Region |#o.transition = 0
}
pred Region_transition_partition2

{
	some  o : Region |#o.transition = 1
}
pred Region_transition_partition3

{
	some  o : Region |#o.transition >= 5
}
pred Region_state_partition1

{
	some  o : Region |#o.state = 0
}
pred Region_state_partition2

{
	some  o : Region |#o.state = 1
}
pred Region_state_partition3

{
	some  o : Region |#o.state >= 5
}
pred Vertex_container_partition1

{
	some  o : Vertex |#o.container = 0
}
pred Vertex_container_partition2

{
	some  o : Vertex |#o.container = 1
}
pred Vertex_container_partition3

{
	some  o : Vertex |#o.container >= 5
}
pred Vertex_outgoing_partition1

{
	some  o : Vertex |#o.outgoing = 0
}
pred Vertex_outgoing_partition2

{
	some  o : Vertex |#o.outgoing = 1
}
pred Vertex_outgoing_partition3

{
	some  o : Vertex |#o.outgoing >= 5
}
pred Vertex_incoming_partition1

{
	some  o : Vertex |#o.incoming = 0
}
pred Vertex_incoming_partition2

{
	some  o : Vertex |#o.incoming = 1
}
pred Vertex_incoming_partition3

{
	some  o : Vertex |#o.incoming >= 5
}
pred Transition_container_partition1

{
	some  o : Transition |#o.container = 0
}
pred Transition_container_partition2

{
	some  o : Transition |#o.container = 1
}
pred Transition_container_partition3

{
	some  o : Transition |#o.container >= 5
}
pred Transition_kind_partition1

{
	some  o : Transition |o.kind = internal
}
pred Transition_kind_partition2

{
	some  o : Transition |o.kind = local
}
pred Transition_kind_partition3

{
	some  o : Transition |o.kind = external
}
pred Transition_target_partition1

{
	some  o : Transition |#o.target = 0
}
pred Transition_target_partition2

{
	some  o : Transition |#o.target = 1
}
pred Transition_target_partition3

{
	some  o : Transition |#o.target >= 5
}
pred Transition_source_partition1

{
	some  o : Transition |#o.source = 0
}
pred Transition_source_partition2

{
	some  o : Transition |#o.source = 1
}
pred Transition_source_partition3

{
	some  o : Transition |#o.source >= 5
}
pred Transition_effect_partition1

{
	some  o : Transition |#o.effect = 0
}
pred Transition_effect_partition2

{
	some  o : Transition |#o.effect = 1
}
pred Transition_effect_partition3

{
	some  o : Transition |#o.effect >= 5
}
pred Transition_guard_partition1

{
	some  o : Transition |#o.guard = 0
}
pred Transition_guard_partition2

{
	some  o : Transition |#o.guard = 1
}
pred Transition_guard_partition3

{
	some  o : Transition |#o.guard >= 5
}
pred Transition_trigger_partition1

{
	some  o : Transition |#o.trigger = 0
}
pred Transition_trigger_partition2

{
	some  o : Transition |#o.trigger = 1
}
pred Transition_trigger_partition3

{
	some  o : Transition |#o.trigger >= 5
}
pred State_isComposite_partition1

{
	some  o : State |o.isComposite = True
}
pred State_isComposite_partition2

{
	some  o : State |o.isComposite = False
}
pred State_isOrthogonal_partition1

{
	some  o : State |o.isOrthogonal = True
}
pred State_isOrthogonal_partition2

{
	some  o : State |o.isOrthogonal = False
}
pred State_isSimple_partition1

{
	some  o : State |o.isSimple = True
}
pred State_isSimple_partition2

{
	some  o : State |o.isSimple = False
}
pred State_isSubmachineState_partition1

{
	some  o : State |o.isSubmachineState = True
}
pred State_isSubmachineState_partition2

{
	some  o : State |o.isSubmachineState = False
}
pred State_region_partition1

{
	some  o : State |#o.region = 0
}
pred State_region_partition2

{
	some  o : State |#o.region = 1
}
pred State_region_partition3

{
	some  o : State |#o.region >= 5
}
pred State_connection_partition1

{
	some  o : State |#o.connection = 0
}
pred State_connection_partition2

{
	some  o : State |#o.connection = 1
}
pred State_connection_partition3

{
	some  o : State |#o.connection >= 5
}
pred State_submachine_partition1

{
	some  o : State |#o.submachine = 0
}
pred State_submachine_partition2

{
	some  o : State |#o.submachine = 1
}
pred State_submachine_partition3

{
	some  o : State |#o.submachine >= 5
}
pred State_entry_partition1

{
	some  o : State |#o.entry = 0
}
pred State_entry_partition2

{
	some  o : State |#o.entry = 1
}
pred State_entry_partition3

{
	some  o : State |#o.entry >= 5
}
pred State_exit_partition1

{
	some  o : State |#o.exit = 0
}
pred State_exit_partition2

{
	some  o : State |#o.exit = 1
}
pred State_exit_partition3

{
	some  o : State |#o.exit >= 5
}
pred State_doActivity_partition1

{
	some  o : State |#o.doActivity = 0
}
pred State_doActivity_partition2

{
	some  o : State |#o.doActivity = 1
}
pred State_doActivity_partition3

{
	some  o : State |#o.doActivity >= 5
}
pred State_stateInvariant_partition1

{
	some  o : State |#o.stateInvariant = 0
}
pred State_stateInvariant_partition2

{
	some  o : State |#o.stateInvariant = 1
}
pred State_stateInvariant_partition3

{
	some  o : State |#o.stateInvariant >= 5
}
pred State_deferrableTrigger_partition1

{
	some  o : State |#o.deferrableTrigger = 0
}
pred State_deferrableTrigger_partition2

{
	some  o : State |#o.deferrableTrigger = 1
}
pred State_deferrableTrigger_partition3

{
	some  o : State |#o.deferrableTrigger >= 5
}
pred PseudoState_kind_partition1

{
	some  o : PseudoState |o.kind = initial
}
pred PseudoState_kind_partition2

{
	some  o : PseudoState |o.kind = deepHistory
}
pred PseudoState_kind_partition3

{
	some  o : PseudoState |o.kind = shallowHistory
}
pred PseudoState_kind_partition4

{
	some  o : PseudoState |o.kind = join
}
pred PseudoState_kind_partition5

{
	some  o : PseudoState |o.kind = fork
}
pred PseudoState_kind_partition6

{
	some  o : PseudoState |o.kind = junction
}
pred PseudoState_kind_partition7

{
	some  o : PseudoState |o.kind = choice
}
pred PseudoState_kind_partition8

{
	some  o : PseudoState |o.kind = entryPoint
}
pred PseudoState_kind_partition9

{
	some  o : PseudoState |o.kind = exitPoint
}
pred PseudoState_kind_partition10

{
	some  o : PseudoState |o.kind = terminate
}
pred PseudoState_stateMachine_partition1

{
	some  o : PseudoState |#o.stateMachine = 0
}
pred PseudoState_stateMachine_partition2

{
	some  o : PseudoState |#o.stateMachine = 1
}
pred PseudoState_stateMachine_partition3

{
	some  o : PseudoState |#o.stateMachine >= 5
}
pred ConnectionPointReference_state_partition1

{
	some  o : ConnectionPointReference |#o.state = 0
}
pred ConnectionPointReference_state_partition2

{
	some  o : ConnectionPointReference |#o.state = 1
}
pred ConnectionPointReference_state_partition3

{
	some  o : ConnectionPointReference |#o.state >= 5
}
pred ConnectionPointReference_entry_partition1

{
	some  o : ConnectionPointReference |#o.entry = 0
}
pred ConnectionPointReference_entry_partition2

{
	some  o : ConnectionPointReference |#o.entry = 1
}
pred ConnectionPointReference_entry_partition3

{
	some  o : ConnectionPointReference |#o.entry >= 5
}
pred ConnectionPointReference_exit_partition1

{
	some  o : ConnectionPointReference |#o.exit = 0
}
pred ConnectionPointReference_exit_partition2

{
	some  o : ConnectionPointReference |#o.exit = 1
}
pred ConnectionPointReference_exit_partition3

{
	some  o : ConnectionPointReference |#o.exit >= 5
}
pred mfAllRanges_StateMachine_region_partition1

{
	StateMachine_region_partition1
}
pred mfAllRanges_StateMachine_region_partition2

{
	StateMachine_region_partition2
}
pred mfAllRanges_StateMachine_region_partition3

{
	StateMachine_region_partition3
}
pred mfAllRanges_StateMachine_submachineState_partition1

{
	StateMachine_submachineState_partition1
}
pred mfAllRanges_StateMachine_submachineState_partition2

{
	StateMachine_submachineState_partition2
}
pred mfAllRanges_StateMachine_submachineState_partition3

{
	StateMachine_submachineState_partition3
}
pred mfAllRanges_StateMachine_connectionPoint_partition1

{
	StateMachine_connectionPoint_partition1
}
pred mfAllRanges_StateMachine_connectionPoint_partition2

{
	StateMachine_connectionPoint_partition2
}
pred mfAllRanges_StateMachine_connectionPoint_partition3

{
	StateMachine_connectionPoint_partition3
}
pred mfAllRanges_Region_stateMachine_partition1

{
	Region_stateMachine_partition1
}
pred mfAllRanges_Region_stateMachine_partition2

{
	Region_stateMachine_partition2
}
pred mfAllRanges_Region_stateMachine_partition3

{
	Region_stateMachine_partition3
}
pred mfAllRanges_Region_subvertex_partition1

{
	Region_subvertex_partition1
}
pred mfAllRanges_Region_subvertex_partition2

{
	Region_subvertex_partition2
}
pred mfAllRanges_Region_subvertex_partition3

{
	Region_subvertex_partition3
}
pred mfAllRanges_Region_transition_partition1

{
	Region_transition_partition1
}
pred mfAllRanges_Region_transition_partition2

{
	Region_transition_partition2
}
pred mfAllRanges_Region_transition_partition3

{
	Region_transition_partition3
}
pred mfAllRanges_Region_state_partition1

{
	Region_state_partition1
}
pred mfAllRanges_Region_state_partition2

{
	Region_state_partition2
}
pred mfAllRanges_Region_state_partition3

{
	Region_state_partition3
}
pred mfAllRanges_Vertex_container_partition1

{
	Vertex_container_partition1
}
pred mfAllRanges_Vertex_container_partition2

{
	Vertex_container_partition2
}
pred mfAllRanges_Vertex_container_partition3

{
	Vertex_container_partition3
}
pred mfAllRanges_Vertex_outgoing_partition1

{
	Vertex_outgoing_partition1
}
pred mfAllRanges_Vertex_outgoing_partition2

{
	Vertex_outgoing_partition2
}
pred mfAllRanges_Vertex_outgoing_partition3

{
	Vertex_outgoing_partition3
}
pred mfAllRanges_Vertex_incoming_partition1

{
	Vertex_incoming_partition1
}
pred mfAllRanges_Vertex_incoming_partition2

{
	Vertex_incoming_partition2
}
pred mfAllRanges_Vertex_incoming_partition3

{
	Vertex_incoming_partition3
}
pred mfAllRanges_Transition_container_partition1

{
	Transition_container_partition1
}
pred mfAllRanges_Transition_container_partition2

{
	Transition_container_partition2
}
pred mfAllRanges_Transition_container_partition3

{
	Transition_container_partition3
}
pred mfAllRanges_Transition_kind_partition3

{
	Transition_kind_partition3
}
pred mfAllRanges_Transition_target_partition1

{
	Transition_target_partition1
}
pred mfAllRanges_Transition_target_partition2

{
	Transition_target_partition2
}
pred mfAllRanges_Transition_target_partition3

{
	Transition_target_partition3
}
pred mfAllRanges_Transition_source_partition1

{
	Transition_source_partition1
}
pred mfAllRanges_Transition_source_partition2

{
	Transition_source_partition2
}
pred mfAllRanges_Transition_source_partition3

{
	Transition_source_partition3
}
pred mfAllRanges_Transition_effect_partition1

{
	Transition_effect_partition1
}
pred mfAllRanges_Transition_effect_partition2

{
	Transition_effect_partition2
}
pred mfAllRanges_Transition_effect_partition3

{
	Transition_effect_partition3
}
pred mfAllRanges_Transition_guard_partition1

{
	Transition_guard_partition1
}
pred mfAllRanges_Transition_guard_partition2

{
	Transition_guard_partition2
}
pred mfAllRanges_Transition_guard_partition3

{
	Transition_guard_partition3
}
pred mfAllRanges_Transition_trigger_partition1

{
	Transition_trigger_partition1
}
pred mfAllRanges_Transition_trigger_partition2

{
	Transition_trigger_partition2
}
pred mfAllRanges_Transition_trigger_partition3

{
	Transition_trigger_partition3
}
pred mfAllRanges_State_isComposite_partition1

{
	State_isComposite_partition1
}
pred mfAllRanges_State_isComposite_partition2

{
	State_isComposite_partition2
}
pred mfAllRanges_State_isOrthogonal_partition1

{
	State_isOrthogonal_partition1
}
pred mfAllRanges_State_isOrthogonal_partition2

{
	State_isOrthogonal_partition2
}
pred mfAllRanges_State_isSimple_partition1

{
	State_isSimple_partition1
}
pred mfAllRanges_State_isSimple_partition2

{
	State_isSimple_partition2
}
pred mfAllRanges_State_isSubmachineState_partition1

{
	State_isSubmachineState_partition1
}
pred mfAllRanges_State_isSubmachineState_partition2

{
	State_isSubmachineState_partition2
}
pred mfAllRanges_State_region_partition1

{
	State_region_partition1
}
pred mfAllRanges_State_region_partition2

{
	State_region_partition2
}
pred mfAllRanges_State_region_partition3

{
	State_region_partition3
}
pred mfAllRanges_State_connection_partition1

{
	State_connection_partition1
}
pred mfAllRanges_State_connection_partition2

{
	State_connection_partition2
}
pred mfAllRanges_State_connection_partition3

{
	State_connection_partition3
}
pred mfAllRanges_State_submachine_partition1

{
	State_submachine_partition1
}
pred mfAllRanges_State_submachine_partition2

{
	State_submachine_partition2
}
pred mfAllRanges_State_submachine_partition3

{
	State_submachine_partition3
}
pred mfAllRanges_State_entry_partition1

{
	State_entry_partition1
}
pred mfAllRanges_State_entry_partition2

{
	State_entry_partition2
}
pred mfAllRanges_State_entry_partition3

{
	State_entry_partition3
}
pred mfAllRanges_State_exit_partition1

{
	State_exit_partition1
}
pred mfAllRanges_State_exit_partition2

{
	State_exit_partition2
}
pred mfAllRanges_State_exit_partition3

{
	State_exit_partition3
}
pred mfAllRanges_State_doActivity_partition1

{
	State_doActivity_partition1
}
pred mfAllRanges_State_doActivity_partition2

{
	State_doActivity_partition2
}
pred mfAllRanges_State_doActivity_partition3

{
	State_doActivity_partition3
}
pred mfAllRanges_State_stateInvariant_partition1

{
	State_stateInvariant_partition1
}
pred mfAllRanges_State_stateInvariant_partition2

{
	State_stateInvariant_partition2
}
pred mfAllRanges_State_stateInvariant_partition3

{
	State_stateInvariant_partition3
}
pred mfAllRanges_State_deferrableTrigger_partition1

{
	State_deferrableTrigger_partition1
}
pred mfAllRanges_State_deferrableTrigger_partition2

{
	State_deferrableTrigger_partition2
}
pred mfAllRanges_State_deferrableTrigger_partition3

{
	State_deferrableTrigger_partition3
}
pred mfAllRanges_PseudoState_kind_partition10

{
	PseudoState_kind_partition10
}
pred mfAllRanges_PseudoState_stateMachine_partition1

{
	PseudoState_stateMachine_partition1
}
pred mfAllRanges_PseudoState_stateMachine_partition2

{
	PseudoState_stateMachine_partition2
}
pred mfAllRanges_PseudoState_stateMachine_partition3

{
	PseudoState_stateMachine_partition3
}
pred mfAllRanges_ConnectionPointReference_state_partition1

{
	ConnectionPointReference_state_partition1
}
pred mfAllRanges_ConnectionPointReference_state_partition2

{
	ConnectionPointReference_state_partition2
}
pred mfAllRanges_ConnectionPointReference_state_partition3

{
	ConnectionPointReference_state_partition3
}
pred mfAllRanges_ConnectionPointReference_entry_partition1

{
	ConnectionPointReference_entry_partition1
}
pred mfAllRanges_ConnectionPointReference_entry_partition2

{
	ConnectionPointReference_entry_partition2
}
pred mfAllRanges_ConnectionPointReference_entry_partition3

{
	ConnectionPointReference_entry_partition3
}
pred mfAllRanges_ConnectionPointReference_exit_partition1

{
	ConnectionPointReference_exit_partition1
}
pred mfAllRanges_ConnectionPointReference_exit_partition2

{
	ConnectionPointReference_exit_partition2
}
pred mfAllRanges_ConnectionPointReference_exit_partition3

{
	ConnectionPointReference_exit_partition3
}
pred mfAllPartitions_StateMachine_region_partition1_StateMachine_region_partition2_StateMachine_region_partition3

{
	StateMachine_region_partition1 and StateMachine_region_partition2 and StateMachine_region_partition3 
}
pred mfAllPartitions_StateMachine_submachineState_partition1_StateMachine_submachineState_partition2_StateMachine_submachineState_partition3

{
	StateMachine_submachineState_partition1 and StateMachine_submachineState_partition2 and StateMachine_submachineState_partition3 
}
pred mfAllPartitions_StateMachine_connectionPoint_partition1_StateMachine_connectionPoint_partition2_StateMachine_connectionPoint_partition3

{
	StateMachine_connectionPoint_partition1 and StateMachine_connectionPoint_partition2 and StateMachine_connectionPoint_partition3 
}
pred mfAllPartitions_Region_stateMachine_partition1_Region_stateMachine_partition2_Region_stateMachine_partition3

{
	Region_stateMachine_partition1 and Region_stateMachine_partition2 and Region_stateMachine_partition3 
}
pred mfAllPartitions_Region_subvertex_partition1_Region_subvertex_partition2_Region_subvertex_partition3

{
	Region_subvertex_partition1 and Region_subvertex_partition2 and Region_subvertex_partition3 
}
pred mfAllPartitions_Region_transition_partition1_Region_transition_partition2_Region_transition_partition3

{
	Region_transition_partition1 and Region_transition_partition2 and Region_transition_partition3 
}
pred mfAllPartitions_Region_state_partition1_Region_state_partition2_Region_state_partition3

{
	Region_state_partition1 and Region_state_partition2 and Region_state_partition3 
}
pred mfAllPartitions_Vertex_container_partition1_Vertex_container_partition2_Vertex_container_partition3

{
	Vertex_container_partition1 and Vertex_container_partition2 and Vertex_container_partition3 
}
pred mfAllPartitions_Vertex_outgoing_partition1_Vertex_outgoing_partition2_Vertex_outgoing_partition3

{
	Vertex_outgoing_partition1 and Vertex_outgoing_partition2 and Vertex_outgoing_partition3 
}
pred mfAllPartitions_Vertex_incoming_partition1_Vertex_incoming_partition2_Vertex_incoming_partition3

{
	Vertex_incoming_partition1 and Vertex_incoming_partition2 and Vertex_incoming_partition3 
}
pred mfAllPartitions_Transition_container_partition1_Transition_container_partition2_Transition_container_partition3

{
	Transition_container_partition1 and Transition_container_partition2 and Transition_container_partition3 
}
pred mfAllPartitions_Transition_kind_partition3

{
	Transition_kind_partition3 
}
pred mfAllPartitions_Transition_target_partition1_Transition_target_partition2_Transition_target_partition3

{
	Transition_target_partition1 and Transition_target_partition2 and Transition_target_partition3 
}
pred mfAllPartitions_Transition_source_partition1_Transition_source_partition2_Transition_source_partition3

{
	Transition_source_partition1 and Transition_source_partition2 and Transition_source_partition3 
}
pred mfAllPartitions_Transition_effect_partition1_Transition_effect_partition2_Transition_effect_partition3

{
	Transition_effect_partition1 and Transition_effect_partition2 and Transition_effect_partition3 
}
pred mfAllPartitions_Transition_guard_partition1_Transition_guard_partition2_Transition_guard_partition3

{
	Transition_guard_partition1 and Transition_guard_partition2 and Transition_guard_partition3 
}
pred mfAllPartitions_Transition_trigger_partition1_Transition_trigger_partition2_Transition_trigger_partition3

{
	Transition_trigger_partition1 and Transition_trigger_partition2 and Transition_trigger_partition3 
}
pred mfAllPartitions_State_isComposite_partition1_State_isComposite_partition2

{
	State_isComposite_partition1 and State_isComposite_partition2 
}
pred mfAllPartitions_State_isOrthogonal_partition1_State_isOrthogonal_partition2

{
	State_isOrthogonal_partition1 and State_isOrthogonal_partition2 
}
pred mfAllPartitions_State_isSimple_partition1_State_isSimple_partition2

{
	State_isSimple_partition1 and State_isSimple_partition2 
}
pred mfAllPartitions_State_isSubmachineState_partition1_State_isSubmachineState_partition2

{
	State_isSubmachineState_partition1 and State_isSubmachineState_partition2 
}
pred mfAllPartitions_State_region_partition1_State_region_partition2_State_region_partition3

{
	State_region_partition1 and State_region_partition2 and State_region_partition3 
}
pred mfAllPartitions_State_connection_partition1_State_connection_partition2_State_connection_partition3

{
	State_connection_partition1 and State_connection_partition2 and State_connection_partition3 
}
pred mfAllPartitions_State_submachine_partition1_State_submachine_partition2_State_submachine_partition3

{
	State_submachine_partition1 and State_submachine_partition2 and State_submachine_partition3 
}
pred mfAllPartitions_State_entry_partition1_State_entry_partition2_State_entry_partition3

{
	State_entry_partition1 and State_entry_partition2 and State_entry_partition3 
}
pred mfAllPartitions_State_exit_partition1_State_exit_partition2_State_exit_partition3

{
	State_exit_partition1 and State_exit_partition2 and State_exit_partition3 
}
pred mfAllPartitions_State_doActivity_partition1_State_doActivity_partition2_State_doActivity_partition3

{
	State_doActivity_partition1 and State_doActivity_partition2 and State_doActivity_partition3 
}
pred mfAllPartitions_State_stateInvariant_partition1_State_stateInvariant_partition2_State_stateInvariant_partition3

{
	State_stateInvariant_partition1 and State_stateInvariant_partition2 and State_stateInvariant_partition3 
}
pred mfAllPartitions_State_deferrableTrigger_partition1_State_deferrableTrigger_partition2_State_deferrableTrigger_partition3

{
	State_deferrableTrigger_partition1 and State_deferrableTrigger_partition2 and State_deferrableTrigger_partition3 
}
pred mfAllPartitions_PseudoState_kind_partition10

{
	PseudoState_kind_partition10 
}
pred mfAllPartitions_PseudoState_stateMachine_partition1_PseudoState_stateMachine_partition2_PseudoState_stateMachine_partition3

{
	PseudoState_stateMachine_partition1 and PseudoState_stateMachine_partition2 and PseudoState_stateMachine_partition3 
}
pred mfAllPartitions_ConnectionPointReference_state_partition1_ConnectionPointReference_state_partition2_ConnectionPointReference_state_partition3

{
	ConnectionPointReference_state_partition1 and ConnectionPointReference_state_partition2 and ConnectionPointReference_state_partition3 
}
pred mfAllPartitions_ConnectionPointReference_entry_partition1_ConnectionPointReference_entry_partition2_ConnectionPointReference_entry_partition3

{
	ConnectionPointReference_entry_partition1 and ConnectionPointReference_entry_partition2 and ConnectionPointReference_entry_partition3 
}
pred mfAllPartitions_ConnectionPointReference_exit_partition1_ConnectionPointReference_exit_partition2_ConnectionPointReference_exit_partition3

{
	ConnectionPointReference_exit_partition1 and ConnectionPointReference_exit_partition2 and ConnectionPointReference_exit_partition3 
}
pred GenerateAndTestSimple

{

}
run GenerateAndTestSimple  for 20