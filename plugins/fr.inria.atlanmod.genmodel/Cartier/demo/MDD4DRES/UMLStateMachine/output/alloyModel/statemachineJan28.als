module umlstatemachineselect

open util/boolean as Bool



enum TransitionKind { internal,local,external }

enum PseudostateKind { initial,deepHistory,shallowHistory,join,fork,junction,choice,entryPoint,exitPoint,terminate }


one  sig StateMachine extends Behavior 
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
 abstract sig Vertex  
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

//For Model Fragments
sig Parameters
{
	max : one Int,
	min : one Int
}



fact Region_containers
{
	all o1: StateMachine.region, o2: State.region, o3: Transition.effect, o4 : FinalState.region |disj[o1,o2,o3,o4]

}

fact PseudoState_containers
{
	all o1: StateMachine.connectionPoint, o2: Region.subvertex |disj[o1,o2]

}

fact ConnectionPointReference_containers
{
all o1: State.connection, o2: Region.subvertex | disj[o1,o2]

}

fact Behavior_containers
{
	all o1: Transition.effect, o2: State.entry, o3: State.exit, o4 : State.doActivity |disj[o1,o2,o3,o4]
}

fact Constraint_containers
{
		all o1: Transition.guard, o2: State.stateInvariant, o3: FinalState.stateInvariant |disj[o1,o2,o3]

}

fact Trigger_containers
{
	all o1: Transition.trigger, o2: State.deferrableTrigger |disj[o1,o2]
}

fact StateMachine_region_composite
{
	 all  owningClassObject1 : StateMachine, owningClassObject2 : StateMachine |all  property1 : owningClassObject1.region, property2 : owningClassObject2.region |property1 = property2 implies owningClassObject1 = owningClassObject2
}

fact StateMachine_region_Region_stateMachine_opposite
{
	all  object1 : StateMachine, object2 : Region |object2 in object1.region implies object1 in object2.stateMachine
}

fact StateMachine_submachineState_State_submachine_opposite
{
	all  object1 : StateMachine, object2 : State |object2 in object1.submachineState implies object1 in object2.submachine
}

fact StateMachine_connectionPoint_composite
{
	 all  owningClassObject1 : StateMachine, owningClassObject2 : StateMachine |all  property1 : owningClassObject1.connectionPoint, property2 : owningClassObject2.connectionPoint |property1 = property2 implies owningClassObject1 = owningClassObject2
}

fact Region_subvertex_composite
{
	 all  owningClassObject1 : Region, owningClassObject2 : Region |all  property1 : owningClassObject1.subvertex, property2 : owningClassObject2.subvertex |property1 = property2 implies owningClassObject1 = owningClassObject2
}

fact Region_subvertex_Vertex_container_opposite
{
	all  object1 : Region, object2 : Vertex |object2 in object1.subvertex implies object1 in object2.container
}

fact Region_transition_composite
{
	all  owningClassObject1 : Region, owningClassObject2 : Region |all  property1 : owningClassObject1.transition, property2 : owningClassObject2.transition |property1 = property2 implies owningClassObject1 = owningClassObject2
}

fact Region_transition_Transition_container_opposite
{
	all  object1 : Region, object2 : Transition |object2 in object1.transition implies object1 in object2.container
}

fact Region_state_State_region_opposite
{
	all  object1 : Region, object2 : State |object2 in object1.state implies object1 in object2.region
}

fact Vertex_outgoing_Transition_source_opposite
{
	all  object1 : Vertex, object2 : Transition |object2 in object1.outgoing implies object1 in object2.source
}

fact Vertex_incoming_Transition_target_opposite
{
	all  object1 : Vertex, object2 : Transition |object2 in object1.incoming implies object1 in object2.target
}

fact Transition_effect_composite
{
	all  owningClassObject1 : Transition, owningClassObject2 : Transition |all  property1 : owningClassObject1.effect, property2 : owningClassObject2.effect |property1 = property2 implies owningClassObject1 = owningClassObject2
}

fact Transition_guard_composite
{
	 all  owningClassObject1 : Transition, owningClassObject2 : Transition |all  property1 : owningClassObject1.guard, property2 : owningClassObject2.guard |property1 = property2 implies owningClassObject1 = owningClassObject2
}

fact Transition_trigger_composite
{
	 all  owningClassObject1 : Transition, owningClassObject2 : Transition |all  property1 : owningClassObject1.trigger, property2 : owningClassObject2.trigger |property1 = property2 implies owningClassObject1 = owningClassObject2
}

fact State_region_composite
{
	all  owningClassObject1 : State, owningClassObject2 : State |all  property1 : owningClassObject1.region, property2 : owningClassObject2.region |property1 = property2 implies owningClassObject1 = owningClassObject2
}

fact State_connection_composite
{
	all  owningClassObject1 : State, owningClassObject2 : State |all  property1 : owningClassObject1.connection, property2 : owningClassObject2.connection |property1 = property2 implies owningClassObject1 = owningClassObject2
}

fact State_connection_ConnectionPointReference_state_opposite
{
	all  object1 : State, object2 : ConnectionPointReference |object2 in object1.connection implies object1 in object2.state
}

fact State_entry_composite
{
	 all  owningClassObject1 : State, owningClassObject2 : State |all  property1 : owningClassObject1.entry, property2 : owningClassObject2.entry |property1 = property2 implies owningClassObject1 = owningClassObject2
}

fact State_exit_composite
{
	all  owningClassObject1 : State, owningClassObject2 : State |all  property1 : owningClassObject1.exit, property2 : owningClassObject2.exit |property1 = property2 implies owningClassObject1 = owningClassObject2
}

fact State_doActivity_composite
{
	all  p : Behavior |p in State.doActivity and all  owningClassObject1 : State, owningClassObject2 : State |all  property1 : owningClassObject1.doActivity, property2 : owningClassObject2.doActivity |property1 = property2 implies owningClassObject1 = owningClassObject2
}

fact State_stateInvariant_composite
{
	 all  owningClassObject1 : State, owningClassObject2 : State |all  property1 : owningClassObject1.stateInvariant, property2 : owningClassObject2.stateInvariant |property1 = property2 implies owningClassObject1 = owningClassObject2
}

fact State_deferrableTrigger_composite
{
	all  owningClassObject1 : State, owningClassObject2 : State |all  property1 : owningClassObject1.deferrableTrigger, property2 : owningClassObject2.deferrableTrigger |property1 = property2 implies owningClassObject1 = owningClassObject2
}

fact PseudoState_stateMachine_StateMachine_connectionPoint_opposite
{
	all  object1 : PseudoState, object2 : StateMachine |object2 in object1.stateMachine implies object1 in object2.connectionPoint
}

/////////////////////////////////////////
//ConnectionPointReference constraints///
////////////////////////////////////////

//The entry Pseudostates must be Pseudostates with kind entryPoint
//entry->notEmpty() implies entry->forAll(e|e.kind = #entryPoint)

fact Inv_ConnectionPointReference_1
{
all object1 : ConnectionPointReference | #object1.entry>0 implies (all object2 : object1.entry | object2.kind =entryPoint)
}

//The exit Pseudostates must be Pseudostates with kind exitPoint
//exit->notEmpty() implies exit->forAll(e|e.kind = #exitPoint)
fact Inv_ConnectionPointReference_2
{
all object1:ConnectionPointReference | #object1.exit>0 implies (all object2: object1.exit | object2.kind =exitPoint)
}
/////////////////////////
//FiniteState constraints//
////////////////////////

//A final state cannot have any outgoing transitions
//self.outgoing->size() =0

fact Inv_FinalState_1
{
all object1:FinalState | #object1.outgoing>0
}

//A final state cannot have regions

fact Inv_FinalState_2
{
all object1:FinalState | #object1.region=0
}
//A final state cannot reference a submachine

fact Inv_FinalState_3
{
all object1:FinalState | #object1.submachine=0
}
//A final state has no entry behaviour 
fact Inv_FinalState_4
{
all object1:FinalState | #object1.entry=0
}
//A final state has no exit behaviour
fact Inv_FinalState_5
{
all object1:FinalState | #object1.exit=0
}
//A final state has no state (do Acitivity) behavior
fact Inv_FinalState_6
{
all object1:FinalState | #object1.doActivity=0
}

//PseudoState Constraints

//An initial vertex can have at most one outgoing transition
//(self.kind = #initial) implies ((self.outgoing->size <= 1)
fact Inv_PseudoState_1
{
all object:PseudoState|object.kind =initial implies #object.outgoing<=1
}
//History vertices can have at most one outgoing transition
//((self.kind=#deepHistory) or (self.kind =#shallowHistory) implies (self.outgoing->size <= 1)
fact Inv_PseudoState_2
{
all object:PseudoState|(object.kind==deepHistory) or (object.kind==shallowHistory) implies #object.outgoing<=1
}
//In a complete statemachine, a join vertex must have at least two incoming transitions and exactly one outgoing transition
//(self.kind=#join) implies ((self.outgoing->size=1) and (self.incoming->size>=2))

fact Inv_PseudoState_3
{
all object:PseudoState|object.kind==join implies #object.outgoing=1 and #object.incoming>=2
}
//All transitions incoming a join vertex must originate in different regions of an orthogonal state.
//(self.kind=#join) implies self.incoming->forAll(t1,t2 | t1 != t2 implies (self.stateMachine.LCA(t1.source,t2.source).container.isOrthogonal)

/*fact Inv_PseudoState_4
{
all object:PseudoState | object.kind==join implies all object1 : object.incoming, object2 : object.incoming | object1 != object2 implies object.stateMachine.
}*/
//In a complete statemachine, a fork vertex must have at least two outgoing transitions and exactly one incoming transition
//(self.kind=#fork) implies ((self.incoming->size=1) and (self.outgoing->size>=2))
fact Inv_PseudoState_5
{
all object:PseudoState | object.kind==fork implies (#object.incoming=1 and #object.outgoing>=2)
}
//All transitions outgoing a fork vertex must target states in different regions of an orthogonal state
//(self.kind=#fork) implies self.outgoing->forAll(t1,t2|t1!=t2 implies (self.stateMachine.LCA(t1.target,t2.target).container.isOrthogonal)
/*
fact Inv_PseudoState_6
{
all object:PseudoState | object.kind==fork 
}
*/
//In a complete statemachine, a junction vertex must have at least one incoming and one outgoing transition
//(self.kind=#junction) implies ((self.incoming->size>=1) and (self.outgoing->size>=1))
fact Inv_PseudoState_7
{
all object:PseudoState | object.kind==junction implies (#object.incoming>=1 and #object.outgoing>=1)
}
//In a complete statemachine, a choice vertex must have at least one incoming and one outgoing transition.
//(self.kind = #choice) implies ((self.incoming->size >= 1) and (self.outgoing->size >= 1))
fact Inv_PseudoState_8
{
all object:PseudoState | object.kind==choice implies (#object.incoming>=1 and #object.outgoing>=1)
}
//Pseudostates of kind entryPoint can only be defined in the topmost regions of a StateMachine.
//(kind = #entryPoint) implies (owner.oclIsKindOf(Region) and owner.owner.oclIsKindOf(StateMachine))
fact Inv_PseudoState_9
{
all object:PseudoState | object.kind==entryPoint implies (object.container in Region and object.container.stateMachine in StateMachine)
}
//Pseudostates of kind exitPoint can only be defined in the topmost regions of a StateMachine.
//(kind = #exitPoint) implies (owner.oclIsKindOf(Region) and owner.owner.oclIsKindOf(StateMachine))
fact Inv_PseudoState_10
{
all object:PseudoState | object.kind==exitPoint implies (object.container in Region and object.container.stateMachine in StateMachine)
}
//////////////////////
//Region Constraints//
/////////////////////

//A region can have at most one initial vertex.
//self.subvertex->select (v | v.oclIsKindOf(Pseudostate))->select(p : Pseudostate | p.kind = #initial)->size() <= 1
fact Inv_Region_1
{
all object1 : Region | all object2 : object1.subvertex, object3: object1.subvertex | (object2.kind == initial and object3.kind==initial) implies object2=object3
}
//A region can have at most one deep history vertex.
//self.subvertex->select (v | v.oclIsKindOf(Pseudostate))->select(p : Pseudostate | p.kind = #deepHistory)->size() <= 1
fact Inv_Region_2
{
all object1: Region | all object2 : object1.subvertex, object3: object1.subvertex | (object2.kind==deepHistory and object3.kind==deepHistory) implies object2=object3
}
//A region can have at most one shallow history vertex.
//self.subvertex->select(v | v.oclIsKindOf(Pseudostate))->select(p : Pseudostate | p.kind = #shallowHistory)->size() <= 1
fact Inv_Region_3
{
all object1: Region | all object2 : object1.subvertex, object3: object1.subvertex | (object2.kind==shallowHistory and object3.kind==shallowHistory) implies object2=object3
}

//If a Region is owned by a StateMachine, then it cannot also be owned by a State and vice versa.
//(stateMachine->notEmpty() implies state->isEmpty()) and (state->notEmpty() implies stateMachine->isEmpty())
fact Inv_Region_4
{

all object : Region | #object.stateMachine>0 implies #object.state==0 and #object.state>0 implies #object.stateMachine=0
}

//The redefinition context of a region is the nearest containing statemachine.
//redefinitionContext =let sm = containingStateMachine() in if sm.context->isEmpty() or sm.general->notEmpty() then sm else sm.context endif

///////////////////////
//State Constraints////
//////////////////////



//There have to be at least two regions in an orthogonal composite state.
//(self.isOrthogonal) implies (self.region->size >= 2)
fact Inv_State_1
{
all object:State | object.isOrthogonal == True implies #object.region>=2
}
//Only submachine states can have connection point references.
//isSubmachineState implies connection->notEmpty ( )
fact Inv_State_2
{
all object:State | object.isSubmachineState == True implies #object.connection>=1
}
//The connection point references used as destinations/sources of transitions associated with a submachine state must be
//defined as entry/exit points in the submachine state machine.

//A state is not allowed to have both a submachine and regions.
//isComposite implies not isSubmachineState
fact Inv_State_4
{
all object: State | object.isComposite == True implies object.isSubmachineState == False
}
//A simple state is a state without any regions.
//isSimple = region.isEmpty()
fact Inv_State_5
{
all object: State | object.isSimple == True implies #object.region = 0
}
//A composite state is a state with at least one region.
//isComposite = content.notEmpty()
fact Inv_State_6
{
all object : State | object.isComposite == True implies #object.region > 0
}
//An orthogonal state is a composite state with at least 2 regions.
//isOrthogonal = (region->size () > 1)

fact Inv_State_7
{
all object : State | object.isOrthogonal == True implies object.isComposite= True and #object.region > 1
}
//Only submachine states can have a reference statemachine.
//isSubmachineState = submachine.notEmpty()

fact Inv_State_8
{
all object : State | object.isSubmachineState == True implies #object.submachine > 0
}
//The redefinition context of a state is the nearest containing statemachine.
//redefinitionContext = let sm = containingStateMachine() in if sm.context->isEmpty() or sm.general->notEmpty() then sm else sm.context endif

//Only composite states can have entry or exit pseudostates defined.
//connectionPoint->notEmpty() implies isComoposite
fact Inv_State_10
{
all object : State | #object.connection>0 implies object.isComposite = True
}
//Only entry or exit pseudostates can serve as connection points.
//connectionPoint->forAll(cp|cp.kind = #entry or cp.kind = #exit)
/*
fact Inv_State_11
{
all object1 : State |all object2 : object1.connection |  object2.kind = entryPoint or object2.kind=exitPoint
}*/

/////////////////////////////
//Statemachine constraints///
////////////////////////////

//The classifier context of a state machine cannot be an interface.
//context->notEmpty() implies not context.oclIsKindOf(Interface)

//The context classifier of the method state machine of a behavioral feature must be the classifier that owns the behavioral
//feature.specification->notEmpty() implies (context->notEmpty() and specification->featuringClassifier->exists (c | c = context))
//entry

//The connection points of a state machine are pseudostates of kind entry point or exit point.
//conectionPoint->forAll (c | c.kind = #entryPoint or c.kind = #exitPoint)
fact Inv_StateMachine_1
{
all object1 : StateMachine | (all object2 : object1.connectionPoint |  object2.kind = entryPoint or object2.kind=exitPoint)
}

//A state machine as the method for a behavioral feature cannot have entry/exit connection points.
//specification->notEmpty() implies connectionPoint->isEmpty()
fact Inv_StateMachine_2
{
all object1: State | (#object1.doActivity =1 and object1.doActivity in StateMachine) implies #object1.doActivity.connectionPoint=0
}
///////////////////////////
//Transtion constraints////
//////////////////////////

//A fork segment must not have guards or triggers.
//(source.oclIsKindOf(Pseudostate) and source.kind = #fork) implies (guard->isEmpty() and trigger->isEmpty())
fact Inv_Transition_1
{
 all object:Transition | (object.source in PseudoState and object.source.kind = fork) implies #object.guard=0 and #object.trigger=0
}
//A join segment must not have guards or triggers.
//(target.oclIsKindOf(Pseudostate) and target.kind = #join) implies (guard->isEmpty() and trigger->isEmpty()))
fact Inv_Transition_2
{
 all object:Transition | (object.target in PseudoState and object.target.kind = join) implies #object.guard=0 and #object.trigger=0
}

//A fork segment must always target a state.
//(source.oclIsKindOf(Pseudostate) and source.kind = #fork) implies (target.oclIsKindOf(State))
fact Inv_Transition_3
{
 all object:Transition | (object.source in PseudoState and object.source.kind = fork) implies object.target in State
}

// A join segment must always originate from a state.
//(target.oclIsKindOf(Pseudostate) and target.kind = #join) implies (source.oclIsKindOf(State))
fact Inv_Transition_4
{
 all object:Transition | (object.target in PseudoState and object.target.kind = join) implies object.source in State
}
// Transitions outgoing pseudostates may not have a trigger.
//source.oclIsKindOf(Pseudostate) and ((source.kind <> #junction) and (source.kind <> #join) and (source.kind <> #initial)) implies trigger->isEmpty()
fact Inv_Transition_5
{
 all object:Transition | (object.source in PseudoState and object.source.kind != junction and object.source.kind!=join and object.source.kind !=initial) implies #object.trigger=0
}
// An initial transition at the topmost level (region of a statemachine) either has no trigger or it has a trigger with the
//stereotype “create.”
/*self.source.oclIsKindOf(Pseudostate) implies
(self.source.oclAsType(Pseudostate).kind = #initial) implies
(self.source.container = self.stateMachine.top) implies
((self.trigger->isEmpty) or
(self.trigger.stereotype.name = 'create'))*/
/*fact Inv_Transition_6
{
 all object:Transition | (object.source in PseudoState and object.source.kind == initial and object.source.container =self.stateMachine) implies #object.trigger =0 or object.trigger in "create"
}*/
//In case of more than one trigger, the signatures of these must be compatible in case the parameters of the signal are
//assigned to local variables/attributes.

// The redefinition context of a transition is the nearest containing statemachine.
/*redefinitionContext =
let sm = containingStateMachine() in
if sm.context->isEmpty() or sm.general->notEmpty() then
sm
else
sm.context
endif*/



/////////////////////////////
//TransitionKind constraints//
/////////////////////////////

//The source state of a transition with transition kind local must be a composite state.
fact Inv_TransitionKind_1
{
all object: Transition | (object.kind == local) implies  object.source.isComposite=True

}

// The source state of a transition with transition kind external must be a composite state.

fact Inv_TransitionKind_2
{

all object: Transition | (object.kind == external) implies  object.source.isComposite=True

}
////////////////////////////////////
//Model Fragments from AllRanges //
////////////////////////////////////

fact ParameterFact
{
	Parameters.max=5 and
	Parameters.min = 1
}

/*
The model fragment with the following object fragments 
The object fragment for the class StateMachine and the following constraints 
0 StateMachine
*/

pred mfAllRanges1 
{
#StateMachine=0
}
/*
The model fragment with the following object fragments 
The object fragment for the class StateMachine and the following constraints 
1 StateMachine
*/

pred mfAllRanges2
{
#StateMachine=1
}



/*
The model fragment with the following object fragments 
The object fragment for the class StateMachine and the following constraints 
The integer range from 1 to 1 for the region property 
*/

pred mfAllRanges3
{
some o : StateMachine | #o.region=1
}

/*
The model fragment with the following object fragments 
The object fragment for the class StateMachine and the following constraints 
The integer range from 2 to 20000 for the region property 
*/

pred mfAllRanges4
{
some o : StateMachine | #o.region>Parameters.min and #o.region <= Parameters.max
}

/*
The model fragment with the following object fragments 
The object fragment for the class StateMachine and the following constraints 
The integer range from 1 to 1 for the submachineState property 
*/

pred mfAllRanges5
{
some o : StateMachine | #o.submachineState=1
}

/*
The model fragment with the following object fragments 
The object fragment for the class StateMachine and the following constraints 
The integer range from 2 to 20000 for the submachineState property 
*/

pred mfAllRanges6
{
some o : StateMachine | #o.submachineState>Parameters.min and #o.submachineState <=Parameters.max
}

/*
The model fragment with the following object fragments 
The object fragment for the class StateMachine and the following constraints 
The integer range from 1 to 1 for the connectionPoint property 
*/

pred mfAllRanges7
{
some o : StateMachine | #o.connectionPoint=1
}

/*
The model fragment with the following object fragments 
The object fragment for the class StateMachine and the following constraints 
The integer range from 2 to 20000 for the connectionPoint property 
*/

pred mfAllRanges8
{
some o : StateMachine | #o.connectionPoint > Parameters.min and #o.connectionPoint <= Parameters.max
}

/*
The model fragment with the following object fragments 
The object fragment for the class Region and the following constraints 
The integer range from 0 to 0 for the stateMachine property 
*/

pred mfAllRanges9
{
some o : Region | #o.stateMachine = 0 
}

/*
The model fragment with the following object fragments 
The object fragment for the class Region and the following constraints 
The integer range from 1 to 1 for the stateMachine property 
*/

pred mfAllRanges10
{
some o : Region | #o.stateMachine = 1 
}

/*
The model fragment with the following object fragments 
The object fragment for the class Region and the following constraints 
The integer range from 0 to 0 for the subvertex property 
*/

pred mfAllRanges11
{
some o : Region | #o.subvertex = 0
}

/*
The model fragment with the following object fragments 
The object fragment for the class Region and the following constraints 
The integer range from 1 to 1 for the subvertex property 
*/

pred mfAllRanges12
{
some o : Region | #o.subvertex = 1
}



/*
The model fragment with the following object fragments 
The object fragment for the class Region and the following constraints 
The integer range from 2 to 20000 for the subvertex property 
*/


pred mfAllRanges13
{
some o : Region | #o.subvertex > Parameters.min and #o.subvertex <= Parameters.max
}


/*
The model fragment with the following object fragments 
The object fragment for the class Region and the following constraints 
The integer range from 0 to 0 for the transition property 
*/


pred mfAllRanges14
{
some o : Region | #o.transition =0
}

/*
The model fragment with the following object fragments 
The object fragment for the class Region and the following constraints 
The integer range from 1 to 1 for the transition property 
*/

pred mfAllRanges15
{
some o : Region | #o.transition =1
}

/*
The model fragment with the following object fragments 
The object fragment for the class Region and the following constraints 
The integer range from 2 to 20000 for the transition property 
*/


pred mfAllRanges16
{
some o : Region | #o.transition > Parameters.min and #o.transition <= Parameters.max
}

/*
The model fragment with the following object fragments 
The object fragment for the class Region and the following constraints 
The integer range from 0 to 0 for the state property 
*/



pred mfAllRanges17
{
some o : Region | #o.state =0
}


/*
The model fragment with the following object fragments 
The object fragment for the class Region and the following constraints 
The integer range from 1 to 1 for the state property 
*/



pred mfAllRanges18
{
some o : Region | #o.state =1
}

/*
The model fragment with the following object fragments 
The object fragment for the class Vertex and the following constraints 
The integer range from 0 to 0 for the container property 
*/



pred mfAllRanges19
{
some o : Vertex | #o.container = 0
}

/*
The model fragment with the following object fragments 
The object fragment for the class Vertex and the following constraints 
The integer range from 1 to 1 for the container property 
*/


pred mfAllRanges20
{
some o : Vertex | #o.container = 1
}

/*
The model fragment with the following object fragments 
The object fragment for the class Vertex and the following constraints 
The integer range from 0 to 0 for the outgoing property 
*/


pred mfAllRanges21
{
some o : Vertex | #o.outgoing = 0
}
/*
The model fragment with the following object fragments 
The object fragment for the class Vertex and the following constraints 
The integer range from 1 to 1 for the outgoing property 
*/


pred mfAllRanges22
{
some o : Vertex | #o.outgoing = 1
}

/*
The model fragment with the following object fragments 
The object fragment for the class Vertex and the following constraints 
The integer range from 2 to 20000 for the outgoing property 
*/


pred mfAllRanges23
{
some o : Vertex | #o.outgoing > Parameters.min and #o.outgoing <= Parameters.max
}


/*
The model fragment with the following object fragments 
The object fragment for the class Vertex and the following constraints 
The integer range from 0 to 0 for the incoming property 
*/


pred mfAllRanges24
{
some o : Vertex | #o.incoming = 0
}
/*
The model fragment with the following object fragments 
The object fragment for the class Vertex and the following constraints 
The integer range from 1 to 1 for the incoming property 
*/

pred mfAllRanges25
{
some o : Vertex | #o.incoming = 1
}

/*
The model fragment with the following object fragments 
The object fragment for the class Vertex and the following constraints 
The integer range from 2 to 20000 for the incoming property 
*/

pred mfAllRanges26
{
some o : Vertex | #o.incoming > Parameters.min and #o.incoming <= Parameters.max
}

/*
The model fragment with the following object fragments 
The object fragment for the class Transition and the following constraints 
The integer range from 1 to 1 for the container property 
*/

pred mfAllRanges27
{
some o : Transition | #o.container = 1
}


/*
The model fragment with the following object fragments 
The object fragment for the class Transition and the following constraints 
The integer range from 1 to 1 for the target property 
*/


pred mfAllRanges28
{
some o : Transition | #o.target = 1
}
/*
The model fragment with the following object fragments 
The object fragment for the class Transition and the following constraints 
The integer range from 1 to 1 for the source property 
*/


pred mfAllRanges29
{
some o : Transition | #o.source = 1
}

/*
The model fragment with the following object fragments 
The object fragment for the class Transition and the following constraints 
The integer range from 0 to 0 for the effect property 
*/


pred mfAllRanges30
{
some o : Transition | #o.effect = 0
}

/*
The model fragment with the following object fragments 
The object fragment for the class Transition and the following constraints 
The integer range from 1 to 1 for the effect property 
*/


pred mfAllRanges31
{
some o : Transition | #o.effect = 1
}

/*
The model fragment with the following object fragments 
The object fragment for the class Transition and the following constraints 
The integer range from 0 to 0 for the guard property 
*/


pred mfAllRanges32
{
some o : Transition | #o.guard = 0
}

/*
The model fragment with the following object fragments 
The object fragment for the class Transition and the following constraints 
The integer range from 1 to 1 for the guard property 
*/

pred mfAllRanges33
{
some o : Transition | #o.guard = 1
}
/*
The model fragment with the following object fragments 
The object fragment for the class State and the following constraints 
The integer range from 0 to 0 for the region property 
*/

pred mfAllRanges34
{
some o : State | #o.region = 0
}
/*
The model fragment with the following object fragments 
The object fragment for the class State and the following constraints 
The integer range from 1 to 1 for the region property 
*/


pred mfAllRanges35
{
some o : State | #o.region = 1
}

/*
The model fragment with the following object fragments 
The object fragment for the class State and the following constraints 
The integer range from 2 to 20000 for the region property 
*/

pred mfAllRanges36
{
some o : State | #o.region > Parameters.min and #o.region <= Parameters.max
}
/*
The model fragment with the following object fragments 
The object fragment for the class State and the following constraints 
The integer range from 0 to 0 for the connection property 
*/

pred mfAllRanges37
{
some o : State | #o.connection =0
}
/*
The model fragment with the following object fragments 
The object fragment for the class State and the following constraints 
The integer range from 1 to 1 for the connection property 
*/

pred mfAllRanges38
{
some o : State | #o.connection =1
}

/*
The model fragment with the following object fragments 
The object fragment for the class State and the following constraints 
The integer range from 2 to 20000 for the connection property 
*/

pred mfAllRanges39
{
some o : State | #o.connection > Parameters.min and #o.connection <= Parameters.max
}
/*
The model fragment with the following object fragments 
The object fragment for the class State and the following constraints 
The integer range from 0 to 0 for the submachine property 
*/

pred mfAllRanges40
{
some o : State | #o.submachine =0
}
/*
The model fragment with the following object fragments 
The object fragment for the class State and the following constraints 
The integer range from 1 to 1 for the submachine property 
*/
pred mfAllRanges41
{
some o : State | #o.submachine =1
}

/*
The model fragment with the following object fragments 
The object fragment for the class State and the following constraints 
The integer range from 0 to 0 for the entry property 
*/

pred mfAllRanges42
{
some o : State | #o.entry =0
}
/*
The model fragment with the following object fragments 
The object fragment for the class State and the following constraints 
The integer range from 1 to 1 for the entry property 
*/
pred mfAllRanges43
{
some o : State | #o.entry =1
}

/*
The model fragment with the following object fragments 
The object fragment for the class State and the following constraints 
The integer range from 0 to 0 for the exit property 
*/

pred mfAllRanges44
{
some o : State | #o.exit =0
}

/*
The model fragment with the following object fragments 
The object fragment for the class State and the following constraints 
The integer range from 1 to 1 for the exit property 
*/

pred mfAllRanges45
{
some o : State | #o.exit =1
}

/*
The model fragment with the following object fragments 
The object fragment for the class State and the following constraints 
The integer range from 0 to 0 for the doActivity property 
*/

pred mfAllRanges46
{
some o : State | #o.doActivity =0
}
/*
The model fragment with the following object fragments 
The object fragment for the class State and the following constraints 
The integer range from 1 to 1 for the doActivity property 
*/
pred mfAllRanges47
{
some o : State | #o.doActivity =1
}

/*
The model fragment with the following object fragments 
The object fragment for the class State and the following constraints 
The integer range from 0 to 0 for the stateInvariant property 
*/

pred mfAllRanges48
{
some o : State | #o.stateInvariant =0
}

/*
The model fragment with the following object fragments 
The object fragment for the class State and the following constraints 
The integer range from 1 to 1 for the stateInvariant property 
*/
pred mfAllRanges49
{
some o : State | #o.stateInvariant =1
}

/*
The model fragment with the following object fragments 
The object fragment for the class PseudoState and the following constraints 
The integer range from 0 to 0 for the stateMachine property 
*/

pred mfAllRanges50
{
some o : PseudoState | #o.stateMachine =0
}
/*
The model fragment with the following object fragments 
The object fragment for the class PseudoState and the following constraints 
The integer range from 1 to 1 for the stateMachine property 
*/

pred mfAllRanges51
{
some o : PseudoState | #o.stateMachine =1
}

/*
The model fragment with the following object fragments 
The object fragment for the class ConnectionPointReference and the following constraints 
The integer range from 0 to 0 for the state property 
*/

pred mfAllRanges52
{
some o : ConnectionPointReference | #o.state =0
}

/*
The model fragment with the following object fragments 
The object fragment for the class ConnectionPointReference and the following constraints 
The integer range from 1 to 1 for the state property 
*/

pred mfAllRanges53
{
some o : ConnectionPointReference | #o.state =1
}
/*
The model fragment with the following object fragments 
The object fragment for the class ConnectionPointReference and the following constraints 
The integer range from 0 to 0 for the entry property 
*/

pred mfAllRanges54
{
some o : ConnectionPointReference | #o.entry =0
}

/*
The model fragment with the following object fragments 
The object fragment for the class ConnectionPointReference and the following constraints 
The integer range from 1 to 1 for the entry property 
*/

pred mfAllRanges55
{
some o : ConnectionPointReference | #o.entry =1
}

/*
The model fragment with the following object fragments 
The object fragment for the class ConnectionPointReference and the following constraints 
The integer range from 2 to 20000 for the entry property 
*/

pred mfAllRanges56
{
some o : ConnectionPointReference | #o.entry > Parameters.min and #o.entry <= Parameters.max
}

/*
The model fragment with the following object fragments 
The object fragment for the class ConnectionPointReference and the following constraints 
The integer range from 0 to 0 for the exit property 
*/

pred mfAllRanges57
{
some o : ConnectionPointReference | #o.exit =0
}
/*
The model fragment with the following object fragments 
The object fragment for the class ConnectionPointReference and the following constraints 
The integer range from 1 to 1 for the exit property 
*/
pred mfAllRanges58
{
some o : ConnectionPointReference | #o.exit =1
}

/*
The model fragment with the following object fragments 
The object fragment for the class ConnectionPointReference and the following constraints 
The integer range from 2 to 20000 for the exit property 
*/
pred mfAllRanges59
{
some o : ConnectionPointReference | #o.exit > Parameters.min and #o.exit <= Parameters.max
}

/*
pred isConsistent
{
mfAllRanges32
}
run isConsistent  for 20
*/
//run mfAllRanges1 for 20
//No Solution 16929 ms
//run mfAllRanges2 for 20
//Instance Found 26176ms
//run mfAllRanges3 for 20
//Instance Found 23605 ms
//run mfAllRanges4 for 20
//Instance Found 18385 ms
//run mfAllRanges5 for 20
//Instance Found 18733 ms
//run mfAllRanges6 for 20
//Instance Found 20575 ms
//run mfAllRanges7 for 20
//No Instance found 25063 ms
//run mfAllRanges8 for 20
//No Instance found 36079 ms
//run mfAllRanges9 for 20
//Instance found 19464 ms
//run mfAllRanges10 for 20
//Instance found 18700 ms
//run mfAllRanges11 for 20
//Instance Found 20852 ms
//run mfAllRanges12 for 20
//Instance found 21345 ms
//run mfAllRanges13 for 20
//Instance found 20628 ms
//run mfAllRanges14 for 20
//Instance found 73589 ms
//run mfAllRanges15 for 20
//Instance found 77351 ms
//run mfAllRanges16 for 20
//Instance found 49101 ms
//run mfAllRanges17 for 20
//Instance found 20486 ms
//run mfAllRanges18 for 20
//Instance found 20668 ms
//run mfAllRanges19 for 20
//Instance found 20765 ms
//run mfAllRanges20 for 20
//Instance found 19662 ms
//run mfAllRanges21 for 20
//Instance found 20455 ms
//run mfAllRanges22 for 20
//Instance found 23893 ms
//run mfAllRanges23 for 20
//Instance found 48678 ms
//run mfAllRanges24 for 20
//Instance found 20148 ms
//run mfAllRanges25 for 20
//Instance found 21238 ms
//run mfAllRanges26 for 20
//Instance found 20830 ms
//run mfAllRanges27 for 20
//Instance found 22543 ms
//run mfAllRanges28 for 20
//Instance found 20763 ms
//run mfAllRanges29 for 20
//Instance found 22250 ms
//run mfAllRanges30 for 20
//Instance found 20208 ms
//run mfAllRanges31 for 20
//Instance found 20044 ms
//run mfAllRanges32 for 20
//Instance found 21688 ms
//run mfAllRanges33 for 20
//Instance found 21394 ms
//run mfAllRanges34 for 20
//Instance found 44923 ms
//run mfAllRanges35 for 20
//Instance found 54547 ms
//run mfAllRanges36 for 20
//Instance found 24066 ms
//run mfAllRanges37 for 20
//Instance found 20366 ms
//run mfAllRanges38 for 20
//Instance found 20628 ms
//run mfAllRanges39 for 20
//Instance found 23906 ms
//run mfAllRanges40 for 20
//Instance found 20305 ms
//run mfAllRanges41 for 20
//Instance found 20412 ms
//run mfAllRanges42 for 20
//Instance found 21986 ms
//run mfAllRanges43 for 20
//Instance found 21929 ms
//run mfAllRanges44 for 20
//Instance found 20629 ms
//run mfAllRanges45 for 20
//Instance found 54139 ms
//run mfAllRanges46 for 20
//Instance found 23216 ms
//run mfAllRanges47 for 20
//Instance found 35790 ms
//run mfAllRanges48 for 20
//Instance found 20070 ms
//run mfAllRanges49 for 20
//Instance found 17528 ms
//run mfAllRanges50 for 20
//Instance found 17814 ms
//run mfAllRanges51 for 20
//Instance Found 38950 ms
//run mfAllRanges52 for 20
//Instance found 18010 ms
//run mfAllRanges53 for 20
//Instance found 17218 ms
//run mfAllRanges54 for 20
//Instance found 18041 ms
//run mfAllRanges55 for 20
//Instance found 24172 ms
//run mfAllRanges56 for 20
//Instance found 38461 ms
//run mfAllRanges57 for 20
//run mfAllRanges58 for 20
//Instance found 35465 ms
