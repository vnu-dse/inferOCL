%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%              A lightweight ocl invariant solver                      %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Author: Duc-Hanh Dang (duc-hanh.dang@inria.fr)
% (c) 2013
% See "Lightweight OCL Invariant Reasoning in Model Finding"
%     "Automating Inference of OCL Business Rules from User Scenarios", Apsec2013
%     "InferOCL: An Automated Inference of OCL Domain Restriction from Scenarios"
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% updated versions:
%
% 2013.10.31: extending CHR, to change labeling strategy
%
% patternIndex( "uniqueAttr",  		1).
% patternIndex( "intervalInv", 		2).
% patternIndex( "cardInv",     		3).
% patternIndex( "nonSelfInc",  		4).
% patternIndex( "attrRel",     		5).
% patternIndex( "maxCard",     		6).
% patternIndex( "requiredInclusion",	7).
% patternIndex( "restrictedAssoc",	8).

:- lib(ic).
:- lib(ech).
:- lib(ordset).
:- lib(var_name).
:- handler inv.

:- option(already_in_store, off). 
:- option(check_guard_bindings, off).
:- option(default_chr_priority,6).

:- constraints 
	labelingAttr/5,
	labelingCard/4.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                           INFERENCE RULES                            % 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%% uniqueAttr %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%LocalPara = [X_Class, X_Attr]

attr_uniqueAttr_rule1	::= 	labelingAttr(Snapshot, AttrVars, Pat, Para, 1)
				==>	patternIndex("uniqueAttr",Pat),
					attr_uniqueAttr_rule1(Snapshot, Para, AllAttrs)
				| ic:alldifferent(AllAttrs), AttrVars = ["uniqueAttr", Para, 1, AllAttrs].

attr_uniqueAttr_rule2	::= 	labelingAttr(Snapshot, AttrVars, Pat, Para, 0)
				==>	patternIndex("uniqueAttr",Pat),
					attr_uniqueAttr_rule2(Snapshot, Para, AllAttrs)
				| AttrVars = ["uniqueAttr", Para, 0, AllAttrs].

card_uniqueAttr_rule1	::= 	labelingCard(CardVars, Pat, Para, 0)
				==>	patternIndex("uniqueAttr",Pat),
					card_uniqueAttr_rule1(CardVars, Para, SizeClass)
				| SizeClass #> 1.

%%%%%%%%%%%%%%%%%%%%%%%%%% intervalInv %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%LocalPara = [X_Class, X_Attr, X_Intervals],

attr_intervalInv	::= 	labelingAttr(Snapshot, AttrVars, Pat, Para, Ret)
				==>	patternIndex("intervalInv",Pat),
					attr_intervalInv(Snapshot, Para, AllAttrs)
				| AttrVars = ["intervalInv", Para, Ret, AllAttrs].

card_intervalInv_rule1	::= 	labelingCard(CardVars, Pat1, Para1, 1),
				labelingCard(CardVars, Pat2, Para2, 0)
				==>	patternIndex("intervalInv",Pat1),
					patternIndex("maxCard",Pat2),
					card_intervalInv_rule1(CardVars, Para1, Para2, SizeAssoc, SizeClsB, Min)
				| SizeAssoc #> Min, SizeClsB #> Min.

%%%%%%%%%%%%%%%%%%%%%%%%%%% cardInv %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%LocalPara = [X_Class, X_Assoc, X_Role, Role2, X_Intervals, X_Class2],

attr_cardInv		::= 	labelingAttr(Snapshot, AttrVars, Pat, Para, Ret)
				==>	patternIndex("cardInv",Pat),
					attr_cardInv(Snapshot, Para, AllAttrs)
				| AttrVars = ["cardInv", Para, Ret, AllAttrs].

card_cardInv_rule1	::=	labelingCard(CardVars, Pat, Para, 1)
				==>	patternIndex("cardInv",Pat),
					card_cardInv_rule1(CardVars,Para,SizeClass,SizeClass2,SizeAssoc,Min,Max)
				| (SizeClass #= 0 or SizeClass2 #>= Min), SizeAssoc #>= Min * SizeClass, SizeAssoc #=< Max * SizeClass.

card_cardInv_rule2	::=	labelingCard(CardVars, Pat, Para, 0)
				==>	patternIndex("cardInv",Pat),
					card_cardInv_rule1(CardVars,Para,SizeClass,SizeClass2,SizeAssoc,Min,Max),
					Min #= 0
				| SizeClass #> 0, SizeClass2 #> Max, SizeAssoc #> Max.

%%%%%%%%%%%%%%%%%%%%%%%% requiredInclusion %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%LocalPara = [X_Class,Assoc,X_RoleB,Role2,AssocR,X_Required,Dependent,ClsB]

attr_requiredInclusion		::= 	labelingAttr(Snapshot, AttrVars, Pat, Para, Ret)
					==>	patternIndex("requiredInclusion",Pat),
						attr_requiredInclusion(Snapshot, Para, AllAttrs)
					| AttrVars = ["requiredInclusion", Para, Ret, AllAttrs].

card_requiredInclusion_rule1	::=	labelingCard(CardVars, Pat, Para, 0)
					==>	patternIndex("requiredInclusion",Pat),
						card_requiredInclusion_rule1(CardVars,Para,SizeXClass,SizeAssoc,SizeAssocR,SizeClsB)
					| SizeXClass #> 0, SizeAssoc #> 0, SizeAssocR #> 0, SizeClsB #> 1, (SizeXClass #= 1 => SizeClsB #> SizeAssoc).

card_requiredInclusion_rule2	::=	labelingCard(CardVars, Pat1, Para1, 0),
					labelingCard(CardVars, Pat2, Para2, 1)
					==>	patternIndex("requiredInclusion",Pat1),
						patternIndex("cardInv",Pat2),
						card_requiredInclusion_rule2(CardVars,Para1,Para2,SizeClsB,Min)
					| SizeClsB #> Min.

%%%%%%%%%%%%%%%%%%%%%%%% restrictedAssoc %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%LocalPara = [X_ClassA,X_Cond,X_RoleA,X_RoleB,X_AssocBC,X_RoleC,RoleCB,ClsB]

attr_restrictedAssoc_rule1	::= 	labelingAttr(Snapshot, AttrVars, Pat, Para, Ret)
					==>	patternIndex("restrictedAssoc",Pat),
						attr_restrictedAssoc_rule1(Snapshot, Para, AllAttrs)
					| AttrVars = ["restrictedAssoc", Para, Ret, AllAttrs].

card_restrictedAssoc_rule1	::=	labelingCard(CardVars, Pat, Para, 0)
					==>	patternIndex("restrictedAssoc",Pat),
						card_restrictedAssoc_rule1(CardVars,Para,SizeXClassA,SizeAssocBC)
					| SizeAssocBC #> 0, SizeXClassA #>0.

%%%%%%%%%%%%%%%%%%%%%%%% maxCard %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%LocalPara = [X_Class,X_MaxCard,X_Assoc,X_Role,Role2,ClsB]

attr_maxCard_rule1		::= 	labelingAttr(Snapshot, AttrVars, Pat, Para, Ret)
					==>	patternIndex("maxCard",Pat),
						attr_maxCard_rule1(Snapshot, Para, AllAttrs)
					| AttrVars = ["maxCard", Para, Ret, AllAttrs].

attr_maxCard_rule2		::= 	labelingAttr(Snapshot, AttrVars, Pat, Para, 0)
					==>	patternIndex("maxCard",Pat),
						attr_maxCard_rule2(Snapshot, Para, MinAttr, SizeAssoc, SizeClsB)
					| MinAttr #< SizeAssoc, MinAttr #< SizeClsB.

card_maxCard_rule1		::=	labelingCard(CardVars, Pat, Para, 0)
					==>	patternIndex("maxCard",Pat),
						card_maxCard_rule1(CardVars,Para,SizeAssoc, SizeClsB)
					| SizeAssoc #> 1, SizeClsB #> 1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%% all %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

attr_labeling		::=	labelingAttr(Snapshot, AttrVars, Pat, Para, R) <=> ground(Snapshot) | true.

card_labeling		::= 	labelingCard(CardVars, Pat, Para, R) <=> ground(CardVars) | true.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                           HELPERS                                    %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

attr_uniqueAttr_rule1(Snapshot, Para, AllAttrs) :-
	Para = [X_Class, X_Attr],
	index(X_Class,IdxClass),
	attIndex(X_Class,X_Attr,IdxAttr),
	nth1(IdxClass, Snapshot, AllAttrsXClass),
	getAttrs(AllAttrsXClass, IdxAttr, AllAttrs).
	%nth1(1,AllAttrs,Attr1),
	%nth1(2,AllAttrs,Attr2),
	%Attr1 \= Attr2.
	%ic:alldifferent(AllAttrs), writeln("XX"),writeln(AllAttrs).

attr_uniqueAttr_rule2(Snapshot, Para, AllAttrs) :-
	Para = [X_Class, X_Attr],
	index(X_Class,IdxClass),
	attIndex(X_Class,X_Attr,IdxAttr),
	nth1(IdxClass, Snapshot, AllAttrsXClass),
	getAttrs(AllAttrsXClass, IdxAttr, AllAttrs).

card_uniqueAttr_rule1(CardVars, Para, SizeClass) :-
	Para = [X_Class, _],
	index(X_Class,IdxClass),
	nth1(IdxClass,CardVars,SizeClass).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

attr_intervalInv(Snapshot, Para, AllAttrs) :-
	Para = [X_Class, X_Attr, _],
	index(X_Class,IdxXClass),
	attIndex(X_Class,X_Attr,IdxAttr),
	nth1(IdxXClass, Snapshot, AllAttrs1),
	getAttrs(AllAttrs1,IdxAttr,AllAttrs).

card_intervalInv_rule1(CardVars, Para1, Para2, SizeAssoc, SizeClsB, Min) :-
	Para1 = [XClass,XAttr,[clsInterval(_,Min0,_)]],
	Para2 = [XClass,XAttr,XAssoc,_,_,ClsB],
	index(XAssoc,IdxAssoc),
	nth1(IdxAssoc,CardVars,SizeAssoc),
	index(ClsB,IdxClsB),
	nth1(IdxClsB,CardVars,SizeClsB),
	Min is Min0 + 1.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

attr_cardInv(Snapshot, Para, AllAttrs) :-
	Para = [_, X_Assoc, _, _, _, _],
	index(X_Assoc,IdxAssoc),
	nth1(IdxAssoc,Snapshot,PAssoc),
	flatten([PAssoc],AllAttrs).

card_cardInv_rule1(CardVars,Para,SizeClass,SizeClass2,SizeAssoc,Min,Max) :-
	Para = [XClass, XAssoc, _, _, [clsInterval(_,Min0,Max0)], XClass2],
	Min is Min0 + 1,
	Max is Max0 - 1,
	index(XClass,IdxClass),
	index(XClass2,IdxClass2),
	index(XAssoc,IdxAssoc),
	nth1(IdxClass,CardVars,SizeClass),
	nth1(IdxClass2,CardVars,SizeClass2),
	nth1(IdxAssoc,CardVars,SizeAssoc).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

attr_restrictedAssoc_rule1(Snapshot, Para, AllAttrs) :-
	Para = [X_ClassA,X_Cond,_,_,X_AssocBC,_,_,_],
	concat_strings("AssocCls_", X_ClassA , AssocX_ClassA),
	index(X_ClassA,IdxX_ClassA),
	attIndex(X_ClassA,X_Cond,IdxX_Cond),
	nth1(IdxX_ClassA, Snapshot, AllAttrX_ClassA),
	getAttrs(AllAttrX_ClassA, IdxX_Cond, AttrsX_Cond),
	index(AssocX_ClassA,IdxAssocX_ClassA),
	nth1(IdxAssocX_ClassA,Snapshot,PX_ClassA),
	index(X_AssocBC,IdxX_AssocBC),
	nth1(IdxX_AssocBC,Snapshot,PX_AssocBC),
	AllAttrs1 = [AttrsX_Cond, PX_ClassA, PX_AssocBC],
	flatten(AllAttrs1,AllAttrs).

%LocalPara = [X_ClassA,X_Cond,X_RoleA,X_RoleB,X_AssocBC,X_RoleC,RoleCB,ClsB]
card_restrictedAssoc_rule1(CardVars,Para,SizeXClassA,SizeAssocBC) :-
	Para = [XClassA,_,_,_,XAssocBC,_,_,_],
	index(XClassA,IdxXClassA),
	index(XAssocBC,IdxXAssocBC),
	nth1(IdxXClassA,CardVars,SizeXClassA),
	nth1(IdxXAssocBC,CardVars,SizeAssocBC).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

attr_requiredInclusion(Snapshot, Para, AllAttrs) :-
	Para = [_,Assoc,_,_,AssocR,_,_,_],
	index(Assoc,IdxAssoc),
	nth1(IdxAssoc,Snapshot,PAssoc),
	index(AssocR,IdxAssocR),
	nth1(IdxAssocR,Snapshot,PAssocR),
	AllAttrs1 = [PAssoc,PAssocR],	
	flatten(AllAttrs1,AllAttrs).

card_requiredInclusion_rule1(CardVars,Para,SizeXClass,SizeAssoc,SizeAssocR,SizeClsB) :-
	Para = [XClass,Assoc,_,_,AssocR,_,_,ClsB],
	index(XClass,IdxXClass),
	index(Assoc,IdxAssoc),
	index(AssocR,IdxAssocR),
	index(ClsB,IdxClsB),
	nth1(IdxXClass,CardVars,SizeXClass),
	nth1(IdxAssoc,CardVars,SizeAssoc),
	nth1(IdxAssocR,CardVars,SizeAssocR),
	nth1(IdxClsB,CardVars,SizeClsB).	

card_requiredInclusion_rule2(CardVars,Para1,Para2,SizeClsB,Min) :-
	Para1 = [XClass,Assoc,_,_,_,_,_,ClsB],	
	Para2 = [XClass,Assoc, _, _, [clsInterval(_,Min0,_)], ClsB],
	Min is Min0 + 1,
	index(ClsB,IdxClsB),	
	nth1(IdxClsB,CardVars,SizeClsB).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%LocalPara = [X_Class,X_MaxCard,X_Assoc,X_Role,Role2,ClsB]

attr_maxCard_rule1(Snapshot, Para, AllAttrs) :-
	Para = [XClass,XMaxCard,XAssoc,_,_,_],
	index(XClass,IdxXClass),
	attIndex(XClass,XMaxCard,IdxXMaxCard),
	nth1(IdxXClass, Snapshot, AllAttrXClass),
	getAttrs(AllAttrXClass, IdxXMaxCard, AttrsXMaxCard),
	index(XAssoc,IdxXAssoc),
	nth1(IdxXAssoc,Snapshot,PXAssoc),
	AllAttrs1 = [AttrsXMaxCard,PXAssoc],	
	flatten(AllAttrs1,AllAttrs).

attr_maxCard_rule2(Snapshot, Para, MinAttr, SizeAssoc, SizeClsB) :-
	Para = [XClass,XMaxCard,XAssoc,_,_,ClsB],
	index(XAssoc,IdxXAssoc),
	nth1(IdxXAssoc,Snapshot,PXAssoc),
	length(PXAssoc, SizeAssoc),
	index(ClsB,IdxClsB),	
	nth1(IdxClsB,Snapshot,OClsB),
	length(OClsB, SizeClsB),
	index(XClass,IdxXClass),
	nth1(IdxXClass, Snapshot, AllAttrXClass),
	attIndex(XClass,XMaxCard,IdxXMaxCard),
	getAttrs(AllAttrXClass, IdxXMaxCard, AttrsXMaxCard),
	ic:min(AttrsXMaxCard, MinAttr).
	
card_maxCard_rule1(CardVars,Para,SizeAssoc,SizeClsB) :-
	Para = [_,_,XAssoc,_,_,ClsB],
	index(XAssoc,IdxAssoc),
	nth1(IdxAssoc,CardVars,SizeAssoc),
	index(ClsB,IdxClsB),	
	nth1(IdxClsB,CardVars,SizeClsB).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

getAttrs(AllAttrs, IdxAttr, Attrs) :-
	foreach(Obj, AllAttrs),
	fromto([], InAttrs, OutAttrs, Attrs),
	param(IdxAttr)
	do
		nth1(IdxAttr, Obj, Attr),
		append(InAttrs, [Attr], OutAttrs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                           HELPERS: The order for labeling            %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

sortAttrVars([],[]).

sortAttrVars(AttrVarsList,OrdAttrVarsList) :-
	AttrVarsList = [AttrVars | AttrVarsList0],
	( foreach(AttrVars0,AttrVarsList0),
	  fromto([AttrVars], In, Out, AttrVarsList1)
	  do
		insertAttrVars(AttrVars0, In, Out)
	),
	subtract(AttrVarsList, AttrVarsList1, AttrVarsList2),
	sortAttrVars(AttrVarsList2,OrdAttrVarsList2),
	append(AttrVarsList1,OrdAttrVarsList2, OrdAttrVarsList).

insertAttrVars(AttrVars, [], [AttrVars]).

insertAttrVars(AttrVars, AttrVarsList, Ret) :-
	AttrVars = [_,_,_,Attrs],
	getVarNameSet(Attrs,VarNameSet),
	( foreach(AttrVars0, AttrVarsList),
	  fromto([], In, Out, Ret),
	  fromto(AttrVarsList, In1, Out1, _),
	  fromto(0,InAdd,OutAdd,_),
	  param(AttrVars, VarNameSet)
	  do
		In1 = [AttrVars0 | Out1],
		AttrVars0 = [_,_,_,Attrs0],
		getVarNameSet(Attrs0, VarNameSet0),
	  	( ordset:ord_intersect(VarNameSet, VarNameSet0)
		  -> ( 	foreach(Attrs1, Out1),
			fromto(0,In2,Out2,Ret2),
			param(VarNameSet)
			do
				getVarNameSet(Attrs1, VarNameSet1),
				( ordset:ord_subset(VarNameSet1, VarNameSet)
				  -> Out2 = 1;
				  Out2 = In2
				)
		     ),	
		     (  ( Ret2 #= 0, InAdd #= 0 ) 
                        -> append(In, [AttrVars0,AttrVars], Out), OutAdd = 1;
			append(In, [AttrVars0], Out), OutAdd = InAdd
                     );
	          append(In, [AttrVars0], Out), OutAdd = InAdd
		)
	).

getVarNameSet(Attrs,VarNameSet) :-
	( foreach(Attr,Attrs),
	  fromto([],In,Out,VarNameList)
	  do
		term_string(Attr,VarName),
		Out = [VarName | In]
	),
	ordset:list_to_ord_set(VarNameList,VarNameSet).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

findExamples(N, SnapshotList) :-
	setval(count,0),
	store_create(Store),
	(
		findExample(Snapshot),
		incval(count),	
		getval(count,X),
		store_inc(Store, Snapshot),
		( (X #= N) -> !;
		  fail
		),
		stored_keys(Store, SnapshotList)
	;
		stored_keys(Store, SnapshotList)
	).
