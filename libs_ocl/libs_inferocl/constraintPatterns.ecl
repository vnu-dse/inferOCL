%--------------------------------------------------------------------------------------
% Date: 2014.02.07: Encoding constraint patterns in eclipse clp
%--------------------------------------------------------------------------------------

constraintPatternIndex("attrRestriction", 1).
constraintPatternIndex("collectRestriction", 2).
constraintPatternIndex("logicConnective", 3).

% The helper defines the context as a collection
ocl_navigationN(Context, Result) :-
  ( Context = [Instances, Vars, ClassName], string(ClassName) -> 
    ocl_allInstances(Instances, ClassName, Collection),
    Result = [Instances, Vars, ClassName, Collection]
  ; Context = [Instances, Vars, ClassName, Self, Path], is_list(Path) -> 
    ( foreach(Role, Path),
      fromto([Self], InObjs, OutObjs, LastRefObjs),
      fromto(ClassName, InClsName, OutClsName, LastClsName),
      param(Instances) do
      is_predicate(roleType/3),
      roleType(Assoc, SrcRole, InClsName),
      roleType(Assoc, Role, OutClsName),
      (InClsName \= OutClsName; Role \= SrcRole),
      %is_predicate(roleMax/3),
      %roleMax(Assoc, Role, 1),
      ocl_navigation(Instances, Assoc, SrcRole, Role, InObjs, OutObjs1),
      ocl_set_asSet(OutObjs1, OutObjs)
    ),
    Result = [Instances, Vars, LastClsName, LastRefObjs]
    %is_predicate(roleType/3),
    %roleType(Assoc, SrcRole, LastClsName),
    %roleType(Assoc, Role, DstClass),
    %(LastClsName \= DstClass; Role \= SrcRole),
    %ocl_navigation(Instances, Assoc, SrcRole, Role, LastRefObj, TmpCollection),
    %ocl_set_asSet(TmpCollection, Collection),
    %Result = [Instances, Vars, DstClass, Collection]
  ; Context = [Instances, Vars, ClassName, [Self] ] -> Result = [Instances, Vars, ClassName, [Self]]
  ; Context = [Instances, Vars, ClassName, Self], compound(Self) -> Result = [Instances, Vars, ClassName, [Self]]
  ).

% OperatorName: {">=", "<=", "=", "in", "between"}
attrRestriction(Context, OpName, AttrName, Value, Result) :-
  ocl_navigationN(Context, [Instances, _, ClassName, Collection]),
%  ocl_allInstances(Instances, ClassName, ObjectList),
  ( OpName == "in" -> 
    ( foreach(Self, Collection),
      fromto(1, In, Out, Result),
      param(Instances, ClassName, AttrName, Value) do
      ocl_attributeCall(Instances, ClassName, AttrName, Self, AttrValue),
      ( member(AttrValue, Value) -> TmpRet = 1; TmpRet = 0 ),
      ic:and(TmpRet, In, Out)
    )
  ; OpName == "="  -> 
    ( foreach(Self, Collection),
      fromto(1, In, Out, Result),
      param(Instances, ClassName, AttrName, Value) do
      ocl_attributeCall(Instances, ClassName, AttrName, Self, AttrValue),
      ( AttrValue == Value -> TmpRet = 1; TmpRet = 0 ),
      ic:and(TmpRet, In, Out)
    )
  ; OpName == ">=", attType(ClassName, AttrName ,"Integer") ->
    ( foreach(Self, Collection),
      fromto(1, In, Out, Result),
      param(Instances, ClassName, AttrName, Value) do
      ocl_attributeCall(Instances, ClassName, AttrName, Self, AttrValue),
      #>=(AttrValue, Value, TmpRet),
      ic:and(TmpRet, In, Out)
    )
  ; OpName == "<=", attType(ClassName, AttrName ,"Integer") -> 
    ( foreach(Self, Collection),
      fromto(1, In, Out, Result),
      param(Instances, ClassName, AttrName, Value) do
      ocl_attributeCall(Instances, ClassName, AttrName, Self, AttrValue),
      #=<(AttrValue, Value, TmpRet),
      ic:and(TmpRet, In, Out)
    )
  ; OpName == "between", attType(ClassName, AttrName ,"Integer") ->
    Value = [Left, Right], 
    number(Left), number(Right),
    ( foreach(Self, Collection),
      fromto(1, In, Out, Result),
      param(Instances, ClassName, AttrName, Left, Right) do
      ocl_attributeCall(Instances, ClassName, AttrName, Self, AttrValue),
      #>=(AttrValue, Left, TmpRet1),
      #=<(AttrValue, Right, TmpRet2),
      ic:and(TmpRet1, TmpRet2, TmpRet),
      ic:and(TmpRet, In, Out)
    )

  ).

% OperatorName: {"and","or","ifelse"}
% Each patternInstance = [PatternPredicate, ParaString]
logicConnective(Context, OpName, PatternInstanceList, Result) :-
  ocl_navigationN(Context, [Instances, Vars, ClassName, Collection]),
  ( OpName == "and"    ->
    ( % TODO: Here, we consider only the case Vars = [] for the child patterns
      ( foreach(PatternInstance, PatternInstanceList),
        fromto(1, In, Out, Result),
        param(Instances, Vars, ClassName) do
        PatternInstance = [ PatternPredicate, ParaString ],
        ParaString = [PatternContext | _],
        PatternContext = [Instances, Vars, ClassName],
        Vars = [], 
        ( apply(PatternPredicate, ParaString) -> TmpRet = 1; TmpRet = 0 ),
        ic:and(TmpRet, In, Out) 
      )
    ; % TODO: Here, we consider only the case: the Context of each child pattern = []
      ( foreach(Self, Collection),
        fromto(1, InRet, OutRet, Result),  
        param(Instances, Vars, ClassName, PatternInstanceList) do
        ( foreach(PatternInstance, PatternInstanceList),
          fromto(InRet, InPat, OutPat, OutRet),
          param(Instances, Vars, ClassName, Self) do
          PatternInstance = [PatternPredicate, [[] | ParaString] ],
          PatternPara = [ [Instances, Vars, ClassName, Self] | ParaString ],
          ( apply(PatternPredicate, PatternPara) -> TmpRet = 1; TmpRet = 0 ),
          ic:and(TmpRet, InPat, OutPat)
        )
      )
    )
  ; OpName == "or"     -> 
    ( ( foreach(PatternInstance, PatternInstanceList),
        fromto(0, In, Out, Result),
        param(Instances, Vars, ClassName) do
        PatternInstance = [ PatternPredicate, ParaString ],
        ParaString = [PatternContext | _],
        PatternContext = [Instances, Vars, ClassName],
        Vars = [],
        ( apply(PatternPredicate, ParaString) -> TmpRet = 1; TmpRet = 0 ),
        ic:or(TmpRet, In, Out) 
      )
    ; % TODO: Here, we consider only the case: the Context of each pattern = []
      ( foreach(Self, Collection),
        fromto(1, InRet, OutRet, Result),  
        param(Instances, Vars, ClassName, PatternInstanceList) do
        ( foreach(PatternInstance, PatternInstanceList),
          fromto(InRet, InPat, OutPat, OutRet),
          param(Instances, Vars, ClassName, Self) do
          PatternInstance = [PatternPredicate, [[] | ParaString] ],
          PatternPara = [ [Instances, Vars, ClassName, Self] | ParaString ],
          ( apply(PatternPredicate, PatternPara) -> TmpRet = 1; TmpRet = 0 ),
          ic:or(TmpRet, InPat, OutPat)
        ),
        ic:and(RetPat, InRet, OutRet)
      )
    )
  ; % TODO: Here, we consider only the case: the Context of each pattern = []
    OpName == "ifelse", length(PatternInstanceList, 3) ->  
    ( foreach(Self, Collection),
      fromto(1, In, Out, Result),
      param(Instances, Vars, ClassName, PatternInstanceList) do
      PatternInstanceList  = [PatternInstance_If, PatternInstance_Then, PatternInstance_Else],
      PatternInstance_If   = [PatternPredicate_If,   [ [] | ParaString_If  ] ],
      PatternInstance_Then = [PatternPredicate_Then, [ [] | ParaString_Then] ],
      PatternInstance_Else = [PatternPredicate_Else, [ [] | ParaString_Else] ],
      ParaPattern_If   = [ [Instances, Vars, ClassName, Self] | ParaString_If  ],
      ParaPattern_Then = [ [Instances, Vars, ClassName, Self] | ParaString_Then],
      ParaPattern_Else = [ [Instances, Vars, ClassName, Self] | ParaString_Else],
      ( apply(PatternPredicate_If, ParaPattern_If) -> 
        ( apply(PatternPredicate_Then, ParaPattern_Then) -> TmpRet = 1; TmpRet = 0 )
      ; ( apply(PatternPredicate_Else, ParaPattern_Else) -> TmpRet = 1; TmpRet = 0 )
      ),
      ic:and(TmpRet, In, Out)
    )
  ).

% OpName: {">=", "<=", "between, "includesAll", "forAll", "isUnique"}
collectRestriction(Context, PatternInstanceList, OpName, Value, Result) :-
  ocl_navigationN(Context, [Instances, Vars, ClassName, Collection]),
  Context1 = [Instances, Vars, ClassName, Collection],
  ( OpName == ">=", number(Value)  ->     
    collectRestriction_select(Context1, PatternInstanceList, RestrictedColl),    
    length(RestrictedColl, Size),
    #>=(Size, Value, Result)
  ; OpName == "<=", number(Value)  -> 
    collectRestriction_select(Context1, PatternInstanceList, RestrictedColl),    
    length(RestrictedColl, Size), 
    #=<(Size, Value, Result)
  ; OpName == "between", Value = [Left, Right], number(Left), number(Right) -> 
    collectRestriction_select(Context1, PatternInstanceList, RestrictedColl),    
    length(RestrictedColl, Size),
    #>=(Size, Left, TmpRet1), 
    #=<(Size, Right, TmpRet2), 
    ic:and(TmpRet1, TmpRet2, Result)
  ; OpName == ">=", is_list(Value) -> 
    collectRestriction_select(Context1, PatternInstanceList, RestrictedColl),    
    length(RestrictedColl, Size),
    append([Instances0, Vars0, ClassName0, Self0], _, Context),
    append(Path, [AttrName], Value),
    ( Path = [] -> RefObj = Self0
    ; ocl_navigationN( [Instances0, Vars0, ClassName0, Self0, Path], [ _, _, _, [RefObj] ])
    ),
    ocl_attributeCall(Instances0,ClassName0, AttrName, RefObj, AttrValue),
    number(AttrValue),
    #>=(Size, AttrValue, Result)       
  ; OpName == "<=", is_list(Value) -> 
    collectRestriction_select(Context1, PatternInstanceList, RestrictedColl), 
    length(RestrictedColl, Size), 
    append(Path, [AttrName], Value),
    append([Instances0, Vars0, ClassName0, Self0], _, Context),
    ( Path = [] -> RefObj = Self0
    ; ocl_navigationN( [Instances0, Vars0, ClassName0, Self0, Path], [ _, _, _, [RefObj] ])
    ), 
    ocl_attributeCall(Instances0,ClassName0, AttrName, RefObj, AttrValue),
    number(AttrValue),
    #=<(Size, AttrValue, Result)       

  ; OpName == "includesAll", is_list(Value), Value \= [] -> 
    collectRestriction_select(Context1, PatternInstanceList, RestrictedColl), 
    append([Instances0, Vars0, ClassName0, Self0], _, Context), 
    ocl_navigationN( [Instances0, Vars0, ClassName0, Self0, Value], [ _, _, _, RefColl ]), 
    ocl_col_includesAll(RestrictedColl, RefColl, Result)

  ; OpName == "forAll" -> 
    collectRestriction_select(Context1, PatternInstanceList, RestrictedColl),
    ( foreach(Self, RestrictedColl),
      fromto(1, InRet, OutRet, Result),
      param(Instances, Vars, ClassName, Value) do 
      Value = [PatternPredicate, [CtxPath | ParaString] ], 
      ( CtxPath = [] -> Ctx = [Instances, Vars, ClassName, Self]
      ; Ctx = [Instances, Vars, ClassName, Self, CtxPath]
      ),
      PatternPara = [ Ctx | ParaString ], 
      ( apply(PatternPredicate, PatternPara) -> Tmp = 1; Tmp = 0 ),
      ic:and(Tmp, InRet, OutRet)
    )

  ; OpName == "isUnique" -> 
    collectRestriction_select(Context1, PatternInstanceList, RestrictedColl),
    Value = [AttrList, RoleList],      
    ( foreach(Self, RestrictedColl),
      fromto([],In, Out, TupleValueList),
      param(Instances, ClassName, AttrList, RoleList) do
      ( foreach(Attr, AttrList),
        fromto([],InAttr,OutAttr,AttrValueList),
        param(Instances, ClassName, Self ) do
        ocl_attributeCall(Instances,ClassName, Attr, Self, AttrValue),
        OutAttr = [AttrValue | InAttr]
      ),
      ( foreach(Role, RoleList),
        fromto([], InRole, OutRole, RefObjList),
        param(Instances, ClassName, Self) do
        is_predicate(roleType/3),
  	roleType(Assoc, SrcRole, ClassName),
  	roleType(Assoc, Role, DstClass),
        (ClassName \= DstClass; Role \= SrcRole),
        is_predicate(roleMax/3),
        roleMax(Assoc, Role, 1),
        ocl_navigation(Instances, Assoc, SrcRole, Role, Self, RefObj),
        OutRole = [RefObj | InRole]
      ),
      Out = [ [AttrValueList, RefObjList] | In]
    ),
    list_is_unique(TupleValueList, Result) 
  ).

collectRestriction_select(Context, PatternInstanceList, Result) :-
  Context = [Instances, Vars, ClassName, Collection], %writeln(ClassName), writeln(Collection),
  ( foreach(Self, Collection),
    fromto([], InColl, OutColl, Result),
    param(Instances, Vars, ClassName, PatternInstanceList) do    
    ( foreach(PatternInstance, PatternInstanceList),
      fromto(1, InPat, OutPat, IsSelected),
      param(Instances, Vars, ClassName, Self) do
      PatternInstance = [PatternPredicate, [ Path | ParaString] ],
      ( Path = [] -> Context1 = [Instances, Vars, ClassName, Self]
      ; Context1 = [Instances, Vars, ClassName, Self, Path]
      ),
      PatternPara = [ Context1 | ParaString ],
      ( apply(PatternPredicate, PatternPara) -> Tmp = 1; Tmp = 0 ),
      ic:and(Tmp, InPat, OutPat)
    ),
    ( IsSelected = 1 -> OutColl = [Self | InColl]; OutColl = InColl )
  ).
