%--------------------------------------------------------------------------------------
% Load the OCL and UML libs
% Date: 2013.10.22: add the ocl CHR - inv_pattern.ecl
% Date: 2013.10.15: get classes and links for labeling
% Date: 2013.11.18: update apply_all(SOK,[],...)
% Date: 2014.01.08: add OneReferee pattern
% Date: 2014.01.16: add CountObject1 pattern
% Date: 2014.02.06: add the file ocl_handler.ecl
%--------------------------------------------------------------------------------------
:-lib(ic).
:-lib(ic_global).
:-lib(ic_global_gac).
:-lib(apply).
:-lib(apply_macros).
:-lib(lists).
:-lib(ech).
:-use_module("ocl_basicops.ecl").
:-use_module("ocl_collections.ecl").
:-use_module("ocl_iterators.ecl").
%:-use_module("ocl_handler.ecl").
:-use_module("uml_basic.ecl").
:-use_module("inv_pattern.ecl").
:-use_module("string_exp.ecl").
:-use_module("constraintPatterns.ecl").
:-use_module("constraintPatternHandler.ecl").
%--------------------------------------------------------------------------------------
%--Applying UniqueAttr Pattern---------------------------------------------------------
%--------------------------------------------------------------------------------------
apply_uniqueAttr(SOK, SNOK, Para):-
% Para = [X_Class, X_Attr],
  getLocalPara_uniqueAttr(Para,LocalPara),
  %--Ensuring the invariant accepts SOK----------
  ( foreach(SOk, SOK),
    param(LocalPara)
    do
      uniqueAttr(SOk, LocalPara, 1)
  ),
  %--Ensuring the invariant rejects SNOK---------
  ( foreach(SNok, SNOK),
    param(LocalPara)
    do
      uniqueAttr(SNok, LocalPara, 0)
  ).
%--Get the LocalPara-----------------------------
getLocalPara_uniqueAttr(Para,LocalPara):-
  Para = [X_Class, X_Attr],
  index(X_Class,_),
  attIndex(X_Class, X_Attr, _),
  %attType(X_Class, X_Attr,"Integer"),
  LocalPara = Para.
%--Writing the UniqueAttr template---------------
write_uniqueAttr(Para, Inv) :-
  Para = [X_Class, X_Attr],
  sprintf(OCLInv,"context %w inv unique_%w:....%w::forAll(p1,p2 | p1 <> p2 implies p1.%w<>p2.%w)",
          [X_Class,X_Attr,X_Class,X_Attr,X_Attr]),
  sprintf(ParaStr,"['%w','%w']",[X_Class,X_Attr]),
  Inv = [ParaStr, OCLInv].
%--Encoding the OCL UniqueAttr template----------
nallInstances1uniqueAttr(Instances, [Para], Result):-
        Para = [X_Class, _],
	ocl_allInstances(Instances, X_Class, Result).
nallInstances2uniqueAttr(Instances, Vars, Result):-
        append(_, [Para], Vars),
        Para = [X_Class, _],
	ocl_allInstances(Instances, X_Class, Result).
nVariable3uniqueAttr(_, Vars, Result):-
	ocl_variable(Vars,2,Result).
nVariable4uniqueAttr(_, Vars, Result):-
	ocl_variable(Vars,1,Result).
nnot_equals5uniqueAttr(Instances, Vars, Result):-
        append(_, [Para], Vars),
        Para = [X_Class, _],
	nVariable3uniqueAttr(Instances, Vars, Obj1),
	nVariable4uniqueAttr(Instances, Vars, Obj2),
	ocl_obj_not_equals(Instances, Obj1, X_Class, Obj2, X_Class, Result).
nVariable6uniqueAttr(_, Vars, Result):-
	ocl_variable(Vars,2,Result).
nAttribute7uniqueAttr(Instances, Vars, Result):-
        append(_, [Para], Vars),
        Para = [X_Class, X_Attr],
	nVariable6uniqueAttr(Instances, Vars, Object),
	ocl_attributeCall(Instances,X_Class,X_Attr, Object, Result).
nVariable8uniqueAttr(_, Vars, Result):-
	ocl_variable(Vars,1,Result).
nAttribute9uniqueAttr(Instances, Vars, Result):-
        append(_, [Para], Vars),
        Para = [X_Class, X_Attr],
	nVariable8uniqueAttr(Instances, Vars, Object),
	ocl_attributeCall(Instances,X_Class,X_Attr, Object, Result).
nnot_equals10uniqueAttr(Instances, Vars, Result):-
	append(_, [Para], Vars),
        Para = [X_Class, X_Attr],
	( attType(X_Class, X_Attr,"Integer") ->   
	  ocl_int_not_equals(Instances, Vars, nAttribute7uniqueAttr, nAttribute9uniqueAttr, Result)
        ;
  	  attType(X_Class, X_Attr,"String") -> 
	  ocl_string_not_equals(Instances, Vars, nAttribute7uniqueAttr, nAttribute9uniqueAttr, Result)  
        ).
nimplies11uniqueAttr(Instances, Vars, Result):-
	ocl_implies(Instances, Vars, nnot_equals5uniqueAttr, nnot_equals10uniqueAttr, Result).
nforAll12uniqueAttr(Instances, Vars, Result):-
	nallInstances2uniqueAttr(Instances, Vars, Value1),
	ocl_col_forAll(Instances, Vars, Value1, nimplies11uniqueAttr, Result).
nforAll13uniqueAttr(Instances, Vars, Result):-
	nallInstances1uniqueAttr(Instances, Vars, Value1),
	ocl_col_forAll(Instances, Vars, Value1, nforAll12uniqueAttr, Result).
uniqueAttr(Instances, Para, Result):-
	nforAll13uniqueAttr(Instances, [Para], Result).
%--------------------------------------------------------------------------------------
%--Applying the Interval Pattern-------------------------------------------------------
%--------------------------------------------------------------------------------------
:- local struct(clsInterval(oid,left,right)).
apply_intervalInv(SOK, SNOK, Para):-
  Para = [X_Class, X_Attr, X_Intervals],
  index(X_Class,_),
  attType(X_Class, X_Attr, "Integer"),
  %--Computing X_Intervals based on SOK, SNOK----
  getAttrList(SOK, Para, SokList),
  getAttrList(SNOK, Para, TmpSnokList),
  subtract(TmpSnokList, SokList, Tmp1),
  %--Asuming all values SnokList are invalid-----
  msort(Tmp1, SnokList),
  computeIntervals(SokList, SnokList, X_Intervals),
  %--Ensuring the invariant accepts SOK----------
  (foreach(SOk, SOK),
   param(Para)
   do
     intervalInv(SOk, Para, 1)
  ),
  %--Ensuring the invariant rejects SNOK---------
  (foreach(SNok, SNOK),
   param(Para)
   do
     intervalInv(SNok, Para, 0)
  ).
%--Get the LocalPara-----------------------------
getLocalPara_intervalInv(Para,LocalPara):-
  LocalPara = Para.
%--Generating an invalid snapshot----------------
genSnok_intervalInv(SOK, SNOK, Para, Result):-
  MAX = 29999,
  MIN = -1,
  Para = [X_Class, X_Attr, X_Intervals],  
  getAttrList(SOK, Para, SokList),  
  getAttrList(SNOK, Para, TmpSnokList1),
  subtract(TmpSnokList1, SokList, TmpList2),  
  msort(TmpList2, SnokList),
  ( foreach(Intv, X_Intervals),
    fromto([MIN, null], In, Out, TmpRet),
    param(SnokList, MIN)
    do(
      Intv = clsInterval{oid:_,left: L,right: R},
      In = [L1, Ret1],
      ( Ret1 == null
        ->( for(I, L1, L),
            fromto(null,In1, Out1, Ret2),
            param(MIN, SnokList)
            do(
              member(I, SnokList)
              -> Out1 = In1;
              ( I == MIN 
                -> Out1 = In1;
                Out1 = I
              )
            )
          );
        Ret2 = Ret1
      ),
      Out = [R, Ret2]
    )
  ),
  TmpRet = [_, Attr1],
  ( Attr1 == null
    -> append(_, [Max1], SnokList),
       ( append(_, [Max2], SokList)
         -> max(Max1, Max2, V);
         V = Max1
       ),
       Attr is V + 1;
    Attr = Attr1
  ),
  Attr #< MAX,
  Attr #> MIN,
  number_string(Attr, AttrStr),
  sprintf(Result,"!create obj:%w....!set obj.%w:='%w'",[X_Class,X_Attr,AttrStr]).
%--Writing the IntervalPattern template----------
write_intervalInv(Para, Inv) :-
  MAX = 29999,
  MIN = -1,
  Para = [X_Class, X_Attr, X_Intervals],
  ( foreach(Intv, X_Intervals),
    fromto(null,In,Out,Tmp),
    param(MAX, MIN, X_Attr)
    do(
      Intv = clsInterval{oid:_,left: L,right: R},
      ( In \= null
        -> concat_strings(In, " or " , In_or);
        In_or = ""
      ),
      number_string(L, Lstr),
      number_string(R, Rstr),
      ( L == MIN
        ->( R == MAX -> Out = "true"
          ; ( R == 1 -> sprintf(Out,"%wself.%w = 0",[In_or,X_Attr])
	    ; sprintf(Out,"%wself.%w < %w",[In_or,X_Attr,Rstr])
            )
          )
        ;( R == MAX 
           -> sprintf(Out,"%w%w < self.%w",[In_or,Lstr,X_Attr])
           ; ( R is L + 2, V is L + 1, number_string(V, Vstr) -> sprintf(Out,"%w(self.%w = %w)",[In_or,X_Attr,Vstr])
 	     ; sprintf(Out,"%w(%w < self.%w and self.%w < %w)",[In_or,Lstr,X_Attr,X_Attr,Rstr])
             ) 
         )
      )
    )
  ),
  sprintf(OCLInv,"context %w inv intv_%w:....%w",[X_Class,X_Attr,Tmp]),
  ( foreach(Intv, X_Intervals),
    fromto(null,In1,Out1,IntvStr)
    do(
      Intv = clsInterval{oid:Id,left: L,right: R},
      ( In1 \= null
        -> concat_strings(In1, ",clsInterval(" , First);
        First = "clsInterval("
      ),
      number_string(Id, Idstr),
      number_string(L, Lstr),
      number_string(R, Rstr),
      sprintf(Out1,"%w%w,%w,%w)",[First,Idstr,Lstr,Rstr])
    )
  ),
  sprintf(ParaStr,"['%w','%w',[%w]]",[X_Class,X_Attr,IntvStr]),
  Inv = [ParaStr, OCLInv].
%--Encoding the OCL Interval template------------
nallInstances1intervalInv(Instances, [Para], Result):-
  Para = [X_Class, _, _],
  ocl_allInstances(Instances, X_Class, Result).
nallInstances2intervalInv(_, Vars, Result):-
  %ocl_allInstances(Instances, "ClsInterval", Result).
  append(_, [Para], Vars),
  Para = [_, _, X_Intervals],
  Result = X_Intervals.
nConstant3intervalInv(_, _, Result):-
  Result=0.
nVariable4intervalInv(_, Vars, Result):-
  ocl_variable(Vars,1,Result).
nVariable5intervalInv(_, Vars, Result):-
  ocl_variable(Vars,2,Result).
nAttribute6intervalInv(Instances, Vars, Result):-
  nVariable5intervalInv(Instances, Vars, Object),
  %ocl_attributeCall(Instances,"ClsInterval","left", Object, Result).
  arg(2, Object, Result).
nVariable7intervalInv(_, Vars, Result):-
  ocl_variable(Vars,3,Result).
nAttribute8intervalInv(Instances, Vars, Result):-
  append(_, [Para], Vars),
  Para = [X_Class, X_Attr, _],
  nVariable7intervalInv(Instances, Vars, Object),
  ocl_attributeCall(Instances,X_Class,X_Attr, Object, Result).
nless_than9intervalInv(Instances, Vars, Result):-
  ocl_int_less_than(Instances, Vars, nAttribute6intervalInv, nAttribute8intervalInv, Result).
nVariable10intervalInv(_, Vars, Result):-
  ocl_variable(Vars,3,Result).
nAttribute11intervalInv(Instances, Vars, Result):-
  append(_, [Para], Vars),
  Para = [X_Class, X_Attr, _],
  nVariable10intervalInv(Instances, Vars, Object),
  ocl_attributeCall(Instances,X_Class,X_Attr, Object, Result).
nVariable12intervalInv(_, Vars, Result):-
  ocl_variable(Vars,2,Result).
nAttribute13intervalInv(Instances, Vars, Result):-
  nVariable12intervalInv(Instances, Vars, Object),
  %ocl_attributeCall(Instances,"ClsInterval","right", Object, Result).
  arg(3, Object, Result).
nless_than14intervalInv(Instances, Vars, Result):-
  ocl_int_less_than(Instances, Vars, nAttribute11intervalInv, nAttribute13intervalInv, Result).
nand15intervalInv(Instances, Vars, Result):-
  ocl_and(Instances, Vars, nless_than9intervalInv, nless_than14intervalInv, Result).
nor16intervalInv(Instances, Vars, Result):-
  ocl_or(Instances, Vars, nVariable4intervalInv, nand15intervalInv, Result).
niterate17intervalInv(Instances, Vars, Result):-
  nallInstances2intervalInv(Instances, Vars, Value1),
  nConstant3intervalInv(Instances, Vars, Value2),
  ( foreach(Xe, Value1),
    fromto(Value2, In, Out, Result),
    param(Instances, Vars)
    do nor16intervalInv(Instances, [In | [Xe | Vars]], Out)
  ).
nforAll18intervalInv(Instances, Vars, Result):-
  nallInstances1intervalInv(Instances, Vars, Value1),
  ocl_col_forAll(Instances, Vars, Value1, niterate17intervalInv, Result).
intervalInv(Instances, Para, Result):-
  nforAll18intervalInv(Instances, [Para], Result).
%------------------------------------------------
%--aux_predicates to realize Interval pattern----
%------------------------------------------------
getAttrList(Snapshots, Para, AttrList) :-
  Para = [X_Class, X_Attr, _],
  (foreach(S, Snapshots),
   fromto([], In, Out, TmpList),
   param(X_Class, X_Attr) 
   do(
     attIndex(X_Class, X_Attr, AttrIdx),
     ocl_allInstances(S, X_Class, XObjects),
     (foreach(XObj, XObjects),
       fromto(In, In1, Out1, Out),
       param(AttrIdx)
       do
         arg(AttrIdx, XObj, AttrValue),         
         ( In1 = oclUndefined 
           -> Out1=oclUndefined;  
           ( AttrValue = oclUndefined 
             -> Out1=oclUndefined; 
             Out1 = [AttrValue | In1]
           )        
         )
     )
   )
  ),
  TmpList \= oclUndefined,
  msort(TmpList, AttrList).
%------------------------------------------------
createNewInterval(Intervals, Left, Right, NewIntv) :-
  length(Intervals, N),
  Oid is N + 1,
  NewIntv = clsInterval{oid: Oid, left: Left, right: Right}.
%------------------------------------------------
computeIntervals([], [], [_]):-
  fail.
%  MAX = 29999,
%  MIN = -1,
%  createNewInterval([], MIN, MAX, Intv).

computeIntervals(SokList, [], [Intv]):-
  SokList = [SokL | _],
  append(_, [SokR], SokList),
  L is SokL - 1,
  R is SokR + 1,
  createNewInterval([], L, R, Intv).

computeIntervals([], SnokList, [Intv1,Intv2]):-
  MAX = 29999,
  MIN = -1,
  SnokList = [SnokL | _],
  append(_, [SnokR], SnokList),
  createNewInterval([], MIN, SnokL, Intv1),
  createNewInterval([Intv1], SnokR, MAX, Intv2).

computeIntervals(SokList, SnokList, X_Intervals):-
  MAX = 29999,
  MIN = -1,
  SokList = [_|_],
  SnokList = [_|_],
  append(SnokList, [MAX], Tmp),
  computeIntervalsLocal(SokList, [MIN | Tmp], X_Intervals).

computeIntervalsLocal(_, [], []).

computeIntervalsLocal([], _, []).

computeIntervalsLocal([_], [_], []).

computeIntervalsLocal(SokList, SnokList, X_Intervals):-
  append([Sok], SokList1, SokList),
  append([Snok], _, SnokList),
  ( Sok < Snok
    -> computeIntervalsLocal(SokList1, SnokList, X_Intervals);
    ( foreach(Snok, SnokList),
      fromto(SnokList,In,Out,SnokList2),
      param(Sok)
      do(
        Snok < Sok
        -> In = [Snok | Out];
        Out = In
      )
    ),
    append(_, [SnokL | SnokList2], SnokList),
    SnokList2 = [SnokR | _],
    createNewInterval(X_Intervals1, SnokL, SnokR, NewIntv),
    computeIntervalsLocal(SokList, SnokList2, X_Intervals1),!,
    X_Intervals = [NewIntv | X_Intervals1]
  ).
%---Check combination of the pattern---------------------
combined_intervalInv(Pat, Para, ParaList):-
  Para = [X_Class, X_Attr, _],
  member([Pat, [X_Class, X_Attr,_]], ParaList).
%--------------------------------------------------------------------------------------
%--Applying Multiplicity Pattern-------------------------------------------------------
%--------------------------------------------------------------------------------------
%:- local struct(clsInterval(oid,left,right)).
apply_cardInv(SOK, SNOK, Para):-
  %Para = [X_Class, X_Role, X_Intervals],
  Para = [_, _, X_Intervals],
  getLocalPara_cardInv(Para,LocalPara),
  %--Computing X_Intervals based on SOK, SNOK----
  getCardList(SOK, LocalPara, SokList),
  getCardList(SNOK, LocalPara, TmpSnokList),
  subtract(TmpSnokList, SokList, Tmp1),
  %--Asuming all values SnokList are invalid-----
  msort(Tmp1, SnokList),
  computeIntervals(SokList, SnokList, X_Intervals),
  %--Ensuring the invariant accepts SOK----------
  (foreach(SOk, SOK),
   param(LocalPara)
   do
     cardInv(SOk, LocalPara, 1)
  ),
  %--Ensuring the invariant rejects SNOK---------
  ( foreach(SNok, SNOK),
    param(LocalPara)
    do      
      LocalPara = [_, X_Assoc, _, _, _, X_Class2],	
      %--check if any target object exists	
      ocl_allInstances(SNok, X_Class2, X_Objs),
      X_Objs \= [],
      %--check if X_Assoc is underconsidered
      index(X_Assoc, X_AssocIndex),
      nth1(X_AssocIndex, SNok, X_LinkList),
      X_LinkList \= [],
      cardInv(SNok, LocalPara, 0)
  ).
%--Get the LocalPara-----------------------------
getLocalPara_cardInv(Para,LocalPara):-
  Para = [X_Class, X_Role, X_Intervals],
  LocalPara = [X_Class, X_Assoc, X_Role, Role2, X_Intervals, X_Class2],
  is_predicate(roleType/3),
  roleType(X_Assoc, Role2, X_Class),
  roleType(X_Assoc, X_Role, X_Class2),
  X_Role \= Role2.

%--Generating an invalid snapshot----------------
%genSnok_cardInv(SOK, SNOK, Para, Result):-
%  Para = [X_Class, X_Role, X_Intervals],  
%  Result = "".
%--Writing the MultiplicityPattern template------
write_cardInv(Para, Inv) :-
  MIN = -1,
  MAX = 29999,
  Para = [X_Class, X_Role, X_Intervals],
  ( foreach(Intv, X_Intervals),
    fromto(null,In,Out,Tmp),
    param(MIN, MAX, X_Role)
    do(
      Intv = clsInterval{oid:_,left: L,right: R},
      ( In \= null
        -> concat_strings(In, " or " , In_or);
        In_or = ""
      ),
      number_string(L, Lstr),
      number_string(R, Rstr),
      ( L == MIN
        ->( R == MAX -> Out = "true"
          ; ( R == 1 -> sprintf(Out,"%wself.%w->size() = 0",[In_or,X_Role])
            ; sprintf(Out,"%wself.%w->size() < %w",[In_or,X_Role,Rstr])
	    )
          )
        ; ( R == MAX -> sprintf(Out,"%w%w < self.%w->size()",[In_or,Lstr,X_Role])
          ; ( R is L + 2, V is L + 1, number_string(V, Vstr) -> sprintf(Out,"%w(self.%w->size() = %w)",[In_or,X_Role,Vstr])
 	    ; sprintf(Out,"%w(%w < self.%w->size() and self.%w->size() < %w)",[In_or,Lstr,X_Role,X_Role,Rstr])
            ) 
	  )
      )
    )
  ),
  sprintf(OCLInv,"context %w inv cardInv_%w:....%w",[X_Class,X_Role,Tmp]),
  ( foreach(Intv, X_Intervals),
    fromto(null,In1,Out1,IntvStr)
    do(
      Intv = clsInterval{oid:Id,left: L,right: R},
      ( In1 \= null
        -> concat_strings(In1, ",clsInterval(" , First);
        First = "clsInterval("
      ),
      number_string(Id, Idstr),
      number_string(L, Lstr),
      number_string(R, Rstr),
      sprintf(Out1,"%w%w,%w,%w)",[First,Idstr,Lstr,Rstr])
    )
  ),
  sprintf(ParaStr,"['%w','%w',[%w]]",[X_Class,X_Role,IntvStr]),
  Inv = [ParaStr, OCLInv].

%--Encoding the OCL MultpConstr template------------
nallInstances1cardInv(Instances, [Para], Result):-
        Para = [X_Class, _, _,_,_,_],
	ocl_allInstances(Instances, X_Class, Result).
nallInstances2cardInv(_, Vars, Result):-
	%ocl_allInstances(Instances, "X_Interval", Result).
        append(_, [Para], Vars),
        Para = [_, _, _, _, X_Intervals,_],
        Result = X_Intervals.
nConstant3cardInv(_, _, Result):-
	Result=0.
nVariable4cardInv(_, Vars, Result):-
	ocl_variable(Vars,1,Result).
nVariable5cardInv(_, Vars, Result):-
	ocl_variable(Vars,2,Result).
nAttribute6cardInv(Instances, Vars, Result):-
	nVariable5cardInv(Instances, Vars, Object),
	%ocl_attributeCall(Instances,"X_Interval","Left", Object, Result).
        arg(2, Object, Result).
nVariable7cardInv(_, Vars, Result):-
	ocl_variable(Vars,3,Result).
nNavigation8cardInv(Instances, Vars, Result):-
        append(_, [Para], Vars),
        Para = [_, X_Assoc, X_Role, Role2, _, _],
	nVariable7cardInv(Instances, Vars, Value1),
	ocl_navigation(Instances,X_Assoc,Role2,X_Role, Value1, Result).
nsize9cardInv(Instances, Vars, Result):-
	nNavigation8cardInv(Instances, Vars, Value1),
	ocl_set_size(Value1, Result).
nless_than10cardInv(Instances, Vars, Result):-
	ocl_int_less_than(Instances, Vars, nAttribute6cardInv, nsize9cardInv, Result).
nVariable11cardInv(_, Vars, Result):-
	ocl_variable(Vars,3,Result).
nNavigation12cardInv(Instances, Vars, Result):-
        append(_, [Para], Vars),
        Para = [_, X_Assoc, X_Role, Role2, _, _],
	nVariable7cardInv(Instances, Vars, Value1),
	nVariable11cardInv(Instances, Vars, Value1),
	ocl_navigation(Instances,X_Assoc,Role2,X_Role, Value1, Result).
nsize13cardInv(Instances, Vars, Result):-
	nNavigation12cardInv(Instances, Vars, Value1),
	ocl_set_size(Value1, Result).
nVariable14cardInv(_, Vars, Result):-
	ocl_variable(Vars,2,Result).
nAttribute15cardInv(Instances, Vars, Result):-
	nVariable14cardInv(Instances, Vars, Object),
	%ocl_attributeCall(Instances,"X_Interval","Right", Object, Result).
        arg(3, Object, Result).
nless_than16cardInv(Instances, Vars, Result):-
	ocl_int_less_than(Instances, Vars, nsize13cardInv, nAttribute15cardInv, Result).
nand17cardInv(Instances, Vars, Result):-
	ocl_and(Instances, Vars, nless_than10cardInv, nless_than16cardInv, Result).
nor18cardInv(Instances, Vars, Result):-
	ocl_or(Instances, Vars, nVariable4cardInv, nand17cardInv, Result).
niterate19cardInv(Instances, Vars, Result):-
	nallInstances2cardInv(Instances, Vars, Value1),
	nConstant3cardInv(Instances, Vars, Value2),
	( foreach(Xe, Value1),
	  fromto(Value2, In, Out, Result),
	  param(Instances, Vars)
	  do nor18cardInv(Instances, [In | [Xe | Vars]], Out)
	).
nforAll20cardInv(Instances, Vars, Result):-
	nallInstances1cardInv(Instances, Vars, Value1),
	ocl_col_forAll(Instances, Vars, Value1, niterate19cardInv, Result).
cardInv(Instances, Para, Result):-
	nforAll20cardInv(Instances, [Para], Result).
%------------------------------------------------
%--aux_predicates for MultiplicityPattern--------
%------------------------------------------------
getCardList(Snapshots, Para, CardList) :-
  Para = [X_Class, X_Assoc, X_Role, Role2, _,_],
  (foreach(S, Snapshots),
   fromto([], In, Out, TmpList),
   param(X_Class, X_Assoc, X_Role, Role2)
   do(	
     ocl_allInstances(S, X_Class, XObjects),
     ( foreach(XObj, XObjects),
       fromto(In, In1, Out1, Out),
       param(S, X_Assoc, X_Role, Role2)
       do(
         ocl_navigation(S,X_Assoc,Role2,X_Role, XObj, ObjSet),
         ocl_set_size(ObjSet, CardValue),
         ( In1 = oclUndefined
           -> Out1 = oclUndefined;
           ( CardValue = oclUndefined
             -> Out1 = oclUndefined;
             Out1 = [CardValue | In1]
           )
         )
       )
     )
    )
  ),
  TmpList \= oclUndefined,
  msort(TmpList, CardList1),
  ( CardList1 == [] 
    -> CardList = [0];
    CardList=CardList1
  ).
%---Check combination of the pattern---------------------
combined_cardInv(Pat, Para, ParaList):-
  Para = [X_Class, X_Role, _],
  member([Pat, [X_Class, X_Role,_]], ParaList).
%--------------------------------------------------------------------------------------
%--Applying the NonSelfInclusion Pattern-----------------------------------------------
%--------------------------------------------------------------------------------------
apply_nonSelfInc(SOK, SNOK, Para):-
  %Para = [X_Class,X_Role],
  Para = [_,_],
  getLocalPara_nonSelfInc(Para,LocalPara),
  %--Ensuring the invariant accepts SOK----------
  (foreach(SOk, SOK),
   param(LocalPara)
   do
     nonSelfInc(SOk, LocalPara, 1)
  ),
  %--Ensuring the invariant rejects SNOK---------
  (foreach(SNok, SNOK),
   param(LocalPara)
   do
     nonSelfInc(SNok, LocalPara, 0)
  ).
%--Get the LocalPara-----------------------------
getLocalPara_nonSelfInc(Para,LocalPara):-
  Para = [X_Class,X_Role],
  LocalPara = [X_Class,X_Assoc,X_Role,Role2,ClsB],
  is_predicate(roleType/3),
  roleType(X_Assoc,Role2,X_Class),
  roleType(X_Assoc,X_Role,ClsB),
  X_Role \= Role2,	
  %--Ensuring X_Class is a subtype of ClsB-------
  ( X_Class \= ClsB 
    ->(aux_subTypeList(ClsB, TypeList),
        member(X_Class, TypeList)
      );
    true
  ).
%--Writing the NonSelfIncPattern template--------
write_nonSelfInc(Para, Inv) :-
  Para = [X_Class,X_Role],
  sprintf(OCLInv,"context %w inv nonSelfInc_%w:....self.%w -> excludes(self)",[X_Class,X_Role,X_Role]),
  sprintf(ParaStr,"['%w','%w']",[X_Class,X_Role]),
  Inv = [ParaStr,OCLInv].
%--Encoding the OCL nonSelfInc template---------
nallInstances1nonSelfInc(Instances,[Para],Result):-
  Para = [X_Class,_,_,_,_],
  ocl_allInstances(Instances, X_Class, Result).
nVariable2nonSelfInc(_, Vars, Result):-
  ocl_variable(Vars,1,Result).
nNavigation3nonSelfInc(Instances, Vars, Result):-
  append(_, [Para], Vars),
  Para = [_,X_Assoc,X_Role,Role2,_],
  nVariable2nonSelfInc(Instances, Vars, Value1),
  ocl_navigation(Instances,X_Assoc,Role2,
                          X_Role,Value1, Result).
nVariable4nonSelfInc(_, Vars, Result):-
  ocl_variable(Vars,1,Result).
nexcludes5nonSelfInc(Instances, Vars, Result):-
  nNavigation3nonSelfInc(Instances,Vars,Value1),
  nVariable4nonSelfInc(Instances, Vars, Value2),
  ocl_set_excludes(Value1, Value2, Result).
nforAll6nonSelfInc(Instances, Vars, Result):-
  nallInstances1nonSelfInc(Instances,Vars,Value1),
  ocl_col_forAll(Instances, Vars, Value1, 
                  nexcludes5nonSelfInc, Result).
nonSelfInc(Instances, Para, Result):-
  nforAll6nonSelfInc(Instances, [Para], Result).
%--------------------------------------------------------------------------------------
%--Applying AttrRel Pattern------------------------------------------------------------
%--------------------------------------------------------------------------------------
:- local struct(attrPair(first,second)).

apply_attrRel(SOK, SNOK, Para):-
  %Para = [X_Class,X_Role,X_Attr1,X_Attr2,X1,X2],
  Para = [_,_,_,_,X1,X2],
  getLocalPara_attrRel(Para,LocalPara),
  %--Computing X1, X2 based on SOK, SNOK---------
  getAttrPairList(SOK, LocalPara, SokList),
  getAttrPairList(SNOK, LocalPara, SnokList),  
  computeAttrPairSup(SokList, SnokList, X1, X2),
  %--Ensuring the invariant accepts SOK----------
  ( foreach(SOk, SOK),
    param(LocalPara)
    do
      attrRel(SOk, LocalPara, 1)
  ),
  %--Ensuring the invariant rejects SNOK---------
  ( foreach(SNok, SNOK),
    param(LocalPara)
    do(
      attrRel(SNok, LocalPara, 0)
    )
  ).
%--Get the LocalPara-----------------------------
getLocalPara_attrRel(Para,LocalPara):-
  Para = [X_Class,X_Role,X_Attr1,X_Attr2,X1,X2],
  LocalPara = [X_Class,ClsB,X_Assoc,X_Role,Role2,X_Attr1,X_Attr2,X1,X2],
  is_predicate(roleType/3),
  roleType(X_Assoc,X_Role,ClsB),
  roleType(X_Assoc,Role2,X_Class),
  X_Role \= Role2,
  roleMax(X_Assoc,X_Role,1),
  attType(X_Class, X_Attr1, "Integer"),
  attType(ClsB, X_Attr2, "Integer").
%--Writing the AttrRelPattern template----------
write_attrRel(Para, Inv) :-
  Para = [X_Class,X_Role,X_Attr1,X_Attr2,X1,X2],
  number_string(X1, StrX1),
  number_string(X2, StrX2),
  sprintf(OCLInv,"context %w inv attrRel_%w_%w:....self.%w < %w implies self.%w.%w < %w",[X_Class,X_Attr1,X_Attr2,X_Attr1,StrX1,X_Role,X_Attr2,StrX2]),
  sprintf(ParaStr,"['%w','%w','%w','%w',%w,%w]",[X_Class,X_Role,X_Attr1,X_Attr2,StrX1,StrX2]),
  Inv = [ParaStr, OCLInv].
%--Encoding the OCL AttrRel template-------------
nallInstances1attrRel(Instances, [Para], Result):-
        Para = [X_Class,_,_,_,_,_,_,_,_],
	ocl_allInstances(Instances, X_Class, Result).
nVariable2attrRel(_, Vars, Result):-
	ocl_variable(Vars,1,Result).
nAttribute3attrRel(Instances, Vars, Result):-
        append(_, [Para], Vars),
        Para = [X_Class,_,_,_,_,X_Attr1,_,_,_],
	nVariable2attrRel(Instances, Vars, Object),
	ocl_attributeCall(Instances,X_Class,X_Attr1, Object, Result).
nConstant4attrRel(_, Vars, Result):-
        append(_, [Para], Vars),
        Para = [_,_,_,_,_,_,_,Result,_].
nless_than5attrRel(Instances, Vars, Result):-
	ocl_int_less_than(Instances, Vars, nAttribute3attrRel, nConstant4attrRel, Result).
nVariable6attrRel(_, Vars, Result):-
	ocl_variable(Vars,1,Result).
nNavigation7attrRel(Instances, Vars, Result):-
        append(_, [Para], Vars),
        Para = [_,_,X_Assoc,X_Role,Role2,_,_,_,_],
	nVariable6attrRel(Instances, Vars, Value1),
	ocl_navigation(Instances,X_Assoc,Role2,X_Role, Value1, Result).
nAttribute8attrRel(Instances, Vars, Result):-
        append(_, [Para], Vars),
        Para = [_,ClsB,_,_,_,_,X_Attr2,_,_],
	nNavigation7attrRel(Instances, Vars, Object),
	ocl_attributeCall(Instances,ClsB,X_Attr2, Object, Result).
nConstant9attrRel(_, Vars, Result):-
        append(_, [Para], Vars),
        Para = [_,_,_,_,_,_,_,_,Result].
nless_than10attrRel(Instances, Vars, Result):-
	ocl_int_less_than(Instances, Vars, nAttribute8attrRel, nConstant9attrRel, Result).
nimplies11attrRel(Instances, Vars, Result):-
	ocl_implies(Instances, Vars, nless_than5attrRel, nless_than10attrRel, Result).
nforAll12attrRel(Instances, Vars, Result):-
	nallInstances1attrRel(Instances, Vars, Value1),
	ocl_col_forAll(Instances, Vars, Value1, nimplies11attrRel, Result).
attrRel(Instances, Para, Result):-
	nforAll12attrRel(Instances, [Para], Result).
%------------------------------------------------
%--aux_predicates to realize AttrRel pattern-----
%------------------------------------------------
getAttrPairList(Snapshots, Para, AttrPairList) :-
  Para = [X_Class,ClsB,X_Assoc,X_Role,Role2,X_Attr1,X_Attr2,_,_],
  ( foreach(S, Snapshots),
    fromto([], In, Out, AttrPairList),
    param(X_Class, ClsB, X_Assoc,Role2,X_Role, X_Attr1, X_Attr2) 
    do
      In = oclUndefined
      -> Out = oclUndefined;
      attIndex(X_Class, X_Attr1, AttrIdx1),
      ocl_allInstances(S, X_Class, XObjects),
      ( foreach(XObj1, XObjects),
        fromto(In, In1, Out1, Out),
        param(S,ClsB, X_Assoc,Role2,X_Role, X_Attr2, AttrIdx1)
        do          
          In1 = oclUndefined 
          -> Out1 = oclUndefined;
	  arg(AttrIdx1, XObj1, X1),
          ( X1 = oclUndefined
            -> Out1 = oclUndefined;
            ocl_navigation(S,X_Assoc,Role2,X_Role, XObj1, XObj2),
            ( XObj2 = oclUndefined
              -> X2 = oclUndefined;
	      attIndex(ClsB, X_Attr2, AttrIdx2),
              arg(AttrIdx2, XObj2, X2)
            ),
	    Out1 = [ attrPair{first:X1, second:X2} | In1 ]	                            
          )                  
      )
  ),  
  AttrPairList \= oclUndefined.

computeAttrPairSup(_, [], _, _):-
  fail.
%  MAX = 29999,
%  X1 = MAX, X2 = MAX.

computeAttrPairSup(SokList, SnokList, X1, X2):-
  SnokList =[_|_],
  ( foreach(attrPair{first:Attr1,second:Attr2}, SnokList),
    fromto(oclUndefined,In1,Out1,X1)
    do(
      In1 = oclUndefined 
      -> ( Attr2 = oclUndefined
           -> Out1 = oclUndefined;
           Out1 is Attr1 + 1
         );
      ( In1 #> Attr1
        -> ( Attr2 = oclUndefined 
             -> fail;
             Out1 = In1
           );
        ( Attr2 = oclUndefined
          -> Out1 = In1;
          Out1 is Attr1 + 1
        )
      )
    )
  ),
  X1 \= oclUndefined,
  ( foreach(attrPair{first:_,second:Attr2}, SnokList),
    fromto(oclUndefined,In2,Out2,X2)
    do( 
      Attr2 = oclUndefined
      -> Out2 = In2;
      ( In2 = oclUndefined   
        -> Out2 = Attr2;
        ( In2 #> Attr2
          -> Out2 = Attr2;
          Out2 = In2
        )
      )
    )
  ),  
  X2 \= oclUndefined,
  ( foreach(attrPair{first:A1,second:A2}, SokList),
    param(X1,X2)
    do(
      A2 \= oclUndefined
      -> A1 #< X1,
         A2 #< X2;
      true
    )
  ).
%--------------------------------------------------------------------------------------
%--Applying MaxCard Pattern------------------------------------------------------------
%--------------------------------------------------------------------------------------
apply_maxCard(SOK, SNOK, Para):-
% Para = [X_Class,X_MaxCard,X_Role],
  getLocalPara_maxCard(Para,LocalPara),
  %--Ensuring the invariant accepts SOK----------
  ( foreach(SnapshotOk, SOK),
    param(LocalPara)
    do
      maxCard(SnapshotOk, LocalPara, 1)
  ),
  %--Ensuring the invariant rejects SNOK---------
  ( foreach(SnapshotNok, SNOK),
    param(LocalPara)
    do
      maxCard(SnapshotNok, LocalPara, 0)
  ).
%--Get the LocalPara-----------------------------
getLocalPara_maxCard(Para,LocalPara):-
  Para = [X_Class,X_MaxCard,X_Role],  
  LocalPara = [X_Class,X_MaxCard,X_Assoc,X_Role,Role2,ClsB],
  index(X_Class,_),
  attIndex(X_Class, X_MaxCard, _),
  attType(X_Class, X_MaxCard,"Integer"),
  is_predicate(roleType/3),
  roleType(X_Assoc,Role2,X_Class),
  roleType(X_Assoc,X_Role,ClsB),
  X_Role \= Role2.
%--Writing the MaxCard template------------------
write_maxCard(Para, Inv) :-
  Para = [X_Class,X_MaxCard,X_Role],
  sprintf(OCLInv,"context %w inv maxCard_%w:....self.%w->size()<=self.%w",[X_Class,X_Role,X_Role,X_MaxCard]),
  sprintf(ParaStr,"['%w','%w','%w']",[X_Class,X_MaxCard,X_Role]),
  Inv = [ParaStr, OCLInv].
%--Encoding the OCL MaxCard template-------------
nallInstances1maxCard(Instances, [Para], Result):-
	Para = [X_Class,_,_,_,_,_],
	ocl_allInstances(Instances, X_Class, Result).
nVariable2maxCard(_, Vars, Result):-
	ocl_variable(Vars,1,Result).
nNavigation3maxCard(Instances, Vars, Result):-
	append(_, [Para], Vars),
	Para = [_,_,X_Assoc,X_Role,Role2,_],
	nVariable2maxCard(Instances, Vars, Value1),
	ocl_navigation(Instances,X_Assoc,Role2,X_Role, Value1, Result).
nsize4maxCard(Instances, Vars, Result):-
	nNavigation3maxCard(Instances, Vars, Value1),
	ocl_set_size(Value1, Result).
nVariable5maxCard(_, Vars, Result):-
	ocl_variable(Vars,1,Result).
nAttribute6maxCard(Instances, Vars, Result):-
	append(_, [Para], Vars),
	Para = [X_Class,X_MaxCard,_,_,_,_],
	nVariable5maxCard(Instances, Vars, Object),
	ocl_attributeCall(Instances,X_Class,X_MaxCard, Object, Result).
nless_than7maxCard(Instances, Vars, Result):-
	ocl_int_less_equal(Instances, Vars, nsize4maxCard, nAttribute6maxCard, Result).
nforAll8maxCard(Instances, Vars, Result):-
	nallInstances1maxCard(Instances, Vars, Value1),
	ocl_col_forAll(Instances, Vars, Value1, nless_than7maxCard, Result).
maxCard(Instances, Para, Result):-
	nforAll8maxCard(Instances, [Para], Result).
%--------------------------------------------------------------------------------------
%--Applying RequiredInclusion Pattern--------------------------------------------------
%--------------------------------------------------------------------------------------
apply_requiredInclusion(SOK, SNOK, Para):-
% Para = [X_Class,X_RoleB,X_Required]
  getLocalPara_requiredInclusion(Para,LocalPara),
  %--Ensuring the invariant accepts SOK----------
  ( foreach(SnapshotOk, SOK),
    param(LocalPara)
    do
      requiredInclusion(SnapshotOk, LocalPara, 1)
  ),
  %--Ensuring the invariant rejects SNOK---------
  ( foreach(SnapshotNok, SNOK),
    param(LocalPara)
    do
      requiredInclusion(SnapshotNok, LocalPara, 0)
  ).
%--Get the LocalPara-----------------------------
getLocalPara_requiredInclusion(Para,LocalPara):-
  Para = [X_Class,X_RoleB,X_Required],  
  LocalPara = [X_Class,Assoc,X_RoleB,Role2,AssocR,X_Required,Dependent,ClsB],
  index(X_Class,_),
  is_predicate(roleType/3),
  roleType(Assoc,Role2,X_Class),
  roleType(Assoc,X_RoleB,ClsB),
  X_RoleB \= Role2,
  X_Class \= ClsB,
  roleType(AssocR,X_Required,ClsB),
  roleType(AssocR,Dependent,ClsB),
  X_Required \= Dependent.
%--Writing the RequiredInclusion template---------
write_requiredInclusion(Para, Inv) :-
  Para = [X_Class,X_RoleB,X_Required],
  sprintf(OCLInv,"context %w inv requiredInclusion_%w:....self.%w->forAll(d |....d.%w->forAll(r | self.%w->includes(r)))",[X_Class,X_RoleB,X_RoleB,X_Required,X_RoleB]),
  sprintf(ParaStr,"['%w','%w','%w']",[X_Class,X_RoleB,X_Required]),
  Inv = [ParaStr, OCLInv].
%--Encoding the OCL RequiredInclusion template------
nallInstances1requiredInclusion(Instances, [Para], Result):-
	Para = [X_Class,_,_,_,_,_,_,_],
	ocl_allInstances(Instances, X_Class, Result).
nVariable2requiredInclusion(_, Vars, Result):-
	ocl_variable(Vars,1,Result).
nNavigation3requiredInclusion(Instances, Vars, Result):-
	append(_, [Para], Vars),
	Para = [_,Assoc,X_RoleB,Role2,_,_,_,_],
	nVariable2requiredInclusion(Instances, Vars, Value1),
	ocl_navigation(Instances,Assoc,Role2,X_RoleB, Value1, Result).
nVariable4requiredInclusion(_, Vars, Result):-
	ocl_variable(Vars,1,Result).
nNavigation5requiredInclusion(Instances, Vars, Result):-
	append(_, [Para], Vars),
	Para = [_,_,_,_,AssocR,X_Required,Dependent,_],
	nVariable4requiredInclusion(Instances, Vars, Value1),
	ocl_navigation(Instances,AssocR,Dependent,X_Required, Value1, Result).
nVariable6requiredInclusion(_, Vars, Result):-
	ocl_variable(Vars,3,Result).
nNavigation7requiredInclusion(Instances, Vars, Result):-
	append(_, [Para], Vars),
	Para = [_,Assoc,X_RoleB,Role2,_,_,_,_],
	nVariable6requiredInclusion(Instances, Vars, Value1),
	ocl_navigation(Instances,Assoc,Role2,X_RoleB, Value1, Result).
nVariable8requiredInclusion(_, Vars, Result):-
	ocl_variable(Vars,1,Result).
nincludes9requiredInclusion(Instances, Vars, Result):-
	nNavigation7requiredInclusion(Instances, Vars, Value1),
	nVariable8requiredInclusion(Instances, Vars, Value2),
	ocl_set_includes(Value1, Value2, Result).
nforAll10requiredInclusion(Instances, Vars, Result):-
	nNavigation5requiredInclusion(Instances, Vars, Value1),
	ocl_col_forAll(Instances, Vars, Value1, nincludes9requiredInclusion, Result).
nforAll11requiredInclusion(Instances, Vars, Result):-
	nNavigation3requiredInclusion(Instances, Vars, Value1),
	ocl_col_forAll(Instances, Vars, Value1, nforAll10requiredInclusion, Result).
nforAll12requiredInclusion(Instances, Vars, Result):-
	nallInstances1requiredInclusion(Instances, Vars, Value1),
	ocl_col_forAll(Instances, Vars, Value1, nforAll11requiredInclusion, Result).
requiredInclusion(Instances, Para, Result):-
	nforAll12requiredInclusion(Instances, [Para], Result).
%--------------------------------------------------------------------------------------
%--Applying RestrictedAssoc Pattern----------------------------------------------------
%--------------------------------------------------------------------------------------
apply_restrictedAssoc(SOK, SNOK, Para):-
% Para = [X_Class,X_RoleB,X_Required]
  getLocalPara_restrictedAssoc(Para,LocalPara),
  %--Ensuring the invariant accepts SOK----------
  ( foreach(SnapshotOk, SOK),
    param(LocalPara)
    do
      restrictedAssoc(SnapshotOk, LocalPara, 1)
  ),
  %--Ensuring the invariant rejects SNOK---------
  ( foreach(SnapshotNok, SNOK),
    param(LocalPara)
    do
      restrictedAssoc(SnapshotNok, LocalPara, 0)
  ).
%--Get the LocalPara-----------------------------
getLocalPara_restrictedAssoc(Para,LocalPara):-
  Para = [X_ClassA,X_Cond,X_RoleA,X_RoleB,X_RoleC],
  LocalPara = [X_ClassA,X_Cond,X_RoleA,X_RoleB,X_AssocBC,X_RoleC,RoleCB,ClsB],
  is_predicate(roleAssocCls/3),
  roleAssocCls(X_ClassA,X_RoleA,ClsB),
  roleAssocCls(X_ClassA,X_RoleB,ClsB),
  X_RoleA @< X_RoleB,
  attType(X_ClassA,X_Cond,"Boolean"),
  is_predicate(roleType/3),
  roleType(X_AssocBC,RoleCB,ClsB),
  roleType(X_AssocBC,X_RoleC,ClsC),
  RoleCB \= X_RoleC,
  ClsB \= ClsC.
%--Writing the RestrictedAssoc template---------
write_restrictedAssoc(Para, Inv) :-
  Para = [X_ClassA,X_Cond,X_RoleA,X_RoleB,X_RoleC],
  sprintf(OCLInv,"context %w inv restrictedAssoc_%w:....self.%w implies....self.%w.%w->excludesAll(self.%w.%w)",[X_ClassA,X_Cond,X_Cond,X_RoleA,X_RoleC,X_RoleB,X_RoleC]),
  sprintf(ParaStr,"['%w','%w','%w','%w','%w']",[X_ClassA,X_Cond,X_RoleA,X_RoleB,X_RoleC]),
  Inv = [ParaStr, OCLInv].
%--Encoding the OCL RestrictedAssoc template------
nallInstances1restrictedAssoc(Instances, [Para], Result):-
	Para = [X_ClassA,_,_,_,_,_,_,_],
	ocl_allInstances(Instances, X_ClassA, Result).
nVariable2restrictedAssoc(_, Vars, Result):-
	ocl_variable(Vars,1,Result).
nAttribute3restrictedAssoc(Instances, Vars, Result):-
	append(_, [Para], Vars),
	Para = [X_ClassA,X_Cond,_,_,_,_,_,_],
	nVariable2restrictedAssoc(Instances, Vars, Object),
	ocl_attributeCall(Instances,X_ClassA,X_Cond, Object, Result).
nVariable4restrictedAssoc(_, Vars, Result):-
	ocl_variable(Vars,1,Result).
nAttribute5restrictedAssoc(Instances, Vars, Result):-
	append(_, [Para], Vars),
	Para = [X_ClassA,_,X_RoleA,_,_,_,_,_],
	nVariable4restrictedAssoc(Instances, Vars, Object),
	ocl_attributeCall(Instances,X_ClassA,X_RoleA, Object, Result).
nVariable6restrictedAssoc(_, Vars, Result):-
	ocl_variable(Vars,1,Result).
nNavigation7restrictedAssoc(Instances, Vars, Result):-
	append(_, [Para], Vars),
	Para = [_,_,_,_,X_AssocBC,X_RoleC,RoleCB,_],
	nVariable6restrictedAssoc(Instances, Vars, Value1),
	ocl_navigation(Instances,X_AssocBC,RoleCB,X_RoleC, Value1, Result).
ncollect8restrictedAssoc(Instances, Vars, Result):-
	nAttribute5restrictedAssoc(Instances, Vars, Value1),
	ocl_bag_collect(Instances, Vars, Value1, nNavigation7restrictedAssoc, Result).
nVariable9restrictedAssoc(_, Vars, Result):-
	ocl_variable(Vars,1,Result).
nAttribute10restrictedAssoc(Instances, Vars, Result):-
	append(_, [Para], Vars),
	Para = [X_ClassA,_,_,X_RoleB,_,_,_,_],
	nVariable9restrictedAssoc(Instances, Vars, Object),
	ocl_attributeCall(Instances,X_ClassA,X_RoleB, Object, Result).
nVariable11restrictedAssoc(_, Vars, Result):-
	ocl_variable(Vars,1,Result).
nNavigation12restrictedAssoc(Instances, Vars, Result):-
	append(_, [Para], Vars),
	Para = [_,_,_,_,X_AssocBC,X_RoleC,RoleCB,_],
	nVariable11restrictedAssoc(Instances, Vars, Value1),
	ocl_navigation(Instances,X_AssocBC,RoleCB,X_RoleC, Value1, Result).
ncollect13restrictedAssoc(Instances, Vars, Result):-
	nAttribute10restrictedAssoc(Instances, Vars, Value1),
	ocl_bag_collect(Instances, Vars, Value1, nNavigation12restrictedAssoc, Result).
nexcludesAll14restrictedAssoc(Instances, Vars, Result):-
	ncollect8restrictedAssoc(Instances, Vars, Value1),
	ncollect13restrictedAssoc(Instances, Vars, Value2),
	ocl_bag_excludesAll(Value1, Value2, Result).
nimplies15restrictedAssoc(Instances, Vars, Result):-
	ocl_implies(Instances, Vars, nAttribute3restrictedAssoc, nexcludesAll14restrictedAssoc, Result).
nforAll16restrictedAssoc(Instances, Vars, Result):-
	nallInstances1restrictedAssoc(Instances, Vars, Value1),
	ocl_col_forAll(Instances, Vars, Value1, nimplies15restrictedAssoc, Result).
restrictedAssoc(Instances,Para, Result):-
	nforAll16restrictedAssoc(Instances, [Para], Result).
%--------------------------------------------------------------------------------------
%--Applying OneReferee Pattern----------------------------------------------------
%--------------------------------------------------------------------------------------
apply_oneReferee(SOK, SNOK, Para):-
% Para = [X_Class,X_Role,X_Attr]
  getLocalPara_oneReferee(Para,LocalPara),
  %--Ensuring the invariant accepts SOK----------
  ( foreach(SnapshotOk, SOK),
    param(LocalPara)
    do
      oneReferee(SnapshotOk, LocalPara, 1)
  ),
  %--Ensuring the invariant rejects SNOK---------
  ( foreach(SnapshotNok, SNOK),
    param(LocalPara)
    do
      oneReferee(SnapshotNok, LocalPara, 0)
  ).
%--Get the LocalPara-----------------------------
getLocalPara_oneReferee(Para,LocalPara):-
  Para = [X_Class,X_Role,X_Attr],
  LocalPara = [X_Class,X_Attr,Assoc,X_Role,Role2,ClsB],
  attType(ClsB, X_Attr,"Boolean"),
  is_predicate(roleType/3),
  roleType(Assoc, Role2, X_Class),
  roleType(Assoc, X_Role, ClsB),
  X_Role \= Role2.
%--Writing the OneReferee template---------
write_oneReferee(Para, Inv) :-
  Para = [X_Class,X_Role,X_Attr],
  sprintf(OCLInv,"context %w inv oneReferee_%w:....%w::allInstances()->forAll(s | s.%w->size() = 0 or s.%w->select(v | v.%w = true)->size() = 1)",[X_Class,X_Role,X_Class,X_Role,X_Role,X_Attr]),
  sprintf(ParaStr,"['%w','%w','%w']",[X_Class,X_Role,X_Attr]),
  Inv = [ParaStr, OCLInv].
%--Encoding the OCL OneReferee template------
nallInstances1oneReferee(Instances, [Para], Result):-
	Para = [X_Class,_,_,_,_,_],
	ocl_allInstances(Instances, X_Class, Result).
nVariable2oneReferee(_, Vars, Result):-
	ocl_variable(Vars,1,Result).
nNavigation3oneReferee(Instances, Vars, Result):-
	append(_, [Para], Vars),
	Para = [_,_,Assoc,X_Role,Role2,_],
	nVariable2oneReferee(Instances, Vars, Value1),
	ocl_navigation(Instances,Assoc,Role2,X_Role, Value1, Result).
nsize4oneReferee(Instances, Vars, Result):-
	nNavigation3oneReferee(Instances, Vars, Value1),
	ocl_set_size(Value1, Result).
nConstant5oneReferee(_, _, Result):-
	Result=0.
nequals6oneReferee(Instances, Vars, Result):-
	ocl_int_equals(Instances, Vars, nsize4oneReferee, nConstant5oneReferee, Result).
nVariable7oneReferee(_, Vars, Result):-
	ocl_variable(Vars,1,Result).
nNavigation8oneReferee(Instances, Vars, Result):-
	append(_, [Para], Vars),
	Para = [_,_,Assoc,X_Role,Role2,_],
	nVariable7oneReferee(Instances, Vars, Value1),
	ocl_navigation(Instances,Assoc,Role2,X_Role, Value1, Result).
nVariable9oneReferee(_, Vars, Result):-
	ocl_variable(Vars,1,Result).
nAttribute10oneReferee(Instances, Vars, Result):-
	append(_, [Para], Vars),
	Para = [_,X_Attr,_,_,_,ClsB],
	nVariable9oneReferee(Instances, Vars, Object),
	ocl_attributeCall(Instances,ClsB,X_Attr, Object, Result).
nConstant11oneReferee(_, _, Result):-
	Result=1.
nequals12oneReferee(Instances, Vars, Result):-
	ocl_boolean_equals(Instances, Vars, nAttribute10oneReferee, nConstant11oneReferee, Result).
nselect13oneReferee(Instances, Vars, Result):-
	nNavigation8oneReferee(Instances, Vars, Value1),
	ocl_set_select(Instances, Vars, Value1, nequals12oneReferee, Result).
nsize14oneReferee(Instances, Vars, Result):-
	nselect13oneReferee(Instances, Vars, Value1),
	ocl_set_size(Value1, Result).
nConstant15oneReferee(_, _, Result):-
	Result=1.
nequals16oneReferee(Instances, Vars, Result):-
	ocl_int_equals(Instances, Vars, nsize14oneReferee, nConstant15oneReferee, Result).
nor17oneReferee(Instances, Vars, Result):-
	ocl_or(Instances, Vars, nequals6oneReferee, nequals16oneReferee, Result).
nforAll18oneReferee(Instances, Vars, Result):-
	nallInstances1oneReferee(Instances, Vars, Value1),
	ocl_col_forAll(Instances, Vars, Value1, nor17oneReferee, Result).
oneReferee(Instances, Para, Result):-
	nforAll18oneReferee(Instances, [Para], Result).
%--------------------------------------------------------------------------------------
%--Applying AttrRel2 Pattern----------------------------------------------------
%--------------------------------------------------------------------------------------
apply_attrRel2(SOK, SNOK, Para):-
% Para = [X_Class,X_Role,X_Attr]
  getLocalPara_attrRel2(Para,LocalPara),  
  computeValue(SNOK,LocalPara),
  %--Ensuring the invariant accepts SOK----------
  ( foreach(SnapshotOk, SOK),
    param(LocalPara)
    do
      attrRel2(SnapshotOk, LocalPara, 1)
  ).
  %--Ensuring the invariant rejects SNOK---------
  %( foreach(SnapshotNok, SNOK),
  %  param(LocalPara)
  %  do
  %    attrRel2(SnapshotNok, LocalPara, 0)
  %).
%--Get the LocalPara-----------------------------
getLocalPara_attrRel2(Para,LocalPara):-
  Para = [X_Class,X_Role,X_Attr1,X_Attr2,Value],
  LocalPara = [X_Class,X_Attr1,ClsB,X_Attr2,Assoc,X_Role,Role2,Value],
  attType(X_Class, X_Attr1,"Integer"),
  attType(ClsB, X_Attr2,"Integer"),
  is_predicate(roleType/3),
  roleType(Assoc, Role2, X_Class),
  roleType(Assoc, X_Role, ClsB),
  X_Role \= Role2.
%--Writing the AttrRel2 template---------
write_attrRel2(Para, Inv) :-
  Para = [X_Class,X_Role,X_Attr1,X_Attr2,Value],
  ( Value == 0 ->
    sprintf(OCLInv,"context %w inv attrRel2_%w_%w_%w:....self.%w->forAll(v | self.%w >= v.%w )",[X_Class,X_Role,X_Attr1,X_Attr2,X_Role,X_Attr1,X_Attr2])
  ;
    number_string(Value,StrValue),
    sprintf(OCLInv,"context %w inv attrRel2_%w_%w_%w:....self.%w->forAll(v | self.%w >= (v.%w + %w) )",[X_Class,X_Role,X_Attr1,X_Attr2,X_Role,X_Attr1,X_Attr2,StrValue])
  ),  
  sprintf(ParaStr,"['%w','%w','%w','%w',%w]",[X_Class,X_Role,X_Attr1,X_Attr2,Value]),
  Inv = [ParaStr, OCLInv].
%--Compute a possible Value = Max(Min(d(Attr1,Attr2)))------
computeValue(SNOK,LocalPara):-
  LocalPara = [_,_,_,_,_,_,_,Value],
  ( foreach(Snok, SNOK),
    fromto(-29999,In,Out,Value1),
    param(LocalPara)
    do
      computeMinDistance(Snok, LocalPara, Min),
      ( In #< Min -> Out = Min
      ; Out = In
      )    
  ),
  Value1 \= 29999,
  Value1 \= -29999,
  Value is Value1 + 1.
%--Compute the minimum distance Min(d(Attr1,Attr2))-----
  computeMinDistance(Snok,LocalPara,Min) :- 
    LocalPara = [X_Class,X_Attr1,ClsB,X_Attr2,Assoc,X_Role,Role2,_],
    ocl_allInstances(Snok, X_Class, XClsObjects),
    ( foreach(XClsObject,XClsObjects),
      fromto(2999,In,Out,Min),
      param(Snok,X_Class,X_Attr1,ClsB,X_Attr2,Assoc,X_Role,Role2)
      do
        ocl_attributeCall(Snok,X_Class,X_Attr1, XClsObject, Attr1),
        Attr1 \= oclUndefined,
        ocl_navigation(Snok,Assoc,Role2,X_Role, XClsObject, BObjects),
        ( foreach(BObject,BObjects),
          fromto(In,In1,Out1,Min1),
          param(Snok,ClsB,X_Attr2,Attr1)
          do
            ocl_attributeCall(Snok,ClsB,X_Attr2, BObject, Attr2),
            Attr2 \= oclUndefined,
            D is Attr1 - Attr2,
            ( D #< In1 -> Out1 = D
            ; Out1 = In1
            )
        ),
        ( Min1 == In -> Out = In
        ; Out = Min1)
    ).
%--Encoding the OCL AttrRel2 template------
nallInstances1attrRel2(Instances, [Para], Result):-
	%Para = [X_Class,X_Attr1,ClsB,X_Attr2,Assoc,X_Role,Role2,Value],
	Para = [X_Class,_,_,_,_,_,_,_],
	ocl_allInstances(Instances, X_Class, Result).
nVariable2attrRel2(_, Vars, Result):-
	ocl_variable(Vars,1,Result).
nNavigation3attrRel2(Instances, Vars, Result):-
	append(_, [Para], Vars),
	Para = [_,_,_,_,Assoc,X_Role,Role2,_],
	nVariable2attrRel2(Instances, Vars, Value1),
	ocl_navigation(Instances,Assoc,Role2,X_Role, Value1, Result).
nVariable4attrRel2(_, Vars, Result):-
	ocl_variable(Vars,2,Result).
nAttribute5attrRel2(Instances, Vars, Result):-
	append(_, [Para], Vars),
	Para = [X_Class,X_Attr1,_,_,_,_,_,_],
	nVariable4attrRel2(Instances, Vars, Object),
	ocl_attributeCall(Instances,X_Class,X_Attr1, Object, Result).
nVariable6attrRel2(_, Vars, Result):-
	ocl_variable(Vars,1,Result).
nAttribute7attrRel2(Instances, Vars, Result):-
	append(_, [Para], Vars),
	Para = [_,_,ClsB,X_Attr2,_,_,_,_],
	nVariable6attrRel2(Instances, Vars, Object),
	ocl_attributeCall(Instances,ClsB,X_Attr2, Object, Result).
nConstant8attrRel2(_, Vars, Result):-
	append(_, [Para], Vars),
	Para = [_,_,_,_,_,_,_,Value],
	Result=Value.
nplus9attrRel2(Instances, Vars, Result):-
	ocl_int_plus(Instances, Vars, nAttribute7attrRel2, nConstant8attrRel2, Result).
ngreater_than10attrRel2(Instances, Vars, Result):-
	ocl_int_greater_equal(Instances, Vars, nAttribute5attrRel2, nplus9attrRel2, Result).
nforAll11attrRel2(Instances, Vars, Result):-
	nNavigation3attrRel2(Instances, Vars, Value1),
	ocl_col_forAll(Instances, Vars, Value1, ngreater_than10attrRel2, Result).
nforAll12attrRel2(Instances, Vars, Result):-
	nallInstances1attrRel2(Instances, Vars, Value1),
	ocl_col_forAll(Instances, Vars, Value1, nforAll11attrRel2, Result).
attrRel2(Instances, Para, Result):-
	nforAll12attrRel2(Instances, [Para], Result).
%--------------------------------------------------------------------------------------
%--Applying the CountObject1 Pattern-------------------------------------------------------
%--------------------------------------------------------------------------------------
apply_countObject1(SOK, SNOK, Para):-  
  Para = [X_Class, X_Attr, _],
  attType(X_Class, X_Attr, "Boolean"),
  computeInterval_countObject1(SOK, SNOK, Para),
  %--Ensuring the invariant accepts SOK----------
  (foreach(SOk, SOK),
   param(Para)
   do
     countObject1(SOk, Para, 1)
  ),
  %--Ensuring the invariant rejects SNOK---------
  (foreach(SNok, SNOK),
   param(Para)
   do
     countObject1(SNok, Para, 0)
  ).
%--Get the LocalPara-----------------------------
getLocalPara_countObject1(Para,LocalPara):-
  LocalPara = Para.
%--Writing the countObject1 pattern template----------
write_countObject1(Para, Inv) :-
  Para = [X_Class, X_Attr, X_Interval],
  X_Interval = clsInterval{oid:_,left: L,right: R},
  ( L #= 0, R #= 29999 -> sprintf(OCLInv,"context %w inv countObject1_%w:....%w::allInstances()->exists(a | a.%w = true)",[X_Class,X_Attr,X_Class,X_Attr])
  ; L #< 0, R \= 29999 -> sprintf(OCLInv,"context %w inv countObject1_%w:....%w::allInstances()->select(a | a.%w = true)->size() < %w",[X_Class,X_Attr,X_Class,X_Attr,R])
  ; L #> 0, R #= 29999 -> sprintf(OCLInv,"context %w inv countObject1_%w:....%w < %w::allInstances()->select(a | a.%w = true)->size()",[X_Class,X_Attr,L, X_Class,X_Attr])
  ; L #>= 0, R \= 29999 -> sprintf(OCLInv,"context %w inv countObject1_%w:....let S:Integer = %w::allInstances()->select(a | a.%w = true)->size() in....%w < T and T < %w",[X_Class,X_Attr,X_Class,X_Attr,L,R])
  ),
  sprintf(ParaStr,"['%w','%w',%w]",[X_Class,X_Attr,X_Interval]),
  Inv = [ParaStr, OCLInv].
%----------------------------------------------------
computeInterval_countObject1(SOK, SNOK, Para) :-
  Para = [_,_,X_Interval],
  ( foreach(Sok,SOK),
    fromto([],In1,Out1,SokList),
    param(Para)
    do
      nsize7countObject1(Sok, [Para], Val),
      Val \= oclUndefined,	
      Out1 = [ Val | In1 ]
  ),
  ( foreach(Snok,SNOK),
    fromto([],In2,Out2,SnokList),
    param(Para)
    do
      nsize7countObject1(Snok, [Para], Val),
      Val \= oclUndefined,	
      Out2 = [ Val | In2 ]
  ),
  %writeln(SokList),
  %writeln(SnokList),
  subtract(SnokList, SokList, SnokList_New),
  computeIntervals(SokList, SnokList_New, [X_Interval]).

%--Encoding the OCL countObject1 template------------
%LocalPara = [X_Class,X_Attr,X_Interval]
nallInstances1countObject1(Instances, [Para], Result):-
	Para = [X_Class,_,_],
	ocl_allInstances(Instances, X_Class, Result).
nVariable2countObject1(_, Vars, Result):-
	ocl_variable(Vars,1,Result).
nAttribute3countObject1(Instances, Vars, Result):-
	append(_, [Para], Vars),
	Para = [X_Class,X_Attr,_],
	nVariable2countObject1(Instances, Vars, Object),
	ocl_attributeCall(Instances,X_Class,X_Attr, Object, Result).
nConstant4countObject1(_, _, Result):-
	Result=1.
nequals5countObject1(Instances, Vars, Result):-
	ocl_boolean_equals(Instances, Vars, nAttribute3countObject1, nConstant4countObject1, Result).
nselect6countObject1(Instances, Vars, Result):-
	nallInstances1countObject1(Instances, Vars, Value1),
	ocl_set_select(Instances, Vars, Value1, nequals5countObject1, Result).
nsize7countObject1(Instances, Vars, Result):-
	nselect6countObject1(Instances, Vars, Value1),
	ocl_set_size(Value1, Result).
nConstant8countObject1(_, Vars, Result):-
	append(_, [Para], Vars),
	Para = [_,_,clsInterval{oid:_,left: L,right: _}],
	Result = L.
nVariable9countObject1(_, Vars, Result):-
	ocl_variable(Vars,-1,Result).
nless_than10countObject1(Instances, Vars, Result):-
	ocl_int_less_than(Instances, Vars, nConstant8countObject1, nVariable9countObject1, Result).
nVariable11countObject1(_, Vars, Result):-
	ocl_variable(Vars,-1,Result).
nConstant12countObject1(_, Vars, Result):-
	append(_, [Para], Vars),
	Para = [_,_,clsInterval{oid:_,left: _,right: R}],
	Result = R.
nless_than13countObject1(Instances, Vars, Result):-
	ocl_int_less_than(Instances, Vars, nVariable11countObject1, nConstant12countObject1, Result).
nand14countObject1(Instances, Vars, Result):-
	ocl_and(Instances, Vars, nless_than10countObject1, nless_than13countObject1, Result).
countObject1(Instances,Para,Result):-
	nsize7countObject1(Instances, [Para], Val),
	ocl_and(Instances, [Val,Val,Para], nless_than10countObject1, nless_than13countObject1, Result).
%--------------------------------------------------------------------------------------
%--Applying All of Patterns------------------------------------------------------------
%--------------------------------------------------------------------------------------
patternIndex( "uniqueAttr",  		1).
patternIndex( "intervalInv", 		2).
patternIndex( "cardInv",     		3).
patternIndex( "nonSelfInc",  		4).
patternIndex( "attrRel",     		5).
patternIndex( "maxCard",     		6).
patternIndex( "requiredInclusion",	7).
patternIndex( "restrictedAssoc",	8).
patternIndex( "oneReferee",		9).
patternIndex( "attrRel2",		10).
patternIndex( "countObject1",		11).
%----patterns combinable-------------------
polyPattern(Pat):- member(Pat,[2,3]).
%----elems4labeling(Pat,Cls,Link,Attr)-----
elems4labeling(1,[1],[],[1]).
elems4labeling(2,[1],[],[1]).
elems4labeling(3,[1,6],[2],[]).
elems4labeling(4,[1,5],[2],[]).
elems4labeling(5,[1,2],[3],[1,2]).
elems4labeling(6,[1,6],[3],[1]).
elems4labeling(7,[1,8],[2,5],[]).
elems4labeling(8,[1,8],[1,5],[1]).
elems4labeling(9,[1,6],[3],[6]).
%LocalPara = [X_Class,X_Attr1,ClsB,X_Attr2,Assoc,X_Role,Role2,_]
elems4labeling(10,[1,3],[5],[1,3]).
%LocalPara = [X_Class,X_Attr]
elems4labeling(11,[1],[],[1]).

apply_all(SOK, [], PATTERN, INV) :-
  ( foreach(Pattern, PATTERN),
    fromto([],In,Out,INV), 
    param(SOK)
    do
      applyPattern(Pattern, SOK, [], Para),      
      Out = [ [Pattern,Para] | In]
  ),!.


apply_all(SOK, SNOK, PATTERN, INV) :-
  sort(SNOK, SNOK0),
  partition(SNOK0, SnokGroups),
  ( foreach(SnokSet, SnokGroups),
    fromto([],In,Out,INV), 
    param(SOK,PATTERN)
    do
      member(Pattern, PATTERN),
      applyPattern(Pattern, SOK, SnokSet, Para),
      uncombined(Pattern, Para, In),      
      Out = [ [Pattern,Para] | In]
  ).

partition([],[]).
partition([L|Ls0], [[L|G]|Gs]) :-
  phrase(group(Ls0, L, Ls1), G),
  partition(Ls1, Gs).

group(Ls, _, Ls) --> {true}.

group(Ls0, PrevElem, Ls) --> [CurrElem],
{ delete(CurrElem, Ls0, Ls1), PrevElem @< CurrElem },
group(Ls1, CurrElem, Ls).

getPatterns(X):-
  findall(Pat, patternIndex(_, Pat), X).

applyPattern(Pat, SOK, SNOK, Para) :-
  patternIndex(PatName, Pat),
  concat_strings("apply_", PatName, TmpName),
  term_string(PatApply, TmpName),
  FApply =.. [PatApply, SOK, SNOK, Para],
  call(FApply).

writeInv(Pat, Para, Inv) :-
  patternIndex(PatName, Pat),
  concat_strings("write_", PatName, TmpName),
  term_string(WriteInv, TmpName),
  FApply =.. [WriteInv, Para, Inv],
  call(FApply).
%---Create a file named Filename to write invs.
writeINV(FileName, INVList) :-
  open(FileName, write, Stream, [end_of_line(crlf)]),
  length(INVList,Size),
  writeln(Stream, Size),
  ( foreach(INV, INVList),
    param(Stream)
    do(
      length(INV,Size),
      writeln(Stream, Size),
      ( foreach(Inv, INV),
        param(Stream)
        do(
          Inv = [Pat, Para],
	  patternIndex(PatName, Pat),
          writeInv(Pat, Para, [ParaStr, OCLInv]),
	  elems4labeling(Pat,Cls,Link,Attr),
	  getLocalPara(Pat,Para,LocalPara),
	  length(Cls,NumCls),
	  length(Link,NumLink),
	  length(Attr,NumAttr),
          write(Stream, Pat),
          write(Stream, "\t"),   
          write(Stream, PatName),
          write(Stream, "\t"),         
          write(Stream, ParaStr),
          write(Stream, "\t"),      
          write(Stream, OCLInv),
	  write(Stream, "\t"),
	  write(Stream, NumCls),
	  ( foreach(Cidx,Cls),
	    param(Stream,LocalPara)
	    do
	      write(Stream, "\t"),
	      nth1(Cidx,LocalPara,Cstr),
	      write(Stream, Cstr)
	  ),
	  write(Stream, "\t"),
	  write(Stream, NumLink),
	  ( foreach(Lidx,Link),
	    param(Stream,LocalPara)
	    do
	      write(Stream, "\t"),
	      nth1(Lidx,LocalPara,Lstr0),
	      ( is_predicate(roleAssocCls/3)
	        -> ( roleAssocCls(Lstr0,_,_)
		     -> concat_strings("AssocCls_", Lstr0, Lstr)
		     ; Lstr = Lstr0
		   )
  		; Lstr = Lstr0
	      ),	      
	      write(Stream, Lstr)
	  ),
	  write(Stream, "\t"),
	  write(Stream, NumAttr),
	  ( foreach(Aidx,Attr),
	    param(Stream,LocalPara)
	    do
	      write(Stream, "\t"),
	      nth1(Aidx,LocalPara,Astr),
	      write(Stream, Astr)
	  ),
	  writeln(Stream, "")
        )
      )
    )
  ),
  close(Stream).
%-----------------------------------------------------------------------------
writeINV(INV) :-
  writeln("---------------------------"),
  ( foreach(Inv, INV)
    do
      Inv = [Pat, Para],
      patternIndex(PatName, Pat),
      writeInv(Pat, Para, [ParaStr, OCLInv]),
      write(PatName),
      write("\t"),         
      write(ParaStr),
      write("\t"),      
      writeln(OCLInv)
  ),
  writeln("---------------------------").
%---Get the LocalPara--------------------------------------------------
getLocalPara(Pat,Para,LocalPara):-
  patternIndex(PatName, Pat),
  concat_strings("getLocalPara_", PatName, TmpName),
  term_string(GetLocalPara, TmpName),
  FApply =.. [GetLocalPara, Para, LocalPara],
  call(FApply).
%---Check combination of patterns---------------------
uncombined(Pat, Para, ParaList):-
  member([Pat,Para], ParaList)
  -> fail;
  ( polyPattern(Pat),    
    patternIndex(PatName, Pat),
    concat_strings("combined_", PatName, TmpName),
    term_string(Combined, TmpName),
    FApply =.. [Combined, Pat, Para, ParaList],
    call(FApply)
    -> fail;
    true
  ).
