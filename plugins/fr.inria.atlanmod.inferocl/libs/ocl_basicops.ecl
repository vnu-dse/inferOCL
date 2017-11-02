%
% ECLiPSe libraries
%
:- lib(ic).     % Interval constraints
:- lib(apply).  % Using variables as functors

% 2007/05/15:
% - Updated ocl_attributeCall to deal with inheritance (access attributes
%   defined in a superclass)
% 2007/07/06:
% - Updated ocl_navigation and ocl_attributeCall to avoid a bug
% when navigation returned a single object
% 2007/07/10:
% - Updated ocl_navigation to speed up the cases where the
% navigation returns an empty list 
% 2009/06/12
% - Added support for direct object comparison
% 2013/09/27:
% - Added support for OclUndefined
% 2013/11/17:
% - Added "resume" predicates as checking is_oclUndefined(Result) was done.

%------------------------------------------------------------------------------
%
% Logical operators - not, and, or, xor, implies, boolean equality, boolean
% disequality
% 
%------------------------------------------------------------------------------

%ocl_not(Instances, Vars, Predicate, Result) :-
%   Result is the logical "not" of the result of
%   a predicate

ocl_not(Instances, Vars, Predicate, Result) :-
   apply(Predicate, [Instances, Vars, TruthValue]),
   ocl_not_resume(TruthValue, Result).

delay ocl_not_resume(TruthValue, _) if nonground(TruthValue).
ocl_not_resume(TruthValue, Result) :-
   ( is_oclUndefined(TruthValue)
     -> Result = oclUndefined;
     (
       Result::0..1,
       ic:neg(TruthValue, Result)
     )
   ).

%ocl_and(Instances, Vars, Pred1, Pred2, Result) :-
%   Result is the logical "and" among the results of the
%   two predicates

ocl_and(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, TruthValue1]),
   apply(Pred2, [Instances, Vars, TruthValue2]),
   ocl_and_resume(TruthValue1,TruthValue2, Result).

delay ocl_and_resume(TruthValue1,TruthValue2, _) if nonground([TruthValue1,TruthValue2]).
ocl_and_resume(X,_, oclUndefined) :- is_oclUndefined(X),!.
ocl_and_resume(_,X, oclUndefined) :- is_oclUndefined(X),!.
ocl_and_resume(TruthValue1,TruthValue2, Result) :-
   Result::0..1,
   ic:and(TruthValue1, TruthValue2, Result).

%ocl_or(Instances, Vars, Pred1, Pred2, Result) :-
%   Result is the logical "or" among the results of the
%   two predicates

ocl_or(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, TruthValue1]),
   apply(Pred2, [Instances, Vars, TruthValue2]),
   ocl_or_resume(TruthValue1,TruthValue2, Result).

delay ocl_or_resume(TruthValue1,TruthValue2, _) if nonground([TruthValue1,TruthValue2]).
ocl_or_resume(X,_, oclUndefined) :- is_oclUndefined(X),!.
ocl_or_resume(_,X, oclUndefined) :- is_oclUndefined(X),!.
ocl_or_resume(TruthValue1,TruthValue2, Result) :-
   Result::0..1,
   ic:or(TruthValue1, TruthValue2, Result).

%ocl_xor(Instances, Vars, Pred1, Pred2, Result) :-
%   Result is the exclusive "or" among the results of the
%   two predicates

ocl_xor(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, TruthValue1]),
   apply(Pred2, [Instances, Vars, TruthValue2]),
   ocl_xor_resume(TruthValue1,TruthValue2, Result).

delay ocl_xor_resume(TruthValue1,TruthValue2, _) if nonground([TruthValue1,TruthValue2]).
ocl_xor_resume(X,_, oclUndefined) :- is_oclUndefined(X),!.
ocl_xor_resume(_,X, oclUndefined) :- is_oclUndefined(X),!.
ocl_xor_resume(TruthValue1,TruthValue2, Result) :-
   Result::0..1,
   xor3(TruthValue1, TruthValue2, Result).

xor3(X, Y, Z) :- ic:neg(X, X1), ic:neg(Y, Y1), ic:and(X, Y1, Z1),
                 ic:and(X1, Y, Z2), ic:or(Z1, Z2, Z).

%ocl_implies(Instances, Vars, Pred1, Pred2, Result) :-
%   Result is true if Pred1 implies Pred2, and it is
%   false otherwise
% hanhdd

ocl_implies(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, TruthValue1]),
   apply(Pred2, [Instances, Vars, TruthValue2]),
   ocl_implies_resume(TruthValue1,TruthValue2, Result).

delay ocl_implies_resume(TruthValue1,TruthValue2, _) if nonground([TruthValue1,TruthValue2]).
ocl_implies_resume(TruthValue1,_, oclUndefined) :- is_oclUndefined(TruthValue1),!.
ocl_implies_resume(0,_, 1) :- !.
ocl_implies_resume(_, TruthValue2, oclUndefined) :- is_oclUndefined(TruthValue2),!.
ocl_implies_resume(TruthValue1,TruthValue2, Result) :-
  Result::0..1,
  =>(TruthValue1, TruthValue2, Result).

%ocl_boolean_equals(Instances, Vars, Pred1, Pred2, Result) :-
%   Result is true if Pred1 is equal to Pred2, and it is
%   false otherwise

ocl_boolean_equals(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, TruthValue1]),
   apply(Pred2, [Instances, Vars, TruthValue2]),
   ocl_boolean_equals_resume(TruthValue1,TruthValue2, Result).

delay ocl_boolean_equals_resume(TruthValue1,TruthValue2, _) if nonground([TruthValue1,TruthValue2]).
ocl_boolean_equals_resume(TruthValue1,TruthValue2, Result) :-
   ( is_oclUndefined(TruthValue1)
     -> Result = oclUndefined;
     ( is_oclUndefined(TruthValue2)
       -> Result = oclUndefined;
       (    
         Result::0..1,
         #=(TruthValue1, TruthValue2, Result)
       )
     )
   ).

%ocl_boolean_not_equals(Instances, Vars, Pred1, Pred2, Result) :-
%   Result is true if Pred1 is not equal to Pred2, and it is
%   false otherwise

ocl_boolean_not_equals(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, TruthValue1]),
   apply(Pred2, [Instances, Vars, TruthValue2]),
   ocl_boolean_not_equals_resume(TruthValue1,TruthValue2, Result).

delay ocl_boolean_not_equals_resume(TruthValue1,TruthValue2, _) if nonground([TruthValue1,TruthValue2]).
ocl_boolean_not_equals_resume(TruthValue1,TruthValue2, Result) :-
   ( is_oclUndefined(TruthValue1)
     -> Result = oclUndefined;
     ( is_oclUndefined(TruthValue2)
       -> Result = oclUndefined;
       (    
         Result::0..1,
         #\=(TruthValue1, TruthValue2, Result)
       )
     )
   ).


%------------------------------------------------------------------------------
%
% Integer arithmetic and relational operators - minus, plus, times, div, 
% division, modulo, min, max, abs, <, >, <=, >=, ==, <>
% 
%------------------------------------------------------------------------------

%ocl_int_unary_minus(Instances, Vars, Predicate, Result) :-
%   Let X be the integer result of Predicate 
%   Result is -X

ocl_int_unary_minus(Instances, Vars, Predicate, Result) :-
   apply(Predicate, [Instances, Vars, X]),
   ocl_int_unary_minus_resume(X,Result).

delay ocl_int_unary_minus_resume(X,_) if nonground(X).
ocl_int_unary_minus_resume(X,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;    
     Result #= -X
   ).

%ocl_int_binary_minus(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the integer result of Pred1
%   Let Y be the integer result of Pred2 
%   Result is X-Y

ocl_int_binary_minus(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_int_binary_minus_resume(X,Y,Result).

delay ocl_int_binary_minus_resume(X,Y,_) if nonground([X,Y]).
ocl_int_binary_minus_resume(X,Y,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     ( is_oclUndefined(Y)
       -> Result = oclUndefined;
       (    
         Result #= X-Y
       )
     )
   ).

%ocl_int_plus(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the integer result of Pred1
%   Let Y be the integer result of Pred2 
%   Result is X-Y

ocl_int_plus(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_int_plus_resume(X,Y,Result).

delay ocl_int_plus_resume(X,Y,_) if nonground([X,Y]).
ocl_int_plus_resume(X,Y,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     ( is_oclUndefined(Y)
       -> Result = oclUndefined;
       (    
         Result #= X+Y
       )
     )
   ).

%ocl_int_times(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the integer result of Pred1
%   Let Y be the integer result of Pred2 
%   Result is X*Y

ocl_int_times(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_int_times_resume(X,Y,Result).

delay ocl_int_times_resume(X,Y,_) if nonground([X,Y]).
ocl_int_times_resume(X,Y,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     ( is_oclUndefined(Y)
       -> Result = oclUndefined;
       ( 
         Result #= X*Y
       )
     )
   ).


%ocl_int_division(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the integer result of Pred1
%   Let Y be the integer result of Pred2 
%   Result is X / Y, the real division of X and Y
ocl_int_division(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_int_division_resume(X,Y,Result).

delay ocl_int_division_resume(X,Y,_) if nonground([X,Y]).
ocl_int_division_resume(X,Y,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     ( is_oclUndefined(Y)
       -> Result = oclUndefined;
       (    
         Result $= X / Y
       )
     )
   ).


%ocl_int_div(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the integer result of Pred1
%   Let Y be the integer result of Pred2 
%   Result is X div Y, the integer division of X and Y

ocl_int_div(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_int_div_resume(X,Y,Result).

delay ocl_int_div_resume(X,Y,_) if nonground([X,Y]).
ocl_int_div_resume(X,Y,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     ( is_oclUndefined(Y)
       -> Result = oclUndefined;
       (    
         Result #= X div Y
       )
     )
   ).


%ocl_int_mod(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the integer result of Pred1
%   Let Y be the integer result of Pred2 
%   Result is X mod Y. This implementation uses the definition
%   of modulo provided in the OCL standard instead of the
%   built-in mod operator. 
%   X mod Y = (X - (X div Y)*Y)

ocl_int_mod(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_int_mod_resume(X,Y,Result).

delay ocl_int_mod_resume(X,Y,_) if nonground([X,Y]).
ocl_int_mod_resume(X,Y,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     ( is_oclUndefined(Y)
       -> Result = oclUndefined;
       (    
         Result #= X - (X/Y)*Y
       )
     )
   ).


%ocl_int_min(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the integer result of Pred1
%   Let Y be the integer result of Pred2 
%   Result is min(X,Y), the minimum of both results

ocl_int_min(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_int_min_resume(X,Y,Result).

delay ocl_int_min_resume(X,Y,_) if nonground([X,Y]).
ocl_int_min_resume(X,_,oclUndefined) :- is_oclUndefined(X),!.
ocl_int_min_resume(_,X,oclUndefined) :- is_oclUndefined(X),!.
ocl_int_min_resume(X,Y,Result) :-
   Result #= min([X,Y]).

%ocl_int_max(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the integer result of Pred1
%   Let Y be the integer result of Pred2 
%   Result is max(X,Y), the maximum of both results

ocl_int_max(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_int_max_resume(X,Y,Result).

delay ocl_int_max_resume(X,Y,_) if nonground([X,Y]).
ocl_int_max_resume(X,_,oclUndefined) :- is_oclUndefined(X),!.
ocl_int_max_resume(_,X,oclUndefined) :- is_oclUndefined(X),!.
ocl_int_max_resume(X,Y,Result) :-
    Result #= max([X,Y]).

%ocl_int_abs(Instances, Vars, Predicate, Result) :-
%   Let X be the integer result of Predicate 
%   Result is |X|, the absolute value of X

ocl_int_abs(Instances, Vars, Predicate, Result) :-
   apply(Predicate, [Instances, Vars, X]),
   ocl_int_abs_resume(X,Result).

delay ocl_int_abs_resume(X,_) if nonground(X).
ocl_int_abs_resume(X,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     Result #= abs(X)
   ).

%ocl_int_equals(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the integer result of Pred1
%   Let Y be the integer result of Pred2 
%   Result is true iff X = Y

ocl_int_equals(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_int_equals_resume(X,Y,Result).

delay ocl_int_equals_resume(X,Y,_) if nonground([X,Y]).
ocl_int_equals_resume(X,_,oclUndefined) :- is_oclUndefined(X),!.
ocl_int_equals_resume(_,X,oclUndefined) :- is_oclUndefined(X),!.
ocl_int_equals_resume(X,Y,Result) :-
   Result::0..1,
   #=(X, Y, Result).


%ocl_int_not_equals(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the integer result of Pred1
%   Let Y be the integer result of Pred2 
%   Result is true iff X <> Y

ocl_int_not_equals(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_int_not_equals_resume(X,Y,Result).

delay ocl_int_not_equals_resume(X,Y,_) if nonground([X,Y]).
ocl_int_not_equals_resume(X,_,oclUndefined) :- is_oclUndefined(X),!.
ocl_int_not_equals_resume(_,X,oclUndefined) :- is_oclUndefined(X),!.
ocl_int_not_equals_resume(X,Y,Result) :-
  Result::0..1,
  #\=(X, Y, Result).

%ocl_int_greater_than(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the integer result of Pred1
%   Let Y be the integer result of Pred2 
%   Result is true iff X > Y

ocl_int_greater_than(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_int_greater_than_resume(X,Y,Result).

delay ocl_int_greater_than_resume(X,Y,_) if nonground([X,Y]).
ocl_int_greater_than_resume(X,Y,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     ( is_oclUndefined(Y)
       -> Result = oclUndefined;
       (    
         Result::0..1,
         #>(X, Y, Result)
       )
     )
   ).


% ocl_int_less_than(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the integer result of Pred1
%   Let Y be the integer result of Pred2 
%  Result is true iff X > Y

ocl_int_less_than(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_int_less_than_resume(X,Y,Result).

delay ocl_int_less_than_resume(X,Y,_) if nonground([X,Y]).
ocl_int_less_than_resume(X,_,oclUndefined) :- is_oclUndefined(X),!.
ocl_int_less_than_resume(_,X,oclUndefined) :- is_oclUndefined(X),!.
ocl_int_less_than_resume(X,Y,Result) :-
   Result::0..1,
   #<(X, Y, Result).


%ocl_int_greater_equal(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the integer result of Pred1
%   Let Y be the integer result of Pred2 
%   Result is true iff X >= Y

ocl_int_greater_equal(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_int_greater_equal_resume(X,Y,Result).

delay ocl_int_greater_equal_resume(X,Y,_) if nonground([X,Y]).
ocl_int_greater_equal_resume(X,Y,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     ( is_oclUndefined(Y)
       -> Result = oclUndefined;
       (    
         Result::0..1,
         #>=(X, Y, Result)
       )
     )
   ).


%ocl_int_less_equal(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the integer result of Pred1
%   Let Y be the integer result of Pred2 
%   Result is true iff X > Y

ocl_int_less_equal(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_int_less_equal_resume(X,Y,Result).

delay ocl_int_less_equal_resume(X,Y,_) if nonground([X,Y]).
ocl_int_less_equal_resume(X,Y,Result) :-
   ( is_oclUndefined(X) -> 
      Result = oclUndefined
   ; is_oclUndefined(Y) -> 
      Result = oclUndefined
   ; Result::0..1,
      #=<(X, Y, Result)     
   ).

%------------------------------------------------------------------------------
%
% Real arithmetic and relational operators - minus, plus, times, division, min, 
% max, abs, floor, round, <, >, >=, <=, ==, <>
% 
%------------------------------------------------------------------------------

%ocl_real_unary_minus(Instances, Vars, Predicate, Result) :-
%   Let X be the real result of Predicate 
%   Result is -X

ocl_real_unary_minus(Instances, Vars, Predicate, Result) :-
   apply(Predicate, [Instances, Vars, X]),
   ocl_real_unary_minus_resume(X,Result).

delay ocl_real_unary_minus_resume(X,_) if nonground(X).
ocl_real_unary_minus_resume(X,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     Result $= -X
   ).


%ocl_real_binary_minus(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the real result of Pred1
%   Let Y be the real result of Pred2 
%   Result is X-Y

ocl_real_binary_minus(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_real_binary_minus_resume(X,Y,Result).

delay ocl_real_binary_minus_resume(X,Y,_) if nonground([X,Y]).
ocl_real_binary_minus_resume(X,Y,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     ( is_oclUndefined(Y)
       -> Result = oclUndefined;
       (    
         Result $= X-Y
       )
     )
   ).


%ocl_real_plus(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the real result of Pred1
%   Let Y be the real result of Pred2 
%   Result is X-Y

ocl_real_plus(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_real_plus_resume(X,Y,Result).

delay ocl_real_plus_resume(X,Y,_) if nonground([X,Y]).
ocl_real_plus_resume(X,Y,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     ( is_oclUndefined(Y)
       -> Result = oclUndefined;
       (    
         Result $= X+Y
       )
     )
   ).


%ocl_real_times(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the real result of Pred1
%   Let Y be the real result of Pred2 
%   Result is X*Y

ocl_real_times(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_real_times_resume(X,Y,Result).

delay ocl_real_times_resume(X,Y,_) if nonground([X,Y]).
ocl_real_times_resume(X,Y,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     ( is_oclUndefined(Y)
       -> Result = oclUndefined;
       (    
         Result $= X*Y
       )
     )
   ).


%ocl_real_division(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the real result of Pred1
%   Let Y be the real result of Pred2 
%   Result is X / Y, the real division of X and Y
ocl_real_division(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_real_division_resume(X,Y,Result).

delay ocl_real_division_resume(X,Y,_) if nonground([X,Y]).
ocl_real_division_resume(X,Y,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     ( is_oclUndefined(Y)
       -> Result = oclUndefined;
       (    
         Result $= X / Y
       )
     )
   ).


%ocl_real_min(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the real result of Pred1
%   Let Y be the real result of Pred2 
%   Result is min(X,Y), the minimum of both results

ocl_real_min(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_real_min_resume(X,Y,Result).

delay ocl_real_min_resume(X,Y,_) if nonground([X,Y]).
ocl_real_min_resume(X,Y,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     ( is_oclUndefined(Y)
       -> Result = oclUndefined;
       (    
         Result $= min([X,Y])
       )
     )
   ).


%ocl_real_max(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the real result of Pred1
%   Let Y be the real result of Pred2 
%   Result is max(X,Y), the maximum of both results

ocl_real_max(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_real_max_resume(X,Y,Result).

delay ocl_real_max_resume(X,Y,_) if nonground([X,Y]).
ocl_real_max_resume(X,Y,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     ( is_oclUndefined(Y)
       -> Result = oclUndefined;
       (    
         Result $= max([X,Y])
       )
     )
   ).


%ocl_real_abs(Instances, Vars, Predicate, Result) :-
%   Let X be the real result of Predicate 
%   Result is |X|, the absolute value of X

ocl_real_abs(Instances, Vars, Predicate, Result) :-
   apply(Predicate, [Instances, Vars, X]),
   ocl_real_abs_resume(X,Result).

delay ocl_real_abs_resume(X,_) if nonground(X).
ocl_real_abs_resume(X,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     Result $= abs(X)
   ).


%ocl_real_floor(Instances, Vars, Predicate, Result) :-
%   Let X be the real result of Predicate 
%   Result is floor(X), rounding X down

ocl_real_floor(Instances, Vars, Predicate, Result) :-
   apply(Predicate, [Instances, Vars, X]),
   ocl_real_floor_resume(X,Result).

delay ocl_real_floor_resume(X,_) if nonground(X).
ocl_real_floor_resume(X,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     Result $= floor(X)
   ).


%ocl_real_round(Instances, Vars, Predicate, Result) :-
%   Let X be the real result of Predicate 
%   Result is floor(X), rounding X to the closest 
%   integer

ocl_real_round(Instances, Vars, Predicate, Result) :-
   apply(Predicate, [Instances, Vars, X]),
   ocl_real_round_resume(X,Result).

delay ocl_real_round_resume(X,_) if nonground(X).
ocl_real_round_resume(X,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     Result $= round(X)
   ).


%ocl_real_equals(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the real result of Pred1
%   Let Y be the real result of Pred2 
%   Result is true iff X = Y

ocl_real_equals(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_real_equals_resume(X,Y,Result).

delay ocl_real_equals_resume(X,Y,_) if nonground([X,Y]).
ocl_real_equals_resume(X,Y,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     ( is_oclUndefined(Y)
       -> Result = oclUndefined;
       (    
         Result::0..1,
         $=(X, Y, Result)
       )
     )
   ).


%ocl_real_not_equals(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the real result of Pred1
%   Let Y be the real result of Pred2 
%   Result is true iff X <> Y

ocl_real_not_equals(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_real_not_equals_resume(X,Y,Result).

delay ocl_real_not_equals_resume(X,Y,_) if nonground([X,Y]).
ocl_real_not_equals_resume(X,Y,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     ( is_oclUndefined(Y)
       -> Result = oclUndefined;
       (    
         Result::0..1,
         $\=(X, Y, Result)
       )
     )
   ).


%ocl_real_greater_than(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the real result of Pred1
%   Let Y be the real result of Pred2 
%   Result is true iff X > Y

ocl_real_greater_than(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_real_greater_than_resume(X,Y,Result).

delay ocl_real_greater_than_resume(X,Y,_) if nonground([X,Y]).
ocl_real_greater_than_resume(X,Y,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     ( is_oclUndefined(Y)
       -> Result = oclUndefined;
       (    
         Result::0..1,
         $>(X, Y, Result)
       )
     )
   ).


%ocl_real_less_than(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the real result of Pred1
%   Let Y be the real result of Pred2 
%   Result is true iff X > Y

ocl_real_less_than(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_real_less_than_resume(X,Y,Result).

delay ocl_real_less_than_resume(X,Y,_) if nonground([X,Y]).
ocl_real_less_than_resume(X,Y,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     ( is_oclUndefined(Y)
       -> Result = oclUndefined;
       (    
         Result::0..1,
         $<(X, Y, Result)
       )
     )
   ).


%ocl_real_greater_equal(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the real result of Pred1
%   Let Y be the real result of Pred2 
%   Result is true iff X >= Y

ocl_real_greater_equal(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_real_greater_equals_resume(X,Y,Result).

delay ocl_real_greater_equal_resume(X,Y,_) if nonground([X,Y]).
ocl_real_greater_equal_resume(X,Y,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     ( is_oclUndefined(Y)
       -> Result = oclUndefined;
       (    
         Result::0..1,
         $>=(X, Y, Result)
       )
     )
   ).


%ocl_real_less_equal(Instances, Vars, Pred1, Pred2, Result) :-
%   Let X be the real result of Pred1
%   Let Y be the real result of Pred2 
%   Result is true iff X > Y

ocl_real_less_equal(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_real_less_equal_resume(X,Y,Result).

delay ocl_real_less_equal_resume(X,Y,_) if nonground([X,Y]).
ocl_real_less_equal_resume(X,Y,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     ( is_oclUndefined(Y)
       -> Result = oclUndefined;
       (    
         Result::0..1,
         $=<(X, Y, Result)
       )
     )
   ).


%------------------------------------------------------------------------------
%
% String operations
% 
%------------------------------------------------------------------------------

ocl_string_concat(Instances, Vars, Pred1, Pred2, Result) :-
   apply(Pred1, [Instances, Vars, X]),
   apply(Pred2, [Instances, Vars, Y]),
   ocl_string_concat_resume(X,Y,Result).

delay ocl_string_concate_resume(X,Y,_) if nonground([X,Y]).
ocl_string_concate_resume(X,Y,Result) :-
   ( is_oclUndefined(X)
     -> Result = oclUndefined;
     ( is_oclUndefined(Y)
       -> Result = oclUndefined;
       (    
         str_len(Result,_),
  	 str_concat(X,Y,Result)
       )
     )
   ).


ocl_string_size(Instances, Vars, Pred, Result) :-
  apply(Pred, [Instances, Vars, X]),
   ocl_string_size_resume(X,Result).

delay ocl_string_size_resume(X,_) if nonground(X).
ocl_string_size_resume(X,Result) :-
  ( is_oclUndefined(X)
    -> Result = oclUndefined;
    str_len(X,Result)
  ).


ocl_string_not_equals(Instances, Vars, Pred1, Pred2, Result) :-
  apply(Pred1, [Instances, Vars, X]),
  apply(Pred2, [Instances, Vars, Y]),
   ocl_string_not_equals_resume(X,Y,Result).

delay ocl_string_not_equals_resume(X,Y,_) if nonground([X,Y]).
ocl_string_not_equals_resume(X,Y,Result) :-
  ( is_oclUndefined(X)
    -> Result = oclUndefined;
    ( is_oclUndefined(Y)
      -> Result = oclUndefined;
      (    
        Result :: 0..1,
	Z :: 0..1,
	Result #= 1 - Z,
	str_eq(X,Y,Z)
      )
    )
  ).


ocl_string_equals(Instances, Vars, Pred1, Pred2, Result) :-
  apply(Pred1, [Instances, Vars, X]),
  apply(Pred2, [Instances, Vars, Y]),
   ocl_string_equals_resume(X,Y,Result).

delay ocl_string_equals_resume(X,Y,_) if nonground([X,Y]).
ocl_string_equals_resume(X,Y,Result) :-
  ( is_oclUndefined(X)
    -> Result = oclUndefined;
    ( is_oclUndefined(Y)
      -> Result = oclUndefined;
      (    
	Result :: 0..1,
	str_eq(X,Y,Result)
      )
    )
  ).



delay ocl_if_then_else(_,_,C,_,_,_) if nonground(C).
ocl_if_then_else(_,_,oclUndefined,_,_,oclUndefined) :- !.
ocl_if_then_else(Instances,Vars,1,ThenPred,_,Result) :- 
   apply(ThenPred,[Instances,Vars,Result]).
ocl_if_then_else(Instances,Vars,0,_,ElsePred,Result) :- 
   apply(ElsePred,[Instances,Vars,Result]).


%------------------------------------------------------------------------------
%
% Base OCL operators - allInstances, VariableExp, navigation...
% 
%------------------------------------------------------------------------------

% ocl_oclIsKindOf(Instances, Obj, TypeName, Result) :-
%    Result is true if Obj is an instance of type TypeName
%    This will happen if the oid of Obj appear within the list of objects of 
%    class TypeName
%    TODO: This implementation does not consider collection types
%    Also, it assumes that we will not ask "isKindOf" for an object from a
%    different type hierarchy

delay ocl_oclIsKindOf(_, Obj, _, _) if var(Obj).
ocl_oclIsKindOf(Instances, Obj, TypeName, Result) :-
    is_oclUndefined(Obj)
    -> Result = oclUndefined;
    (
      % Get the list of oids in the class
      index(TypeName, Index),
      nth1(Index, Instances, ObjList),
      getOidList(ObjList, OidList),
      % Get the oid of the Object
      ocl_mustBeObject(Obj, Object),
      getOid(Object, Oid),
      % Result is true iff the oid belongs to the list
      Result::0..1,
      countOidInList( OidList, Oid, Count),
      #>=(Count, 1, Result)
   ).

% ocl_oclIsTypeOf(Instances, Obj, TypeName, Result) :-
%    Result is true if Obj is an instance of type TypeName and it is not
%    an instance of any subclass
%    TODO: This implementation does not consider collection types
%    Also, it assumes that we will not ask "isKindOf" for an object from a
%    different type hierarchy

delay ocl_oclIsTypeOf(_, Object, _, _) if var(Object).
ocl_oclIsTypeOf(_, X, _, oclUndefined) :- is_oclUndefined(X),!.
ocl_oclIsTypeOf(Instances, Object, TypeName, Result) :-
   Result::0..1,
   % InType = does the object belong to TypeName? 
   ocl_oclIsKindOf(Instances, Object, TypeName, InType),
   % Get a list of subtypes of type TypeName
   aux_subTypeList( TypeName, SubTypeList),
   % Generate a list InSubTypeList
   % InSubTypeList[i] = true iff the object belongs to the i-th subtype
   ( foreach(SubType, SubTypeList),
     foreach(InSubType, InSubTypeList),
     param(Instances, Object)
     do
       ocl_oclIsKindOf(Instances, Object, SubType, InSubType)
   ),
   % NotInSubType = does the object belong to a subtype of TypeName?
   #=(sum(InSubTypeList), 0, NotInSubType),
   ic:and(InType,NotInSubType,Result).
   
% aux_subTypeList(Type, SubTypeList) :-
%    SubTypeList is the list of all subtypes of Type
%    A class with no subtypes will return the empty list
aux_subTypeList(Type, TypeList ) :-
   % First test if there is inheritance in the model
   % If there is no predicate isSubTypeOf the model fails
   ( is_predicate(isSubTypeOf/2) ->
     findall(X, isSubTypeOf(X, Type), TypeList)
     ;
     TypeList = []
   ).
   
% aux_baseType(Type, BaseType) :-
%    BaseType is the superclass of Type with no parents
%    This operation will not work properly in models with multiple inheritance
aux_baseType(Type, BaseType) :-
   % Does the class have a parent?
   % Check if "isSubTypeOf" exists, just in case there is no inheritance at all
   % in the input model
   ( is_predicate(isSubTypeOf/2), isSubTypeOf( Type, Parent ) ->
     % Type has a parent: recursive call, find base type of parent
     aux_baseType( Parent, BaseType )
     ;   
     % Type has no parent: it is the base type
     BaseType = Type
   ).

% an intermediate version that ignores the runtime type of the objects
delay ocl_obj_equals(Obj1, _, _) if var(Obj1).
delay ocl_obj_equals(_, Obj2, _) if var(Obj2).
ocl_obj_equals(Obj1, _, oclUndefined):- is_oclUndefined(Obj1), !.
ocl_obj_equals(_, Obj2, oclUndefined):- is_oclUndefined(Obj2), !.
ocl_obj_equals(Obj1, Obj2, Result):-
   Result::0..1,
   ocl_mustBeObject(Obj1, Object1),
   ocl_mustBeObject(Obj2, Object2),
   % Compute the Oids of both objects
   getOid(Object1, Oid1),
   getOid(Object2, Oid2),
   % Check if both Oids are equal
   ( Oid1 #= Oid2
     -> Result = 1; 
     Result = 0 
   ).  

        
%ocl_obj_equals(Instances, Obj1, Type1, Obj2, Type2, Result) :-
%   Result is true if Obj1 and Obj2 are equal
delay ocl_obj_equals(_, Obj1, _ , Obj2, _, _ ) if var(Obj1).
delay ocl_obj_equals(_, _, _ , Obj2, _, _ ) if var(Obj2).
ocl_obj_equals(_, Obj1, _, _, _, oclUndefined):- is_oclUndefined(Obj1), !.
ocl_obj_equals(_, _, _ , Obj2, _, oclUndefined):- is_oclUndefined(Obj2), !.
ocl_obj_equals(_, Obj1, Type1, Obj2, Type2, Result):-
   Result::0..1,
   % Compute the base type of each object - the top of the class hierarchy
   aux_baseType(Type1, BaseType1),
   aux_baseType(Type2, BaseType2),
   % If the objects have the same base type, they will be equal if they have
   % the same Oid. Otherwise, they will be different
   ( BaseType1 = BaseType2 ->
     % Compare Oids
     % This could an object or a collection with one object
     % In the second case, convert it to an object 
     ocl_mustBeObject(Obj1, Object1),
     ocl_mustBeObject(Obj2, Object2),
     % Compute the Oids of both objects
     getOid(Object1, Oid1),
     getOid(Object2, Oid2),
     % Check if both Oids are equal
     #=( Oid1, Oid2, Result )
     ;
     % Objects are different
     Result = 0
   ).  

%ocl_obj_not_equals(Instances, Obj1, Type1, Obj2, Type2, Result) :-
%   Result is true if Obj1 and Obj2 are different
delay ocl_obj_not_equals(_, Obj1, _ , Obj2, _, _ ) if var(Obj1).
delay ocl_obj_not_equals(_, _, _ , Obj2, _, _ ) if var(Obj2).
ocl_obj_not_equals(_, Obj1, _, _, _, oclUndefined):- is_oclUndefined(Obj1), !.
ocl_obj_not_equals(_, _, _ , Obj2, _, oclUndefined):- is_oclUndefined(Obj2), !.
ocl_obj_not_equals(Instances, Obj1, Type1, Obj2, Type2, Result):-
   ocl_obj_equals(Instances, Obj1, Type1, Obj2, Type2, Aux),
   ic:neg(Aux, Result).

%ocl_allInstances(Instances, TypeName, Result) :-
%   Result is the set of instances of TypeName
% hanhdd: if nth1 returns not found ...

delay ocl_allInstances(Instances, _, _) if var(Instances).
ocl_allInstances(Instances, TypeName, Result) :-
   index(TypeName, Index),
   ( nth1(Index, Instances, Result)
     -> true;
     Result = []
   ).

%ocl_variable(Vars, NestingLevel, Result) :-
%   Result is the variable from Vars in position NestingLevel
%   Variable 1 is the variable defined in the innermost iterator, 
%   Var. 2 is defined in the next innermost iterator, ...

ocl_variable(Vars, NestingLevel, Result) :-
   nth1(NestingLevel, Vars, Result).

%ocl_attributeCall(Instances, TypeName, AttribName, Object, Result)  :-
%   Result is the value of attribute AttribName within Object, which is
%   an instance of TypeName. 

% Old implementation - does not support inheritance
% delay ocl_attributeCall(_, _, _, X, _) if var(X).
% ocl_attributeCall(_, TypeName, AttribName, Object, Result)  :-
%    attIndex(TypeName, AttribName, Index), 
%    arg(Index, Object, Result).

% Alternative implementation that supports inheritance

% //hanhdd
% the implementation to support association classes
% we could navigate from an association to associated classes using
% role names as attributes of the association class

delay ocl_attributeCall(_, _, _, X, _) if var(X).
ocl_attributeCall(_, _, _, Obj, oclUndefined)  :- is_oclUndefined(Obj), !.
ocl_attributeCall(Instances, TypeName, AttribName, Obj, Result)  :-
  ( is_predicate(roleAssocCls/3), roleAssocCls(TypeName, AttribName, TargetTypeName)
    -> ocl_attributeCall_noAssocCls(Instances, TypeName, AttribName, Obj, TargetId),
    ocl_allInstances(Instances, TargetTypeName, TargetInstances),
    findObjectByOid(TargetInstances, TargetId, Result)
  ; ocl_attributeCall_noAssocCls(Instances, TypeName, AttribName, Obj, Result)
  ).
ocl_attributeCall_noAssocCls(Instances, TypeName, AttribName, Obj, Result)  :-
  ocl_mustBeObject(Obj, Object),
  ( attIndex(TypeName, AttribName, Index) ->
    arg(Index, Object, Result), !
  ; 
    % The attribute must be defined in a superclass
    isSubTypeOf(TypeName, SuperClass),
    % Get the instances of the superclass
    index(SuperClass, SuperIndex),
    nth1(SuperIndex, Instances, SuperInstances),
    % Get the attributes of the object with the same oid
    % in the superclass (i.e. the attributes inherited from the superclass)
    getOid(Object, Oid),
    findObjectByOid(SuperInstances, Oid, ObjInSuperClass),
    ocl_attributeCall_noAssocCls(Instances, SuperClass, AttribName, ObjInSuperClass, Result)
  ; Result = oclUndefined
  ).

% findObjectByOid(Instances, Oid, Obj) :-
%   Find an Object with a given Oid with a list of Instances of a class

delay findObjectByOid(_,X,_) if var(X).
delay findObjectByOid([H|T],_,_) if getOid(H,X), nonground(X).
findObjectByOid([], _, oclUndefined) :- !.  
   %hanhdd
   %writeln("Internal error"),
   %writeln(" Oid of an object does not appear in its superclass"), 
   %abort.

findObjectByOid([H|T], Oid, Obj) :-
   getOid(H,O),
   ( O = Oid -> 
     Obj = H ;
     findObjectByOid(T, Oid, Obj) ).

% ocl_navigation(Instances, Vars, Association, SrcRole, DstRole, Objects, Result) :-
%    Navigation expression of an Association like Object.DstRole
%    - Association is the name of the association being navigated
%    - Objects is the value of the source object (or objects)
%    - SrcRole is the role where the source objects participate in Association,
%      the initial role of the navigation
%    - DstRole is the role of Association that we want to reach
%    - On output, Result becomes the set of objects that participate in DstRole 
%      such that some object from Objects participates in srcRole. If there is
%      only one object, instead of a list it become the first object of the set

delay ocl_navigation(_,_,_,_,X,_) if var(X).
ocl_navigation(_, _, _, _, Objects, oclUndefined) :- is_oclUndefined(Objects), !.
%ocl_navigation(_, _, _, _, Objects, oclUndefined) :- is_list(Objects), is_undefined_list(Objects), !.
ocl_navigation(Instances, Association, SrcRole, DstRole, Objects, Result) :-
   % Get the list of oids of the source objects
   ( is_list(Objects) -> 

     % Objects is a list of several objects
     getOidList(Objects, OidList) 
   ; 
     % Objects is a single object outside a list
     getOid(Objects,Oid),
     (is_oclUndefined(Oid) -> OidList = oclUndefined; OidList = [Oid])
   ),
 
   % Get the list of links of the association
   index(Association, AssocIndex),
   nth1(AssocIndex, Instances, LinkList),

   % Get the role indices
   roleIndex(Association, SrcRole, SrcIndex),
   roleIndex(Association, DstRole, DstIndex),

   % Get the set of links of the association where SrcIndex equals
   % an object within OidList. Returns a list of oids in the 
   % target relation
   aux_navigate(LinkList, SrcIndex, DstIndex, OidList, TargetOidList),
      
   % Get the set of objects of the target class   
   roleType(Association, DstRole, Type),
   index(Type, ClassIndex),
   nth1(ClassIndex, Instances, ObjectsOfType),

   % Select only those objects with an oid in the oid list
   aux_selectByOid(ObjectsOfType, TargetOidList, Result1),
   roleMax(Association,DstRole,Max),
   (Max==1 -> aux_set_to_obj(Result1,Result) ; Result=Result1).

delay aux_set_to_obj(X,_) if nonground(X).
aux_set_to_obj([X],X) :- !.
aux_set_to_obj(_,oclUndefined) :- !.

% aux_navigate(LinkList, SrcIndex, DstIndex, OidList, Result) :-
%    - LinkList is a list of links of an association
%    - SrcIndex is the input role for the navigation
%    - DstIndex is the output role for the association
%    - OidList is the list of valid oids in the input role
%    - Result should be assigned the list of valid oids in the
%      output role where a link with an oid from OidList in SrcRole
%      which have a corresponding Oid in OidList

delay aux_navigate(X,_,_,_,_) if nonground(X).
delay aux_navigate(_,X,_,_,_) if var(X).
delay aux_navigate(_,_,X,_,_) if var(X).
delay aux_navigate(_,_,_,X,_) if nonground(X).
aux_navigate(X, _, _, _, oclUndefined) :- is_oclUndefined(X),!.
aux_navigate(_, X, _, _, oclUndefined) :- is_oclUndefined(X),!.
aux_navigate(_, _, X, _, oclUndefined) :- is_oclUndefined(X),!.
aux_navigate(_, _, _, X, oclUndefined) :- is_oclUndefined(X),!.
aux_navigate(LinkList, SrcIndex, DstIndex, OidList, Result) :-
   ( foreach(Link, LinkList),
     fromto([], In, Out, Result),
     param(SrcIndex, DstIndex, OidList)
     do 
        arg(SrcIndex, Link, SrcValue),
        ( member(SrcValue, OidList) -> 
          % The target of this link should be added to the result
          arg(DstIndex, Link, DstValue),
          Out = [DstValue|In]          
        ;
          % The target of this link should not be added to the result
          Out = In
        )
   ).

% aux_selectByOid(Instances, OidList, Result) :-
%    Result stores a list of objects from Instances with the given oids in OidList
%    Result is always a list, even if there is only a single object

delay aux_selectByOid(X,_,_) if var(X).
delay aux_selectByOid(_,X,_) if nonground(X).
delay aux_selectByOid(X,_,_) if getOidList(X,Y), nonground(Y). 
aux_selectByOid(X,_,oclUndefined) :- is_oclUndefined(X), !.
aux_selectByOid(_,Y,oclUndefined) :- is_oclUndefined(Y),!.
aux_selectByOid(Instances, OidList, Result) :-
   ( foreach(Object, Instances),
     fromto([], In, Out, Result),
     param(OidList)
     do
        getOid(Object, Oid),
        ( member(Oid, OidList) ->
          % This object belongs to the solution
          Out = [Object|In]
	;
          % This object does not belong to the solution
          Out = In 
	)  
   ).
   % Check if the length of the list is one, in that case return the object
   % outside of the list
   %( length(ObjectList,1) ->
   %  ObjectList = [ Result ]; 
   %  Result = ObjectList
   %).
      
% ocl_mustBeObject( X, Y ) :-
%    Check that X is either an object or a collection of only one object.
%    If it is an object, it will be stored in variable Y upon success. 
%    Otherwise the function will fail.
%    Navigation may return a collection of just one object. This function
%    is called when access to the single object is needed.

delay ocl_mustBeObject(X,_) if var(X). 
ocl_mustBeObject(X, oclUndefined) :- is_oclUndefined(X),!.
ocl_mustBeObject([H|[]], H)    :- !.
ocl_mustBeObject([_|[_|_]], oclUndefined):- !.
ocl_mustBeObject(X, X) :- is_not_list(X), !.

% check if Result is oclUndefined
is_oclUndefined(Result) :-
  ground(Result),
  Result = oclUndefined.
