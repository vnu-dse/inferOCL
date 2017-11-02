txt_write_object_diagram(FileName, Instances) :-
   % Create the snapshot file
   open(FileName, write, Stream, [end_of_line(crlf)]),
   % Write all objects and links in the file
   write(Stream,"["),
   (foreach(TypeInstances, Instances),
    count(Idx, 1, _),
    param(Stream, Instances)
    do
      ( Idx = 1
        -> true;
        write(Stream, ",")
      ),
      % Get the name of this type
      index(TypeName, Idx),
      % Test whether this is a class or an association
      % Associations will have a "isUnique" flag
      %   
      ( is_predicate(assocIsUnique/2), assocIsUnique(TypeName,_) ->
        % Association
        txt_write_assoc(Stream, TypeInstances, TypeName);
        % Class
        ( is_predicate(isSubTypeOf/2), isSubTypeOf( TypeName, _) -> 
           % The class has a parent
           % No need to print the file, it will be printed by the base type
           true
           ;
           txt_write_class(Stream, Instances, TypeInstances, TypeName)
         )
      )
   ),
   write(Stream,"]"),
   close(Stream).

%   Write all links (Instances) of a given association of name TypeName.

txt_write_assoc(Stream, Instances, TypeName) :-
   write(Stream,"["),
   ( foreach(Link, Instances),
     count(N, 1, _), 
     param(Stream, TypeName)
     do(
       ( N = 1
         -> true;
         write(Stream, ",")
       ),
       txt_write_link(Stream, Link, TypeName)
     )
   ),
   write(Stream,"]").

%   Write all objects (TypeInstances) of a given class of name TypeName.

txt_write_class(Stream, Instances, TypeInstances, TypeName) :-
   write(Stream,"["),
   ( foreach(Object, TypeInstances),
     count(N, 1, _),
     param(Stream, TypeName, Instances)
     do(
       ( N = 1
         -> true;
         write(Stream,",")
       ),
       txt_write_object(Stream, Instances, Object, TypeName)
     )
   ),
   write(Stream,"]").    

% txt_write_attributes(+Stream, +Object, +TypeName):-
%   Write all attributes of a given object within class TypeName.

txt_write_attributes(Stream, Object, TypeName) :-
  ( foreacharg(AttribValue, Object, Idx),
    count(N, 1, _),    
    param(Stream, TypeName)
    do(
      ( N = 1
        -> true;
        write(Stream, ",")
      ),
      ( Idx = 1 -> 
        % Ignore the oid field
        true;
        attIndex(TypeName, AttribName, Idx),
        attType(TypeName, AttribName, AttType),
        % Write another attribute
        txt_att_value_to_string(AttribValue,AttType,VS),
        write(Stream, VS)
      )
    )
  ).

txt_att_value_to_string(Value,"EString", VS) :- !, txt_att_value_to_string(Value,"String",VS).

txt_att_value_to_string(Value,"String", VS) :-
        is_list(Value),
	!,
	(foreach(V,Value),fromto("",V1,V2,VS) do 
            ( V :: [38,39,60,62,91,92,93,123,125] -> sprintf(X,"\\%c",[V]); sprintf(X,"%c",V)),
            append_strings(V1,X,V2)
        ).

txt_att_value_to_string(Value,_ , VS) :-
	sprintf(VS,"%w",Value).

% txt_type_list(+Instances, +Object, +TypeName, -TypeList, -ObjList) :-
%   Given an Object of a given TypeName, compute the list of subtypes of TypeName
%   where the Object belongs. The most concrete type should be the first type
%   of the list.

txt_findObjectByOid([], _, _) :- fail.
txt_findObjectByOid([H|T], Oid, Obj) :-
   getOid(H,O),
   ( O = Oid -> 
     Obj = H ;
     txt_findObjectByOid(T, Oid, Obj) ).

txt_type_list(Instances, Object, TypeName, TypeList, ObjList) :- 
   % Check if the type has a subtype
   is_predicate(isSubTypeOf/2),
   isSubTypeOf(SubType, TypeName),
   % Check if the oid of the object is a valid oid of the subclass
   % Get the oid of the object
   getOid(Object, Oid),
   % Get the list of oids of the objects of the subclass
   index(SubType, Index),
   nth1(Index, Instances, ObjectList),
   % Find the object with that oid within 
   txt_findObjectByOid( ObjectList, Oid, Obj),     
   % Recursive call
   txt_type_list(Instances, Obj, SubType, TypeAuxList, ObjAuxList),
   append(TypeAuxList,[TypeName], TypeList),
   append(ObjAuxList,[Obj], ObjList).

txt_type_list(_, Object, TypeName, TypeList, ObjList) :- 
   TypeList = [ TypeName ],
   ObjList = [ Object ],
   !.
   
% txt_write_object(+Stream, +Instances, +Object, +TypeName):-
%   Write all information about an instance of a class to the Snapshot file. 

txt_write_object(Stream, Instances, Object, TypeName) :-
  % The identifier used within the GraphViz file will be   
  % type name in lower case + oid of the object:
  getOid(Object, Oid),
  % Get the list of types of the object (the object may have attributes
  % in a class, one of its subclasses, ...)
  txt_type_list(Instances, Object, TypeName, TypeList, ObjList),
  % Get the most concretetype
  nth1(1, TypeList, MostConcreteType), 
  printf(Stream, "%s(%d", [MostConcreteType, Oid]),
  % Write the list of attributes of the object
  ( foreach(Type, TypeList),
    foreach(Obj, ObjList),
    count(N, 1, _),
    param(Stream)
    do(      
      ( N = 1
        -> true;
        write(Stream, ",")
      ),
      txt_write_attributes(Stream, Obj, Type)
    )
  ),
  write(Stream,")").     

% txt_write_link(+Stream, +Link, +TypeName) :-
%   Write a Link with type TypeName.

txt_write_link(Stream, Link, TypeName) :-
   % Get the arity of the link
   functor(Link, _, Arity),
   % Binary and n-ary links will be drawn in a different way.
   (Arity = 2 ->
    txt_write_binary_link(Stream, Link, TypeName);
    txt_write_nary_link(Stream, Link, TypeName)
   ).

% txt_write_binary_link(+Stream, +Link, +TypeName) :-
%   Write a binary Link between two objects.

txt_write_binary_link(Stream, Link, TypeName) :-
   % Get Oids of participating objects
   arg(1, Link, Oid1),
   arg(2, Link, Oid2),
   % Get role names (needed to access role types)
   %roleIndex(TypeName, RoleName1, 1),
   %roleIndex(TypeName, RoleName2, 2),
   % Get role types
   %roleType(TypeName, RoleName1, RoleType1),
   %roleType(TypeName, RoleName2, RoleType2),
   % Locate the base types for each role type
   %aux_baseType(RoleType1, BaseRoleType1),
   %aux_baseType(RoleType2, BaseRoleType2),
   printf(Stream, "%s(%d,%d)", [TypeName, Oid1, Oid2]).     
  
% txt_write_nary_link(+Stream, +Link, +TypeName) :-
%   Write a n-ary Link between two objects.
%   TODO: Missing!

txt_write_nary_link(_, _, _) :-
   true.
     
     
