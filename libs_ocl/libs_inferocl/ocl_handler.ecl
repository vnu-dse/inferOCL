% 2014/02/06:
% - Create the file

:- lib(ic).
:- lib(ech).
:- lib(ordset).
:- lib(var_name).
:- handler ocl_handler.

:- option(already_in_store, off). 
:- option(check_guard_bindings, off).
:- option(default_chr_priority,6).

:- constraints 
	aux_col_select/3,
	ocl_col_size/2.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%                           INFERENCE RULES                            % 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%%%%%%%%%%%%%%%%%%%%%%%%%% uniqueAttr %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%LocalPara = [X_Class, X_Attr]

ocl_hander_rule1	::= 	aux_col_select(Collection1, List1, Result1),
				aux_col_select(Collection2, List2, Result2)
				<=>	Collection1 == Collection2, List1 == List2 | aux_col_select(Collection1, List1, Result1), Result1 = Result2.


ocl_hander_rule2	::= 	ocl_col_size(Col1, Size1),
				ocl_col_size(Col2, Size2)
				<=>	Col1 == Col2 | ocl_col_size(Col1, Size1), Size1 = Size2.
