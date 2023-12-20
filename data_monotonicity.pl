%    The contents of this file are subject to the Mozilla Public License
%    Version  1.1  (the "License"); you may not use this file except in
%    compliance with the License. You may obtain a copy of the License at:
%
%    http://www.mozilla.org/MPL/
%
%    Software  distributed  under  the License is distributed on an "AS
%    IS"  basis,  WITHOUT  WARRANTY  OF  ANY  KIND,  either  express or
%    implied.
%
% Purpose: EVALUATE MONOTONICITY OF A TABLE AND PROVIDE PREDICATES TO COMPUTE MONOTONICITY OF BOUND CONJECTURES ACQUIRED FUNCTIONS
% Authors: Nicolas Beldiceanu, IMT Atlantique

:- module(monotonicity,[check_monotonicity/3,
                        monotonicity/4,
                        combine_monotonicity/3]).

:- use_module(library(clpfd)).
:- use_module(utility).

check_monotonicity(_, none, none) :- !.                           % stop as soon as identify a group with two inflexion points
check_monotonicity([], Monotonicity, Monotonicity) :- !.          % stop if on empty list
check_monotonicity([_], Monotonicity, Monotonicity) :- !.         % stop if on a list with one element: one group of one element
check_monotonicity(L, Previous, Final) :-
    monotonicity(L, undetermined, Monotonicity, RemainingGroups), % compute monotonicity of current group
    (Monotonicity = none -> Final = none                                          ;
                            combine_monotonicity(Previous, Monotonicity, Current),
                            check_monotonicity(RemainingGroups, Current, Final)   ).

monotonicity(_, none, none, _) :- !.                                             % stop as soon as identify two inflexion points in the group
monotonicity([_], Monotonicity, Monotonicity, []) :- !.                          % stop and retransmit result if at the end the group
monotonicity([P-t(_,B1), P-t(Q2,B2)|R], Previous, Final, RemainingGroups) :- !,
    (B1 < B2 -> Current = inc ;                                                  % compare bounds of two consecutive entry of current group
     B1 = B2 -> Current = cst ;
                Current = dec ),
    combine_trend(Previous, Current, Next),                                      % combine trend of the group with current trend
    (Next = none -> Final = none                                                       ;
                            monotonicity([P-t(Q2,B2)|R], Next, Final, RemainingGroups) ).
monotonicity([_,Elem|R], Final, Final, [Elem|R]).                                % stop and retransmit result if at the end the group

% combine previous trend with current trend in order to update the trend of a group
combine_trend(undetermined, Res, Res   ) :- !.
combine_trend(cst,          Res, Res   ) :- !.
combine_trend(inc,          dec, peak  ) :- !.
combine_trend(inc,          _,   inc   ) :- !.
combine_trend(dec,          inc, valley) :- !.
combine_trend(dec,          _,   dec   ) :- !.
combine_trend(peak,         inc, none  ) :- !.
combine_trend(peak,         _,   peak  ) :- !.
combine_trend(valley,       dec, none  ) :- !.
combine_trend(valley,       _,   valley).

% combine monotonicity information of previous groups with monotonicity information of current group
combine_monotonicity(none,         _,            none  ) :- !.
combine_monotonicity(undetermined, Res,          Res   ) :- !.
combine_monotonicity(cst,          undetermined, cst   ) :- !.
combine_monotonicity(cst,          Res,          Res   ) :- !.
combine_monotonicity(inc,          dec,          incdec) :- !.
combine_monotonicity(inc,          incdec,       incdec) :- !.
combine_monotonicity(inc,          peak,         peak  ) :- !.
combine_monotonicity(inc,          valley,       valley) :- !.
combine_monotonicity(inc,          _,            inc   ) :- !.
combine_monotonicity(dec,          inc,          incdec) :- !.
combine_monotonicity(dec,          incdec,       incdec) :- !.
combine_monotonicity(dec,          peak,         peak  ) :- !.
combine_monotonicity(dec,          valley,       valley) :- !.
combine_monotonicity(dec,          _,            dec   ) :- !.
combine_monotonicity(incdec,       peak,         peak  ) :- !.
combine_monotonicity(incdec,       valley,       valley) :- !.
combine_monotonicity(incdec,       _,            incdec) :- !.
combine_monotonicity(peak,         valley,       none  ) :- !.
combine_monotonicity(peak,         _,            peak  ) :- !.
combine_monotonicity(valley,       peak,         none  ) :- !.
combine_monotonicity(valley,       _,            valley).
