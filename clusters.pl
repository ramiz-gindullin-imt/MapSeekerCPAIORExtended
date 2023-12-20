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
% Purpose: Main program to run to generate conjectures (in the context of combinatorial objects) or
%          to acquire constraints (in the context of ASSISTANT)
% Author : Nicolas Beldiceanu, IMT Atlantique

:- use_module(library(clpfd)).
:- use_module(gen_candidate_tables).

:- use_module(table_access).
:- use_module(tables).

:- multifile conjecture/9. % cmodif
:- dynamic conjecture/9.   % cmodif

:- multifile table_metadata/31.
:- dynamic table_metadata/31.

top(KindCombi) :-
    attributes_combi(KindCombi, KindBounds),
    member(Bound, [low(_), up(_)]),
    member(KindBound, KindBounds),
    functor(Bound, BoundName, 1),
    atom_concat('conjectures_', BoundName, Tempo0  ),
    atom_concat(Tempo0,         '_',       Tempo1  ),
    atom_concat(Tempo1,         KindBound, ConjFile),
    atom_concat('found_conjectures/', ConjFile, ConjFile1),
    atom_concat(ConjFile1, '_bool.pl', CFile),
    consult(CFile),
    gen_tables(Table, KindCombi, KindBound, Bound, _NParam),
    max_size_combi(KindCombi, MaxN),
    number_codes(MaxN, CodesMaxN),           % convert MaxN to an atom in order to create
    atom_codes(AtomMaxN, CodesMaxN),         % the name of the subfolder that will contain
    atom_concat('data/', KindCombi, Tempo0),
    atom_concat(Tempo0,  '/data',   Tempo1),
    atom_concat(Tempo1,  AtomMaxN,  Tempo2),
    atom_concat(Tempo2,  '/',       Tempo3),
    atom_concat(Tempo3,  Table,     Table1),
    atom_concat(Table1, '_metadata.pl', MetaDataFile),
    consult(MetaDataFile),
    tab_get_arity(col(Table,_), NbCol),
    Col in 1..NbCol,
    indomain(Col),
    tab_get_name(col(Table,Col), Name),
    tab_get_kind(col(Table,Col), Kind),
    memberchk(Kind, [low,up,secondary]),
    tab_get_min(col(Table,Col), Min),
    tab_get_max(col(Table,Col), Max),
    tab_get_nval(col(Table,Col), NVal),
    Range is Max-Min,
    check_range_nval(Range, NVal, RangeNVal),
    (conjecture(_,Kind,col(Table,Col),_,_,_,_,_,_) -> % cmodif
        false
    ;
        write(Table), write(' '),
        write(RangeNVal), write(' '),
        write(Name), write(' '),
        (RangeNVal = range ->
            write(Min), write(' '), write(Max)
        ;
            write(NVal)
        ),
        nl,
        false
    ),
    get_metadata_arity(MetadataArity),
    functor(TermMetadata, table_metadata, MetadataArity),
    retractall(TermMetadata),
    false.

check_range_nval(Range, _, range) :-
    Range > 1,
    Range =< 3,
    !.
check_range_nval(_, NVal, val) :-
    NVal > 2,
    NVal =< 4.

gen_tables(Table, KindCombi, KindBound, Bound, NParam) :-
    gen_candidate_tables(Table, KindCombi, KindBound, Bound, NParam).
gen_tables(_, _, _, _, _) :-
    functor(TermConjecture, conjecture, 9), % cmodif
    retractall(TermConjecture),
    false.
