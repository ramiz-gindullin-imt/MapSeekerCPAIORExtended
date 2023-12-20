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
:- use_module(library(lists)).
:- use_module(table_access).
:- use_module(tables).
:- use_module(utility).
:- use_module(gen_candidate_tables).

% set_prolog_flag(informational,off), [performance_test_script], create_examples, halt.
% set_prolog_flag(informational,off), [performance_test_script], create_stats.

%top :- create_examples('existing_maps/graph/found_conjectures_graph_low_mina.pl').

create_examples:-
    open('performance_test_list.pl', write, FOut),
    format(FOut, ':- multifile table_info/6.~n:- dynamic table_info/6.~n~n~n', []),
    Maps = [[forest,     low, [t, f, minf, maxf, mind, maxd, minp, maxp, mint, maxt]],
            [forest,      up, [t, f, minf, maxf, mind, maxd, minp, maxp, mint, maxt]],
            [forest0,    low, [t, f, minf, maxf, mind, maxd, minp, maxp, mint, maxt]],
            [forest0,     up, [t, f, minf, maxf, mind, maxd, minp, maxp, mint, maxt]],
            [cgroup,     low, [dmax, dmin, drange, dsum_squares, ng, nv, smax, smin, srange, ssum_squares]],
            [cgroup,      up, [dmax, dmin, drange, dsum_squares, ng, nv, smax, smin, srange, ssum_squares]],
            [graph,      low, [v, c, minc, maxc, s, mins, maxs, mina]],
            [graph,       up, [v, c, minc, maxc, s, mins, maxs, maxa]],
            [group,      low, [dmax, dmin, drange, dsum_squares, ng, nv, smax, smin, srange, ssum_squares]],
            [group,       up, [dmax, dmin, drange, dsum_squares, ng, nv,       smin, srange              ]],
            [partition,  low, [max, min, nval, range, sum_squares]],
            [partition,   up, [max, min, nval, range, sum_squares]],
            [partition0, low, [max, min, nval, range, sum_squares]],
            [partition0,  up, [max, min, nval, range, sum_squares]],
            [tree,       low, [f, mind, maxd, minp, maxp]],
            [tree,        up, [f, mind, maxd, minp, maxp]]
            ], % for test purposes
    % what I have now, all the unbroken files
    (foreach(Map,Maps), param(FOut) do consult_map(Map, FOut)),
    close(FOut).

% put it back later.
maps(      [[forest,     low, [f, maxd, maxf, maxp, maxt, mind, minf, minp, mint, t]],
            [forest,      up, [f, maxd, maxf, maxp, maxt, mind, minf, minp, mint, t]],
            [forest0,    low, [f, maxd, maxf, maxp, maxt, mind, minf, minp, mint, t]],
            [forest0,     up, [f, maxd, maxf, maxp, maxt, mind, minf, minp, mint, t]],
            [cgroup,     low, [dmax, dmin, drange, dsum_squares, ng, nv, smax, smin, srange, ssum_squares]],
            [cgroup,      up, [dmax, dmin, drange, dsum_squares, ng, nv, smax, smin, srange, ssum_squares]],
            [graph,      low, [v, c, minc, maxc, s, mins, maxs, mina]],
            [graph,       up, [v, c, minc, maxc, s, mins, maxs, maxa]],
            [group,      low, [dmax, dmin, drange, dsum_squares, ng, nv, smax, smin, srange, ssum_squares]],
            [group,       up, [dmax, dmin, drange, dsum_squares, ng, nv,       smin, srange              ]],
            [partition,  low, [max, min, nval, range, sum_squares]],
            [partition,   up, [max, min, nval, range, sum_squares]],
            [partition0, low, [max, min, nval, range, sum_squares]],
            [partition0,  up, [max, min, nval, range, sum_squares]],
            [tree,       low, [f, maxd, maxp, mind, minp]],
            [tree,        up, [f, maxd, maxp, mind, minp]]
            ]).

consult_map([KindCombi, Bound, InvariantList], FOut) :-
    (foreach(Invariant, InvariantList), param([KindCombi, Bound, FOut])
    do
     write('% '),write([KindCombi, Bound, Invariant]),nl,
     consult_map(KindCombi, Bound, Invariant),

     findall([OutputCol,Cost,Conjecture],
            (functor(Conjecture, conjecture, 9),
             call(Conjecture),
             Conjecture = conjecture(_,_,OutputCol,_,_,Cost,_,_,_)),
            ConjectureList),
     sort(ConjectureList,ConjectureListSorted),
     filter_conjectures_by_cost(ConjectureListSorted, ConjectureListFiltered),
     select_bool_conjectures(ConjectureListFiltered, ConjectureBoolList),
     create_example(ConjectureBoolList, [KindCombi, Bound, Invariant], TablesInfo),
     (foreach(TableInfo, TablesInfo), param(FOut)
     do
      format(FOut, '~w.~n', [TableInfo])
     ),
     retractall(conjecture(_,_,_,_,_,_,_,_,_))
    ).

filter_conjectures_by_cost([],[]) :- !.
filter_conjectures_by_cost([Conjecture],[Conjecture]) :- !.
filter_conjectures_by_cost([[OutputCol,Cost1,Formula1],
                            [OutputCol,Cost2,Formula2]|R], ConjectureListFiltered) :-
    !,
    (Cost1 >= Cost2 ->
        filter_conjectures_by_cost([[OutputCol,Cost2,Formula2]|R], ConjectureListFiltered)
    ;
        filter_conjectures_by_cost([[OutputCol,Cost1,Formula1]|R], ConjectureListFiltered)
     ).
filter_conjectures_by_cost([[OutputCol1,Cost1,Formula1],
                            [OutputCol2,Cost2,Formula2]|R], [[OutputCol1,Cost1,Formula1]|S]) :-
    filter_conjectures_by_cost([[OutputCol2,Cost2,Formula2]|R], S).

select_bool_conjectures(ConjectureList, ConjectureBoolList) :-
    findall(conjecture(Type,OutputCol,OutputName,MaxN,Cost,FormulaB),
            (member([_,_,Conjecture], ConjectureList),
             Conjecture = conjecture(_,Type,OutputCol,OutputName,MaxN,Cost,Formula,_,_),
             Formula = t(InputCols, InputNames, ShiftBool, bool(Negated, _, Oplus, NbTerms, _)),
             FormulaB = t(InputCols, InputNames, ShiftBool, bool(Negated, 0, Oplus, NbTerms, none))
            ),
            ConjectureBoolList).

create_example(Conjectures, [KindCombi, Bound, Invariant], TablesInfo) :-
    create_example(Conjectures, 1, [KindCombi, Bound, Invariant], TablesInfo).

create_example([], _, _, []) :- !.
create_example([Conjecture|R], I, [KindCombi, Bound, Invariant], [table_info(TableName,KindCombi,Bound-Invariant,Negated,Oplus,NbTerms)|S]):-
    Conjecture = conjecture(_Type,col(TableNameSource,OutputCol), OutputName, MaxN, _Cost,
                            t(InputCols, InputNames, _, bool(Negated, _ShiftBool, Oplus, NbTerms, _Conds))), % we keep the same MaxN
    %write([KindCombi, Bound, Invariant]-Conjecture),
    load_table_metadata(KindCombi, MaxN, TableNameSource),
    %write(' oui'),nl,
    % step 1 - create new table name and file
    number_codes(I, CodesI),                              % convert MaxN to an atom
    atom_codes(AtomI, CodesI),                            % as it will be part of the name of the directory where to access data
    atoms_concat(['test_table_',KindCombi,'_',Bound,'_',Invariant,'_', AtomI], TableName),
    atoms_concat(['data/model_seeker/data0/',TableName,'.pl'],TableFile),
    length(InputCols, NCol0),
    NCol is NCol0 + 1,
    open(TableFile, write, SOut),
    format(SOut, ':- multifile signature/3.~n:- multifile ~w/~w.~n:- dynamic signature/3.~n:- dynamic ~w/~w.~n~n~n',
           [TableName,NCol,TableName,NCol]),
    write(table(model_seeker, TableName, [0-NCol], 0, [no_pk,no_fk])),write('.'),% write([KindCombi, Bound, Invariant]-Conjecture),
    
    % step 2 - create signature term and write it
    functor(Signature, signature, 3),
    arg(1, Signature, TableName),
    arg(2, Signature, 0),
    functor(ColList, t, NCol),
    (foreach(ColName, InputNames), for(I2,1,NCol0), param(ColList)
    do
     arg(I2, ColList, t(ColName, primary, input))
    ),
    arg(NCol, ColList, t(OutputName, secondary, output)),
    arg(3, Signature, ColList),
    format(SOut, '~w.~n~n', [Signature]),
    % step 3 - create table entries and write them
    tab_get_arity(col(TableNameSource,_), NSource),
    findall(EntryTerm,
            (functor(EntryTermSource, TableNameSource, NSource),
             functor(EntryTerm,       TableName,       NCol   ),
             call(EntryTermSource),
             (foreach(col(_,ColI), InputCols), for(I3,1,NCol0),
              param([ColList, EntryTerm, EntryTermSource])
             do
              arg(ColI, EntryTermSource, Value),
              arg(I3,   EntryTerm,       Value)
             ),
             arg(OutputCol, EntryTermSource, ValueOutput),
             arg(NCol,      EntryTerm,       ValueOutput),
             format(SOut, '~w.~n', [EntryTerm])
            ),
            _),
    % step 4 - remove table info from RAM and move to the next table
    close(SOut),
    nl,
    remove_signature_and_table_facts(TableNameSource),
    get_metadata_arity(Arity),
    functor(MetadataTerm, table_metadata, Arity),
    retractall(user:MetadataTerm),
    I1 is I + 1,
    create_example(R, I1, [KindCombi, Bound, Invariant], S).

consult_map(KindCombi, Bound, Invariant) :-
    atom_concat('existing_maps/', KindCombi, PrefixName0),
    atom_concat(PrefixName0, '/found_conjectures_', PrefixName),
    atom_concat(PrefixName, KindCombi, PrefixNameKind0),
    atom_concat(PrefixNameKind0, '_', PrefixNameKind),
    atom_concat(PrefixNameKind, Bound, PrefixNameBound0),
    atom_concat(PrefixNameBound0, '_', PrefixNameBound),
    atom_concat(PrefixNameBound, Invariant, PrefixNameInvariant),
    atom_concat(PrefixNameInvariant, '.pl', FileName),
    consult(FileName).

load_table_metadata(KindCombi, MaxN, Table):-
    atoms_concat(['data/',KindCombi,'/data'], DirData),
    gen_table_and_metadata_file_names(DirData, MaxN, Table, TableFile, MetadataFile),
    consult(TableFile),
    consult(MetadataFile).



% set_prolog_flag(informational,off), [performance_test_script], create_stats, halt.
create_stats :-
    create_stat('performance_test_stats_core_model.pl'),
    create_stat('performance_test_stats_enhanced_model.pl'),
    create_stat('performance_test_stats_full_model.pl').

% set_prolog_flag(informational,off), [performance_test_script], create_stats2m halt.
create_stats2 :-
    create_stat('performance_test_stats_adv_5_1_only.pl'),
    create_stat('performance_test_stats_adv_5_2_only.pl'),
    create_stat('performance_test_stats_adv_5_3_only.pl').

create_stat(File) :-
    write('Results for '),write(File),write(':'),nl,
    consult(File),
    findall(KindCombi, performance(_,_,KindCombi,_,_,_,_), MapsAll),
    %findall(KindCombi-Map, performance(_,_,KindCombi,Map,_,_,_), MapsAll),
    findall(Oplus-NbTerms, performance(_,_,_,_,Oplus,NbTerms,_), CandFormulaeAll),
    sort(MapsAll,Maps),
    sort(CandFormulaeAll,CandFormulae),
    write('Per map:'),nl,
    %(foreach(KindCombiI-MapI,Maps)
    (foreach(KindCombiI,Maps)
    do
     findall(Runtime,performance(_,_,KindCombiI,_MapI,_,_,Runtime),Runtimes),
     sumlist(Runtimes, TotalRuntime),
     length(Runtimes,  NTables),
     TotalRuntimes is TotalRuntime div 1000,
     AvgRuntime is TotalRuntimes div NTables,
     %write(KindCombiI-MapI), write(' ('), write(NTables), write('): '), write(TotalRuntimes), write('s / '), write(AvgRuntime), write('s.'), nl
     write(KindCombiI), write(' ('), write(NTables), write('): '), write(TotalRuntimes), write('s / '), write(AvgRuntime), write('s.'), nl
    ),
    nl,nl,
    write('Per formula complexity:'),nl,
    (foreach(OplusI-NbTermsI,CandFormulae)
    do
     findall(Runtime,performance(_,_,_,_,OplusI,NbTermsI,Runtime),Runtimes),
     sumlist(Runtimes, TotalRuntime),
     length(Runtimes,  NTables),
     TotalRuntimes is TotalRuntime div 1000,
     AvgRuntime is TotalRuntimes div NTables,
     write(OplusI-NbTermsI), write(' ('), write(NTables), write('): '), write(TotalRuntimes), write('s / '), write(AvgRuntime), write('s.'), nl
    ),
    nl,nl,nl,
    retractall(performance(_,_,_,_,_,_,_)).
