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
% Purpose: point to potential non sharp missing bounds by examining and comparing all produced maps of a combinatorial object by inverting quadratic conjectures
% Authors: Nicolas Beldiceanu, IMT Atlantique and Jovial Cheukam Ngouonou, IMT Atlantique, Université Laval (Québec)
% WARNING: TODO update name of conjecture file wrt SplitDiv, SplitMod (maybe assume them to be both 1).

:- use_module(library(lists)).
:- use_module(library(clpfd)).
:- use_module(table_access).
:- use_module(tables).
:- use_module(utility).
:- use_module(gen_candidate_tables).
:- use_module(eval_formula).

/*

extract from conjecture id(low_n_srange_ssum_squares,_49583,_49585) upper bound (up_n_ssum_squares_srange) for srange by inverting lower bound of ssum_squares wrt parameter srange
conjecture(up,
           col(up_n_ssum_squares_srange,2),
           srange,
           30,
           10,
           t([col(up_n_ssum_squares_srange,2)],
           [ssum_squares],
           [_103885],
           ffloor(plus(polynom([monome([],-2)]),
                       sqrt(polynom([monome([t(_103885,1)],4),monome([],4)]))),
                  polynom([monome([],2)]))))
           
           srange =< floor( -2 - sqrt() )
eval_formula_term(fdiv(minus(polynom([monome([],-2)]),sqrt(polynom([monome([t(_114799,1)],-4),monome([t(0,1)],4),monome([],4)]))),polynom([monome([],2)])))



| ?- top(partition).

extract from table low_n_max_sum_squares upper bound (up_n_sum_squares_max) for max by inverting lower bound of sum_squares wrt parameters n and max
conjecture(up,col(up_n_sum_squares_max,3),max,30,10,t([col(up_n_sum_squares_max,1),col(up_n_sum_squares_max,2)],[n,sum_squares],[_46389,_46489],ffloor(plus(polynom([monome([],1)]),sqrt(polynom([monome([t(_46389,1)],-4),monome([t(_46489,1)],4),monome([],1)]))),polynom([monome([],2)]))))
max =< floor( (1 + sqrt(-4.n + 4.sum_squares + 1)) / 2)

extract from table low_n_range_sum_squares upper bound (up_n_sum_squares_range) for range by inverting lower bound of sum_squares wrt parameters n and range
conjecture(up,col(up_n_sum_squares_range,3),range,30,10,t([col(up_n_sum_squares_range,1),col(up_n_sum_squares_range,2)],[n,sum_squares],[_42545,_42617],ffloor(plus(polynom([monome([],-1)]),sqrt(polynom([monome([t(_42545,1)],-4),monome([t(_42617,1)],4),monome([],1)]))),polynom([monome([],2)]))))
range =< floor( (-1 + sqrt(-4.n + 4.sum_squares + 1)) / 2)

extract from table up_n_max_sum_squares lower bound (low_n_sum_squares_max) for max by inverting upper bound of sum_squares wrt parameters n and max
conjecture(low,col(low_n_sum_squares_max,3),max,30,10,t([col(low_n_sum_squares_max,1),col(low_n_sum_squares_max,2)],[n,sum_squares],[_65051,_65123],fceil(plus(polynom([monome([t(_65051,1)],-1),monome([],2)]),sqrt(polynom([monome([t(_65051,2)],1),monome([t(_65051,1)],-4),monome([t(_65123,1)],4)]))),polynom([monome([],2)]))))
max >= ceil( (-n+2) + sqrt(n^2 - 4.n + 4.sum_squares) / 2)



found conjecture: partition0
 conjecture(low,col(low_n_m_sum_squares_max,3),max,30,10,
 t([col(low_n_m_sum_squares_max,1),col(low_n_m_sum_squares_max,3)],
   [n,sum_squares],
   [_57775,_57875],
   fceil(plus(polynom([monome([t(_57775,1)],-1),monome([],2)]),
              sqrt(polynom([monome([t(_57775,2)],1),monome([t(_57775,1)],-4),monome([t(_57875,1)],4)]))),
         polynom([monome([],2)]))))
   ceil( -n+2 + sqrt(n^2 - 4.n + 4.sum_squares) / 2)


| ?- top(cgroup).

extract from conjecture id(up_n_ng_dmin_nv,_45461,_45463) lower bound (low_n_nv_dmin_ng) for ng by inverting upper bound of nv wrt parameters n, ng and dmin
conjecture(low,
           col(low_n_nv_dmin_ng,4),
           ng,
           20,
           10,
           t([col(low_n_nv_dmin_ng,1),col(low_n_nv_dmin_ng,2),col(low_n_nv_dmin_ng,3)],
              [n,      nv,     dmin],
              [_123531,_123617,_123539],
              fceil(plus(polynom([monome([t(_123531,1)],-1),monome([t(_123539,1)],1)]),
                    sqrt(polynom([monome([t(_123539,1),t(_123531,1)],-2),monome([t(_123539,2)],1),monome([t(_123531,2)],1),monome([t(_123617,1)],4)]))),
                   polynom([monome([],2)])))
          )

ng >= ceil( dmin - n + sqrt(-2.n.dmin + dmin^2 + n^2 + 4.nv) / 2 )
ng >= ceil( dmin-n + sqrt((dmin-n)^2 + 4.nv) / 2 )


extract from conjecture id(up_n_ng_dmin_smax,_41557,_41559) lower bound (low_n_smax_dmin_ng) for ng by inverting upper bound of smax wrt parameters n, ng and dmin
conjecture(low,
           col(low_n_smax_dmin_ng,4),
           ng,
           20,
           10,
           t([col(low_n_smax_dmin_ng,1),col(low_n_smax_dmin_ng,2),col(low_n_smax_dmin_ng,3)],
             [n,     smax,    dmin],
             [_171523,_171609,_171531],
             fceil(plus(polynom([monome([t(_171523,1)],-1),monome([t(_171531,1)],1)]),sqrt(polynom([monome([t(_171531,1),t(_171523,1)],-2),monome([t(_171531,2)],1),monome([t(_171523,2)],1),monome([t(_171609,1)],4)]))),polynom([monome([],2)]))))
ng >= ceil( dmin - n + sqrt(-2.n.dmin + dmin^2 + n^2 + 4.smax ) /  2 )
ng >= ceil( dmin - n + sqrt((dmin-n)^2 + 4.smax ) /  2 )


extract from conjecture id(up_n_ng_dmax,_38563,_38565) lower bound (low_n_dmax_ng) for ng by inverting upper bound of dmax wrt parameters n and ng
conjecture(low,
           col(low_n_dmax_ng,3),
           ng,
           20,
           10,
           t([col(low_n_dmax_ng,1),col(low_n_dmax_ng,2)],
             [n,      dmax],
             [_153877,_153949],
             fceil(plus(polynom([monome([t(_153877,1)],-1),monome([],1)]),sqrt(polynom([monome([t(_153877,2)],1),monome([t(_153949,1)],4),monome([t(_153877,1)],-2),monome([],1)]))),polynom([monome([],2)]))))
ng >= ceil( -n + 1 + sqrt(n^2 + 4.dmax -2.n + 1) / 2 )

extract from conjecture id(up_n_ng_smin_dmax,_37325,_37327) lower bound (low_n_ng_dmax_smin) for smin by inverting upper bound of dmax wrt parameters n, ng and smin
conjecture(low,
           col(low_n_ng_dmax_smin,4),
           smin,
           20,
           10,
           t([col(low_n_ng_dmax_smin,1),col(low_n_ng_dmax_smin,2),col(low_n_ng_dmax_smin,3)],
           [n,     ng,      dmax],
           [_178103,_178107,_178189],
           fceil(plus(polynom([monome([t(_178103,1)],-1),monome([t(_178107,1)],1)]),sqrt(polynom([monome([t(_178103,1),t(_178107,1)],-2),monome([t(_178103,2)],1),monome([t(_178107,2)],1),monome([t(_178189,1)],4)]))),polynom([monome([],2)]))))
smin >= ceil( -n + ng + sqrt(-2.n.ng + n^2 + ng^2 + 4.dmax) / 2 )
smin >= ceil( ng - n + sqrt((ng - n)^2 + 4.dmax) / 2 )

| ?- top(group).

extract from conjecture id(up_n_ng_nv,_45675,_45677) lower bound (low_n_nv_ng) for ng by inverting upper bound of nv wrt parameters n and ng
conjecture(low,
           col(low_n_nv_ng,3),
           ng,
           20,
           10,
           t([col(low_n_nv_ng,1),col(low_n_nv_ng,2)],
             [n,      nv],
             [_124653,_124753],
             fceil(plus(polynom([monome([t(_124653,1)],-1)]),sqrt(polynom([monome([t(_124653,2)],1),monome([t(_124753,1)],4)]))),polynom([monome([],2)]))))
ng >= ceil( -n + sqrt(n^2 + 4.nv) / 2)

extract from conjecture id(up_n_ng_smax,_40529,_40531) lower bound (low_n_smax_ng) for ng by inverting upper bound of smax wrt parameters n and ng
conjecture(low,
           col(low_n_smax_ng,3),
           ng,
           20,
           10,
           t([col(low_n_smax_ng,1),col(low_n_smax_ng,2)],
             [n,      smax],
             [_167725,_167797],
             fceil(plus(polynom([monome([t(_167725,1)],-1),monome([],-1)]),sqrt(polynom([monome([t(_167725,2)],1),monome([t(_167725,1)],2),monome([t(_167797,1)],4),monome([],1)]))),polynom([monome([],2)]))))

ng >= ceil( -n - 1 + sqrt(n^2 + 2.n + 4.smax + 1) / 2 )
*/

/*
extract upper bound for max by inverting lower bound of sum_squares wrt parameters n and max     (sum_squares >= max^2 - max + n)
up(root2)   OK (example1)

extract upper bound for range by inverting lower bound of sum_squares wrt parameters n and range (sum_squares >= range^2 + range + n)
up(root2)   TO CHECK

sum_squares =< (n mod max)^2 - max.(n mod max) + n.max (non traité car on a le test atom(M2))  up_n_max_sum_squares
*/

flag(1). % Flag=1: 6 arguments,  Flag=0: 9 arguments.

top(KindCombi) :-                       % modif
    top(KindCombi, 1, 2).               % modif

top(KindCombi, NParam) :-               % modif
    top(KindCombi, NParam, NParam).     % modif

top(KindCombi, MinNParam, MaxNParam) :- % modif
    max_size_combi(KindCombi, MaxMaxN),                                                       % get max.param.size for which we generate tables for KindCombi
    get_tables(KindCombi, 2, _, _, TableNames),                                               % get all the table names (using the smallest size 2)
    low_up_attributes_combi(KindCombi, ListBoundedParams),
    findall(BoundedParam, member(low-BoundedParam, ListBoundedParams), LBoundedParams),       % get characteristics for which we search lower bounds
    add_index(LBoundedParams, 1, LowBoundedParams),                                           % add index to these characteristics
    findall(BoundedParam, member(up-BoundedParam,  ListBoundedParams), UBoundedParams),       % get characteristics for which we search upper bounds
    add_index(UBoundedParams, 1, UpBoundedParams),                                            % add index to these characteristics
    append(LowBoundedParams, UpBoundedParams, BoundedParams),
    sort(BoundedParams, SortedBoundedParams),
    keys_and_values(SortedBoundedParams, _, AllBoundedParams),                                % get characteristics for which we search a lower or upper bound
    consult_conjecture_files(LBoundedParams, KindCombi, low, MinNParam, MaxNParam), % modif   % consult all conjecture files of object KindCombi containing lower bounds
    consult_conjecture_files(UBoundedParams, KindCombi, up,  MinNParam, MaxNParam), % modif   % consult all conjecture files of object KindCombi containing upper bounds
    flag(Flag), (Flag = 0 ->
    findall(conjecture(Type, Kind, col(Table,IndBound), NameBound, t(IndInputParams, NameInputParams, Formula)), % cmodif ???
            (conjecture(Type,                                                                                    % cmodif ???
                        Kind,                                                                 % construct list of potentially inversible conjectures
                        col(Table,IndBound),
                        NameBound,
                        _MaxN,
                        _Cost,
                        t(IndInputParams, NameInputParams, Vars, Formula),
                        _, _),                                                                % cmodif
             memberchk(Kind, [low,up]),                                                       % focus only on lower and upper bound conjecture (no secondary characteristics)
             findall(IndInput, member(col(_,IndInput),IndInputParams), IndInputs),
             max_member(Max, IndInputs),                                                      % should not mention secondary characteristics as input parameters
             IndBound is Max+1,                                                               % (will check later with metadata that all input parameters and bound parameter are >= 0)
             lists_intersect(NameInputParams, AllBoundedParams),                              % the input parameters should mention at least one input parameter for which
             Vars = NameInputParams),                                                         % we can search for a missing bound
             Conjectures)                                                                     % search missing conjectures by trying to invert some existing conjectures
    ;
    findall(conjecture(id(Table,_,_), Kind, col(Table,IndBound), NameBound, t(IndInputParams, NameInputParams, Formula)), % cmodif ???
            (conjecture(Kind,                                                                 % construct list of potentially inversible conjectures
                        col(Table,IndBound),
                        NameBound,
                        _MaxN,
                        _Cost,
                        t(IndInputParams, NameInputParams, Vars, Formula)),                   % cmodif
             memberchk(Kind, [low,up]),                                                       % focus only on lower and upper bound conjecture (no secondary characteristics)
             findall(IndInput, member(col(_,IndInput),IndInputParams), IndInputs),
             max_member(Max, IndInputs),                                                      % should not mention secondary characteristics as input parameters
             IndBound is Max+1,                                                               % (will check later with metadata that all input parameters and bound parameter are >= 0)
             lists_intersect(NameInputParams, AllBoundedParams),                              % the input parameters should mention at least one input parameter for which
             Vars = NameInputParams),                                                         % we can search for a missing bound
             Conjectures)                                                                     % search missing conjectures by trying to invert some existing conjectures
    ),
    length(Conjectures, NbConjectures),                                                       % get nber.of conjectures and
    init_cpt(conjecture_id, NbConjectures),                                                   % record it to generate an id for the inverted conjecture
    search_potential_missing_conjectures(Conjectures, KindCombi, MinNParam, MaxNParam, MaxMaxN, TableNames, LowBoundedParams, UpBoundedParams), % modif
    false.
top(_, _, _) :- % modif
    flag(Flag), (Flag = 0 -> Arity = 9 ; Arity = 6),
    functor(Term, conjecture, Arity),                                                         % retract all conjecture facts of KindCombi as want to allow one calling top on another combinatorial object
    retractall(Term).

consult_conjecture_files([], _, _, _, _) :- !.                                       % modif  % given a list of characteristics and a given type of bound, i.e. Kind
consult_conjecture_files([BoundedParam|R], KindCombi, Kind, MinNParam, MaxNParam) :- % modif  % load all corresponding conjecture files
    atoms_concat(['data/',KindCombi,'/found_conjectures_',KindCombi,'_',Kind,'_',BoundedParam,'_',MinNParam,'_',MaxNParam,'.pl'], FileName), % modif
    consult(FileName),
    consult_conjecture_files(R, KindCombi, Kind, MinNParam, MaxNParam).              % modif

search_potential_missing_conjectures([], _, _, _, _, _, _, _) :- !. % modif                   % given a list of conjectures search to invert them to extract missing conjectures
search_potential_missing_conjectures([Conjecture|R], KindCombi, MinNParam, MaxNParam, MaxMaxN, TableNames, LowBoundedParams, UpBoundedParams) :- % modif
    search_potential_missing_conjecture(KindCombi, MinNParam, MaxNParam, MaxMaxN, TableNames, Conjecture, LowBoundedParams, UpBoundedParams), % modif
    search_potential_missing_conjectures(R, KindCombi, MinNParam, MaxNParam, MaxMaxN, TableNames, LowBoundedParams, UpBoundedParams). % modif

search_potential_missing_conjecture(KindCombi, MinNParam, MaxNParam, MaxMaxN, TableNames, Conjecture, LowBoundedParams, UpBoundedParams) :- % modif
    Conjecture = conjecture(_Id, _Kind, col(Table,_IndBound), NameBound,                      % try to extract missing bound from the current conjecture Conjecture % cmodif ???
                            t(_IndInputParams, NameInputParams, _Formula)),
%   nl, write(source_conjecture), nl, write(Conjecture), nl,
%   Table = low_n_max_sum_squares,
%   Table = up_n_min_sum_squares,
%   Table = up_n_max_sum_squares,
%   Table = up_n_nval_min_sum_squares,
%   Table = low_n_range_sum_squares,
%   Table = up_n_m_max_sum_squares,
%   Table = low_n_m_max_sum_squares,

    % write('name input params: '), write(NameInputParamsConj), nl,
    
    atoms_concat(['data/',KindCombi,'/data'], DirData),
    gen_table_and_metadata_file_names(DirData, MaxMaxN, Table, _, MetadataFile),              % build path to file name corresponding to the metadata of Table and of the largest availabel size MaxMaxN
    consult(MetadataFile),                                                                    % metadata as need to extract min value of InputParam
    member(InputParam, NameInputParams),                                                      % try to identify a missing bound for the different input parameters
    tab_get_col_name(InputParam, Table, Col),                                                 % check that bound of inverted conjecture is positive as current version of the code only valid when bound is positive
    tab_get_min_max(col(Table,Col), Min, _),                                                  % (if want to handle case when bound is negative would have to generalise identify_square_root_bounds)
    Min >= 0,
    delete(NameInputParams, InputParam, RestInputParams),                                     % remove current input parameter for which we will search a missing bound
    findall(BoundType,                                                                        % search for current input parameter if there exist a missing lower or
            (member(KindBound, [low,up]),                                                     % upper bound wrt the remaining input parameters and the bounded parameter
             (KindBound = low ->                                                              % (which becomes an input parameter of the missing bound)
                OrderedParams = LowBoundedParams
             ;
                OrderedParams = UpBoundedParams
             ),
             memberchk(_-InputParam, OrderedParams),
             \+check_if_not_missing_conjecture(RestInputParams, NameBound, KindBound, InputParam),
             get_table_name_of_missing_conjecture(TableNames, RestInputParams, NameBound, KindBound, InputParam, BoundType)
            ),
            MissingBounds),
    (MissingBounds = [_|_] ->                                                                 % if at least one bound is missing, i.e. a lower or an upper bound
%       write('missing bounds: '), write(MissingBounds), nl,
        search_inverted_conjecture(KindCombi, MinNParam, MaxNParam, MaxMaxN, NameBound, RestInputParams, % modif    % then try to invert current conjecture to isolate bound parameter % cmodif ???
                                   InputParam, Conjecture, MissingBounds)                     % of missing bound
    ;
        true
    ),
    false.                                                                                    % force to backtrack to consider an other input parameter of current conjecture
search_potential_missing_conjecture(_, _, _, _, _, Conjecture, _, _) :- % modif
    Conjecture = conjecture(_, _, col(Table,_), _, _),                                        % succeed after trying all input parameters of current conjecture % cmodif ???
    remove_metadata_facts(Table).                                                             % remove metadata fact that was read at the beginning of search_potential_missing_conjecture

check_if_not_missing_conjecture(RestInputParams, NameBound, BoundType, InputParam) :-         % succed if we have at least one conjecture for a potential missing bound
    insert_elem(RestInputParams, NameBound, InputParams),                                     % insert the old bounded parameter as an input parameter of the potential missing bound
    flag(Flag),
    (Flag = 0 ->
    conjecture(_, BoundType, _, InputParam, _, _, t(_, InputParams, _), _, _)                 % (try to insert it at the different potential positions) % cmodif
    ;
    conjecture(   BoundType, _, InputParam, _, _, t(_, InputParams, _)      )
    ),
    !.                                                                                        % succeed as soon as figure out that the potential missing bound has a conjecture

get_table_name_of_missing_conjecture(TableNames, RestInputParams, NameBound, KindBound, InputParam, BoundType) :-
    insert_elem(RestInputParams, NameBound, InputParams),                                     % try to insert new input parameter at different positions
    atoms_concat_with_underscore([KindBound,InputParams,InputParam], Table),                  % build the table name for which a conjecture was missing
    memberchk(Table, TableNames),                                                             % check its presence the the list of table names
    !,
    (KindBound = low -> BoundType = low(Table) ; BoundType = up(Table)).                      % build the missing bound type

% KindCombi    : kind of combinatorial object we currently consider
% MinNParam    : minimum number of input parameters of conjectures of the conjecture file
% MaxNParam    : maximum number of input parameters of conjectures of the conjecture file
% MaxMaxN      : maximum parameter size for which we generate tables for KindCombi
% Param        : name of the parameter that is bounded by the conjecture Conjecture
% Params       : name of the parameters of the conjecture Conjecture from which we remove the parameter for which we try to find a missing bound
% Bound        : parameter for which we try to find a missing bound
% Conjecture   : conjecture from which we try to extract a new bound on parameter Bound by isolating it from the expression
% MissingBounds: list of missing bounds (bound and table name) for which will try to generate a bound by inverting an existing bound
search_inverted_conjecture(KindCombi, MinNParam, MaxNParam, MaxMaxN, Param, Params, Bound, Conjecture, MissingBounds) :- % modif ???
    BoundParams = [Param|Params],                                                             % input parameters of the new bound we try to extract for parameter Bound
    (check_if_quadratic_conjecture(KindCombi, MaxMaxN, Bound, BoundParams, Conjecture,        % check if current conjecture is a quadratic conjecture that can be inverted
                                   KindNewBound, CorrespondanceNamesVars) ->                  % to find a missing bound for parameter Bound
% write(Conjecture), nl,
        Conjecture = conjecture(SourceConjId, Kind, col(_Table,_IndBound), NameBound, t(_IndInputParams, NameInputParams, _Formula)), % cmodif ???
        (KindNewBound = low(Root) ->                                                          % if found a lower bound only
            (memberchk(low(LowTable), MissingBounds) ->                                       % if did not have yet a lower bound for this characteristics then create a new conjecture
                print_header_extracted_bound(SourceConjId, KindCombi, MinNParam, MaxNParam, MaxMaxN, NameInputParams, Kind, NameBound, low(LowTable-Root), Bound, CorrespondanceNamesVars) % modif ???
            ;
                true
            )
        ;
         KindNewBound = up(Root) ->                                                           % if found an upper bound only
            (memberchk(up(UpTable),  MissingBounds) ->                                        % if did not have yet an upper bound for this characteristics then create a new conjecture
                print_header_extracted_bound(SourceConjId, KindCombi, MinNParam, MaxNParam, MaxMaxN, NameInputParams, Kind, NameBound, up(UpTable-Root),  Bound, CorrespondanceNamesVars) % modif ???
            ;
                true
            )
        ;
            KindNewBound = low_up(Root1,Root2),                                               % if found both a lower and an upper bound
            ((memberchk(low(LowTable), MissingBounds),                                        % if both bounds were missing
                memberchk( up(UpTable),  MissingBounds)) ->                                   % then create two new conjectures
                print_header_extracted_bound(SourceConjId, KindCombi, MinNParam, MaxNParam, MaxMaxN, NameInputParams, Kind, NameBound, low_up(LowTable-Root1,UpTable-Root2), Bound, CorrespondanceNamesVars) % modif ???
            ;
             memberchk(low(LowTable), MissingBounds) ->                                       % if only lower bound was missing then create a new conjecture
                print_header_extracted_bound(SourceConjId, KindCombi, MinNParam, MaxNParam, MaxMaxN, NameInputParams, Kind, NameBound, low(LowTable-Root1), Bound, CorrespondanceNamesVars) % modif ???
            ;
             memberchk(up(UpTable),  MissingBounds) ->                                        % if only upper bound was missing then create a new conjecture
                print_header_extracted_bound(SourceConjId, KindCombi, MinNParam, MaxNParam, MaxMaxN, NameInputParams, Kind, NameBound, up(UpTable-Root2),  Bound, CorrespondanceNamesVars) % modif ???
            ;
                write(search_inverted_conjecture), nl, halt
            )
        )
    ).

check_if_quadratic_conjecture(KindCombi, MaxMaxN, NewBound, NewBoundParams, Conjecture, KindNewBound, CorrespondanceNamesVars) :-

    % CHECK THAT A CONJECTURE IS A QUADRATIC TERM
    % ...........................................
    Conjecture = conjecture(_SourceConjId, Kind, col(Table,IndBound), NameBound, t(IndInputParams, NameInputParams, Formula)), % cmodif ???
    length(NameInputParams, LenInputParams),
    Formula = polynom(Monomes),
    
    get_monome_of_given_degree(Monomes, 2, Monome2),                                          % extract a quadratic term Monome2
    Monome2 = t(M2,2),
    (atom(M2) ->                                                                              % handle a single input parameter (not something like n mod max)
        NewMonomes = Monomes,
        NewMonome2 = Monome2,
        NewM2      = M2
    ;
        write('M2: '), write(M2), nl,
        get_minorant_majorant_wrt_new_bounded_param(KindCombi, M2, NewBound,                  % get minorant/majorant of M2, when possible try to keep NewBound
                                                    Minorant, Majorant),                      % in the minorant and majorant

% write('kind    : '),            write(Kind), nl,
% write('monomes : '),            write(Monomes), nl,
% write('m2      : '),            write(M2), nl,
% write('minorant: '),            write(Minorant), nl,
% write('majorant: '),            write(Majorant), nl,
% write('---> Monomes: '),        write(Monomes), nl,

        substitute_and_simplify(Monomes, Kind, M2,                                            % within the list of monomes replace the term M2 by its minorant or majorant
                                t(Minorant,Majorant),                                         % depending of Kind (low or up) and of the sign of its coefficient, and expand
                                NewMonomes),                                                  % the substituted monomes and simplify by grouping similar monomes
        get_monome_of_given_degree(NewMonomes, 2, NewMonome2),                                % extract quadratic term Monome2
        NewMonome2 = t(NewM2,2)
    ),

% write('--> NewMonomes: '), write(NewMonomes), nl,

    extract_monome(NewMonomes,   NewMonome2, NewCoefsMonome2, RestMonomes1),                  % extract coefficient (NewCoefsMonome2=ACoef) of the quadratic term (and the other terms)
    extract_monome(RestMonomes1, t(NewM2,1), NewCoefsMonome1, NewCoefsMonome0),               % extract other coefficients (NewCoefsMonome1=BCoef, NewCoefsMonome0=CCoef)

    % COMPUTE THE COEFFICIENTS OF THE QUADRATIC EQUATION AS WELL AS ITS ROOTS
    % .......................................................................
    length(NameInputParams, NParams),
    length(Vars,            NParams),                                                         % create a list of fresh variables for the input parameters
    keys_and_values(NameInputParamsVars, NameInputParams, Vars),                              % and replace the input parameter names by fresh variables
    replace_recursively_atoms_by_vars(NewCoefsMonome2, NameInputParamsVars, VCoefsMonome2),   % ACoef
    ACoef = polynom(VCoefsMonome2),                                                           % build correspondance between name of parameters and variables used in Root1 and Root2 
    CorrespondanceNamesVars = [NameBound|NameInputParams]-[VOut|Vars],                        % as will need this correspondance to
                                                                                              % create a conjecture fact for the derived by inversion conj. roots of the quadratic polynom
% write('acoef: '), write(ACoef), nl,
% write('bcoef: '), write(BCoef), nl,
% write('ccoef: '), write(CCoef), nl,

    prod_monomes_coef(NewCoefsMonome1, -1, NamesMinusBCoef),                                                                % -B
    minus_two_polynomes(polynom(NewCoefsMonome0), polynom([monome([t(NameBound,1)],1)]), polynom(NamesMinusCCoefOut)),      % C-Out
    prod_monomes_coef(NewCoefsMonome2, 4, NamesFourACoef),                                                                  % 4.A
    prod_two_polynomes(polynom(NamesFourACoef), polynom(NamesMinusCCoefOut), polynom(NamesProdFourACoefMinusCCoefOut)),     % 4.A.(C-Out)
    prod_two_polynomes(polynom(NewCoefsMonome1), polynom(NewCoefsMonome1), polynom(NamesSquareBCoef)),                      % B^2
    minus_two_polynomes(polynom(NamesSquareBCoef), polynom(NamesProdFourACoefMinusCCoefOut), polynom(NamesSqrt)),           % B^2 - 4.A.(C-Out)
    prod_monomes_coef(NewCoefsMonome2, 2, NamesTwoACoef),

% write('NamesMinusBCoef: '), write(NamesMinusBCoef), nl,
% write('NamesMinusCCoefOut: '), write(NamesMinusCCoefOut), nl,
% write('NamesFourACoef: '), write(NamesFourACoef), nl,
% write('NamesProdFourACoefMinusCCoefOut: '), write(NamesProdFourACoefMinusCCoefOut), nl,
% write('NamesSquareBCoef: '), write(NamesSquareBCoef), nl,
% write('NamesSquareBCoef: '), write(NamesSqrt), nl,
% write('NamesTwoACoef'), write(NamesTwoACoef), nl,

    NameRoot1 = fdiv(minus(polynom(NamesMinusBCoef), sqrt(polynom(NamesSqrt))), polynom(NamesTwoACoef)),
    NameRoot2 = fdiv( plus(polynom(NamesMinusBCoef), sqrt(polynom(NamesSqrt))), polynom(NamesTwoACoef)),

% write('NameRoot1: '), write(NameRoot1), nl,
% write('NameRoot2: '), write(NameRoot2), nl,

    replace_recursively_atoms_by_vars(NameRoot1, [NameBound-VOut|NameInputParamsVars], Root1),
    replace_recursively_atoms_by_vars(NameRoot2, [NameBound-VOut|NameInputParamsVars], Root2),

% write('coef2: '), write(NewCoefsMonome2), write(' '), write(VCoefsMonome2), nl,
% write('coef1: '), write(NewCoefsMonome1), write(' '), write(VCoefsMonome1), nl,
% write('coef0: '), write(NewCoefsMonome0), write(' '), write(VCoefsMonome0), nl, nl,

    % BUILD CORRESPONDANCE BETWEEN (i) INDEX OF INPUT PARAMETER OF NEW BOUND AND (ii) VARIABLES USED IN Root1, Root2
    % ..............................................................................................................
    nth1(PosNewBound, NameInputParams, NewBound),                                             % get name  of NewBound to remove it from the input parameters of current conjecture (as it become an output)
    nth1(PosNewBound, IndInputParams, col(_,IndNewBound)),                                    % get index of NexBound
    findall(InputParam, member(col(_,InputParam), IndInputParams), InputParams),              % input parameters of current conjecture
    keys_and_values(IndInputParamsVars, InputParams, Vars),
    CorIndexVars = [IndBound-VOut|IndInputParamsVars],
    delete(CorIndexVars, IndNewBound-_, CorrepondanceIndexVars),
    sort(CorrepondanceIndexVars, SortedCorrepondanceIndexVars),                               % correspondance between indexes and logical variables of input parameter of the new bound we try to derive
    keys_and_values(SortedCorrepondanceIndexVars, _, SortedVars),                             % extract logical variables (sorted wrt their indexes)
    convert_list_to_term(SortedVars, t, TermSortedVars),                                      % term containing the logical variables that will be the input parameters of the new bound we try to derive

    % LOAD TABLE ASSOCIATED WITH CURRENT CONJECTURE (USED LATER TO EVALUATE THE SIGN OF THE a COEFFICIENT OF A QUADRATIC TERM AND THE SIGN OF ITS ROOTS)
    % ..................................................................................................................................................
    atoms_concat(['data/',KindCombi,'/data'], DirData),
    gen_table_and_metadata_file_names(DirData, MaxMaxN, Table, TableFile, _),                 % build path to file name corresponding to Table and to largest availabel size MaxMaxN
    consult(TableFile),                                                                       % read signature and facts for table of current conjecture Conjecture
    signature(Table, _, Args),                                                                % get description of the different columns of the table Table
    functor(Args, _, NbCols),                                                                 % get number of columns of the table Table
    extract_index_names_from_table_signature(Args, NewBoundParams, NewIndexParams),           % given the names of the input parameters of the new bound(s) we try to extract, extract the corresponding name indexes
    keys_and_values(NewIndexBoundParams, NewIndexParams, NewBoundParams),                     % build the pairs index-name for the input parameters of the new bound(s) we try to extract
    keysort(NewIndexBoundParams, SortedNewIndexBoundParams),                                  % sort pairs index-name by increasing index
    keys_and_values(SortedNewIndexBoundParams, SortedNewIndexParams, _SortedNewBoundParams),  % get sorted indexes of the input parameters of the new bound(s) we try to extract
    functor(TermSource, Table, NbCols),                                                       % create a term for extracting a table entry of the table Table
    functor(TermTarget, t, NParams),                                                          % create a term for extracting just the table entry corresponding to input parameters of the new bound(s) we try to extract
    unify_variables(SortedNewIndexParams, 1, TermSource, TermTarget),                         % unify the two terms to get input parameters of new bound(s) when reading the next table entry

    % FROM THE LOADED TABLE FIND SIGN OF COEF a OF QUADRATIC TERM AND SIGN OF THE ROOT IN ORDER TO FIND A MISSING BOUND
    % .................................................................................................................
    retractall(signs(_,_,_)),                                                                 % no sign/3 fact before calling compute_sign_of_roots_and_acoef_from_all_table_entries/5
    compute_sign_of_roots_and_acoef_from_all_table_entries(TermSource, TermTarget, TermSortedVars, t(ACoef,Root1,Root2), signs(_,_,_)),
    (signs(SignACoef,SignRoot1,SignRoot2) ->                                                  % if coef.A is always >0 or <0 and if at least same sign for Root1 or Root2 then will search for a bound
        retractall(signature(_,_,_)),                                                         % remove signature fact as well as table entries from which derived the quadratic term and its roots
        retractall(TermSource),                                                               % compute potential new bound from quadratic term
        identify_square_root_bounds(Kind, LenInputParams, SignACoef, SignRoot1, SignRoot2, NameRoot1-Root1, NameRoot2-Root2, KindNewBound)
    ;                                                                                         % if could not find a quadratic term that could lead to some bound
        retractall(signature(_,_,_)),                                                         % then remove signature fact as well as
        retractall(TermSource),                                                               % table entries from which derived the quadratic term and its roots
        false                                                                                 % fail as will not for sure be able to generate new conjectures
    ).

% get a minorant and majorant of Monome wrt NewBound
get_minorant_majorant_wrt_new_bounded_param(KindCombi, Monome, NewBound, Minorant, Majorant) :-
    ((Monome = X mod NewBound, X \== NewBound) ->
        Minorant = [                          monome([],0) ], % lower bound of X mod NewBound is 0
        Majorant = [monome([t(NewBound,1)],1),monome([],-1)]  % upper bound of X mod NewBound is NewBound-1
    ;
     (Monome = NewBound mod X, X \== NewBound) ->
        Minorant = [                          monome([],0) ], % lower bound of NewBound mod X is 0
        Majorant = [monome([t(NewBound,1)],1)              ]  % upper bound of NewBound mod X is NewBound (not X-1 as we want to keep if possible NewBound)
    ;
     (memberchk(KindCombi,[group,cgroup]), Monome = min(NewBound,1)) ->
        Minorant = [monome([], 0)],
        Majorant = [monome([t(NewBound,1)],1)]
    ;
     atom_not_in_term(NewBound, Monome) ->
        Minorant = Monome,
        Majorant = Monome
    ;
        write('WARNING: missing minorant or majorant, '), write(get_minorant_majorant_wrt_new_bounded_param(Monome, NewBound)), nl, false
    ).

% Given,
%   Kind            the fact that the initial bound is a lower or upper bound,
%   LenInputParams  number of input parameter of source conjecture (used to check that target conjecture will not loose some parameter)
%   SignACoef       the sign of the coefficient A of the quadratic term from which we try to extract a new bound,
%   SignRoot1       the sign of Root1, 
%   SignRoot2       the sign of Root2,
%   NameRoot1-Root1 the first  root of the quadratic term from which we try to extract a new bound,
%   NameRoot2-Root2 the second root of the quadratic term from which we try to extract a new bound,
% figure out the kind of bound(s) that can be derived by inverting the quadratic term
identify_square_root_bounds(Kind, LenInputParams, SignACoef, SignRoot1, SignRoot2, NameRoot1-Root1, NameRoot2-Root2, KindNewBound) :-
    (SignACoef = 0 -> write(identify_square_root_bounds), nl, halt ; true),
    ((Kind = up,  SignACoef < 0) -> Bound = 1 ;                                               % if initial bound is an upper bound and sign of coefficient a is negative we may have a bound
     (Kind = low, SignACoef > 0) -> Bound = 1 ;                                               % if initial bound is a  lower bound and sign of coefficient a is positive we may have a bound
                                    Bound = 0 ),
    ((integer(SignRoot1), integer(SignRoot2), SignRoot1 >= 0, SignRoot2 >= 0) ->              % if both roots are positive
        (Bound = 1 ->                                                                         % then extract both a lower and upper bound from the quadratic term
            extract_nb_distinct_atoms(NameRoot1, NbAtomsRoot1),
            extract_nb_distinct_atoms(NameRoot2, NbAtomsRoot2),
            ((NbAtomsRoot1 = LenInputParams, NbAtomsRoot2 = LenInputParams) ->                % check that did not loose any input parameter for Root1 and Root2
                KindNewBound = low_up(Root1,Root2)
            ;
             NbAtomsRoot1 = LenInputParams ->
                KindNewBound = low(Root1)
            ;
             NbAtomsRoot2 = LenInputParams ->
                KindNewBound = up(Root2)
            ;
                false
            )
        ;
            false
        )
    ;
     (integer(SignRoot2), SignRoot1 = none, SignRoot2 >= 0) ->                                % if sign of root1 is not fixed wrt all table entries and root2 is positive
        extract_nb_distinct_atoms(NameRoot2, NbAtomsRoot2),                                   % then depending on the sign of a coef. and of type of initial bound extract and upper or lower bound
        (NbAtomsRoot2 =\= LenInputParams ->                                                   % check that did not loose any input parameter for Root2
            false
        ;
         Bound = 1 ->
            KindNewBound = up(Root2)
        ;
            KindNewBound = low(Root2)
        )
    ;
     (integer(SignRoot1), integer(SignRoot2), SignRoot1 < 0, SignRoot2 >= 0) ->               % if root1 is negative and root2 is positive
        extract_nb_distinct_atoms(NameRoot2, NbAtomsRoot2),                                   % then depending on the sign of a coef. and of the type of initial bound extract and upper or lower bound
        (NbAtomsRoot2 =\= LenInputParams ->                                                   % check that did not loose any input parameter for Root2
            false
        ;
         Bound = 1 ->
            KindNewBound = up(Root2)
        ;
            KindNewBound = low(Root2)
        )
    ;
        false
    ).
/*
identify_square_root_bounds(Kind, LenInputParams, SignACoef, SignRoot1, SignRoot2, NameRoot1-Root1, NameRoot2-Root2, KindNewBound) :-
    ((SignRoot1 = none, SignRoot2 >= 0) ->                                                    % if sign of Root1 is not always positive (or always negative) and if sign of root2 is positive
        extract_nb_distinct_atoms(NameRoot2, NbAtomsRoot2),
        (NbAtomsRoot2 =\= LenInputParams ->
            false
        ;
         SignACoef < 0 ->                                                                     % if a coefficient of quadratic term is negative then extract an upper bound from the quadratic term
            KindNewBound = low(Root2)
        ;
            KindNewBound = up(Root2)
        )
    ;
     (SignRoot2 = none, SignRoot1 >= 0) ->                                                    % if sign of Root2 is not always positive (or always negative) and if sign of root1 is positive
        extract_nb_distinct_atoms(NameRoot1, NbAtomsRoot1),
        (NbAtomsRoot1 =\= LenInputParams ->
            false
        ;
         SignACoef < 0 ->                                                                     % if a coefficient of quadratic term is negative then extract an upper bound from the quadratic term
            KindNewBound = low(Root1)
        ;
            KindNewBound = up(Root1)
        )
    ;
        ((Kind = up,  SignACoef < 0) -> Bound = 1 ;                                           % if initial bound is an upper bound and sign of coefficient a is negative we may have a bound
         (Kind = low, SignACoef > 0) -> Bound = 1 ;                                           % if initial bound is a  lower bound and sign of coefficient a is positive we may have a bound
                                        Bound = 0 ),
        extract_nb_distinct_atoms(NameRoot1, NbAtomsRoot1),
        extract_nb_distinct_atoms(NameRoot2, NbAtomsRoot2),
        ((integer(SignRoot1), integer(SignRoot2), SignRoot1 >= 0, SignRoot2 >= 0) ->          % if both roots are positive
            (Bound = 1 ->                                                                     % then extract both a lower and upper bound from the quadratic term
                ((NbAtomsRoot1 = LenInputParams, NbAtomsRoot2 = LenInputParams) ->
                    KindNewBound = low_up(Root1,Root2)
                ;
                 NbAtomsRoot1 = LenInputParams ->
                    KindNewBound = low(Root1)
                ;
                 NbAtomsRoot2 = LenInputParams ->
                    KindNewBound = up(Root2)
                ;
                    false
                )
            ;
                false
            )
        ;
         (integer(SignRoot1), integer(SignRoot2), SignRoot1 < 0, SignRoot2 >= 0) ->           % if root1 is negative and root2 is positive
            (NbAtomsRoot2 =\= LenInputParams ->
                false
            ;
             Bound = 1 ->                                                                     % then depending on the sign of a coef. and of type of initial bound extract and upper or lower bound
                KindNewBound = up(Root2)
            ;
                KindNewBound = low(Root2)
            )
        ;
            false
        )
    ).
*/

% if ACoef is null then fail                                                                  (as we do not have a quadratic formula)
% if ACoef is both positive and negative then fail                                            (as cannot deduce a bound)
% if Root1 is both positive and negative and if Root2 is both positive or negative then fail  (as cannot deduce a bound)
% otherwise if does not fail then return in a fact of the form sign(SignACoef,SignRoot1,SignRoot2) the
% signs of ACoef, Root1 and Root2 (note that one of the sign of Root1 or Root2 may be undefined)
%
% TermSource          : a term corresponding to the table name and its arguments                       (logical variables)
% TermTarget          : a term corresponding to t and the arguments we want to extract from TermSource (logical variable)
% TermSortedVars      : a term t containing the logical variables present in Root1 and Root2
% t(ACoef,Root1,Root2): the a coefficient of the quadratic term and its roots as symbolic formulae
% Signs               : the sign of ACoef, Root1 and Root2 that will be computed
compute_sign_of_roots_and_acoef_from_all_table_entries(TermSource, TermTarget, TermSortedVars, t(ACoef,Root1,Root2), Signs) :-
    assert(Signs),                                                                            % assert previous signs (signs are logical variables as did not already scan table entries)
    call(TermSource),                                                                         % get next table entry: will update signs wrt current table entry
    signs(PrevSignACoef,PrevSignRoot1,PrevSignRoot2),                                         % get previous signs, i.e. the signs computed from the already scanned table entries (note that fail if no sign)
    retractall(signs(_,_,_)),                                                                 % remove current signs as do not want to have any sign in case we fail
    copy_term(TermSortedVars-ACoef, TermTarget-EvalACoef),                                    % replace in ACoef its logical variables (when they are used) by their corresponding values from current table entry
    eval_formula_term(EvalACoef, ValEvalACoef),                                               % evaluate the value of ACoef wrt current table entry
    sign(ValEvalACoef, NextSignACoef),                                                        % evaluate the sign of ACoef wrt current table entry
    (NextSignACoef = 0 ->                                                                     % fail as for the current entry we do not have a quadratic formula
        false
    ;
     (integer(PrevSignACoef), NextSignACoef \== PrevSignACoef) ->                             % fail if current sign of A wrt current table entry is different from sign of A on previous table entries
        false
    ;
        copy_term(TermSortedVars-Root1, TermTarget-EvalRoot1),                                % replace in Root1 its logical variables by their corresponding values from current table entry
        eval_formula_term(EvalRoot1, ValEvalRoot1),                                           % evaluate the value of Root1 wrt current table entry
        sign(ValEvalRoot1, SignRoot1),                                                        % evaluate the sign of Root1 wrt current table entry
        (var(PrevSignRoot1)            -> NextSignRoot1 = SignRoot1     ;                     % if on first table entry then record current sign of Root1
         PrevSignRoot1 = 0             -> NextSignRoot1 = SignRoot1     ;                     % if not on first table entry and Root1 was equal to 0 on the previous table entries the record current sign of Root1
         SignRoot1     = 0             -> NextSignRoot1 = PrevSignRoot1 ;                     % if not on first table entry and current sign of Root1 is 0 then record previous sign of Root1
         SignRoot1     = PrevSignRoot1 -> NextSignRoot1 = PrevSignRoot1 ;                     % if not on first table entry and same sign as on previous entries then keep the sign of Root1
                                          NextSignRoot1 = none          ),                    % record the fact that the sign of Root1 was both negative and positive for different table entries
        copy_term(TermSortedVars-Root2, TermTarget-EvalRoot2),                                % replace in Root2 its logical variables by their corresponding values from current table entry
        eval_formula_term(EvalRoot2, ValEvalRoot2),                                           % evaluate the value of Root2 wrt current table entry
        sign(ValEvalRoot2, SignRoot2),                                                        % evaluate the sign of Root2 wrt current table entry
        (var(PrevSignRoot2)            -> NextSignRoot2 = SignRoot2     ;                     % if on first table entry then record current sign of Root2
         PrevSignRoot2 = 0             -> NextSignRoot2 = SignRoot2     ;                     % if not on first table entry and Root2 was equal to 0 on the previous table entries the record current sign of Root2
         SignRoot2     = 0             -> NextSignRoot2 = PrevSignRoot2 ;                     % if not on first table entry and current sign of Root2 is 0 then record previous sign of Root2
         SignRoot2     = PrevSignRoot2 -> NextSignRoot2 = PrevSignRoot2 ;                     % if not on first table entry and same sign as on previous entries then keep the sign of Root2
                                          NextSignRoot2 = none          ),                    % record the fact that the sign of Root2 was both negative and positive for different table entries
        ((NextSignRoot1 = none, NextSignRoot2 = none) ->                                      % if both Root1 and Root2 had some table entries for which they were negative and positive then fail
            false
        ;
            assert(signs(NextSignACoef, NextSignRoot1, NextSignRoot2)),                       % record the updated signs of ACoef, Root1 and Root2
            false                                                                             % fail to for backtrack on call(TermSource): note that as we assert signs fact signs/3 after call(TermSource) will not fail
        )
    ),
    write(compute_sign_of_roots_and_acoef_from_all_table_entries), nl, halt.                  % should have failed before
compute_sign_of_roots_and_acoef_from_all_table_entries(_, _, _, _, _).                        % succeed once we process all table entries

% extract from a list of monones a term (of a given degree Degree) of one of the monomes
% and check that the extracted term does not occur with a greater degree
get_monome_of_given_degree([Monome|_], Degree, t(M,Degree)) :-
    Monome = monome(Monomes,_),
    member(t(M,Degree), Monomes),
    greater_degree_does_not_exist(M, Degree, Monomes),
    !.
get_monome_of_given_degree([_|R], Degree, Monome) :-
    get_monome_of_given_degree(R, Degree, Monome).

greater_degree_does_not_exist(M, Degree, Monomes) :-
    member(t(M,D), Monomes),
    D > Degree,
    !,
    false.
greater_degree_does_not_exist(_, _, _).

extract_monome([], _, [], []) :- !.
extract_monome([Monome|R], ExtractedMonome, [CoefMonome|S], RestMonomes) :-
    Monome = monome(Monomes,Coef),
    memberchk(ExtractedMonome, Monomes),
    !,
    delete(Monomes, ExtractedMonome, Rest),
    CoefMonome = monome(Rest,Coef),
    extract_monome(R, ExtractedMonome, S, RestMonomes).
extract_monome([Monome|R], ExtractedMonome, CoefMonome, [Monome|S]) :-
    extract_monome(R, ExtractedMonome, CoefMonome, S).

add_index([], _, []) :- !.
add_index([X|R], I, [I-X|S]) :-
    I1 is I+1,
    add_index(R, I1, S).

print_header_extracted_bound(SourceConjId, KindCombi, MinNParam, MaxNParam, MaxMaxN, NameInputParams, Kind, NameBound, KBound, Bound, CorrespondanceNamesVars) :- % cmodif ???
    nl, write('extract from conjecture '),
    write(SourceConjId),
    (KBound = low(LowTable-LowRoot)                   -> write(' lower bound ('), write(LowTable), write(')')                                        ;
     KBound = up(UpTable-UpRoot)                      -> write(' upper bound ('), write(UpTable),  write(')')                                        ;
     KBound = low_up(LowTable-LowRoot,UpTable-UpRoot) -> write(' lower and upper bounds ('), write(LowTable), write(','), write(UpTable), write(')') ;
                                                         write(print_header_extracted_bound(KBound)), nl, halt                                       ),
    write(' for '),
    write(Bound),
    write(' by inverting '), 
    (Kind = low -> write('lower ') ; write('upper ')),
    write('bound of '),
    write(NameBound),
    write(' wrt parameter'),
    length(NameInputParams, N),
    (N > 1 -> write('s ') ; write(' ')),
    write_atoms(NameInputParams),
    nl,
    length(NameInputParams, NInputParams),
    IndBound is NInputParams+1,
    (atom(LowTable) ->
        gen_inverted_conjecture_fact(SourceConjId, KindCombi, MinNParam, MaxNParam, MaxMaxN, IndBound, Bound, CorrespondanceNamesVars, low,  LowTable, LowRoot, LowConjecture), % cmodif ???
        write(LowConjecture), nl
    ;
        true
    ),
    (atom(UpTable) ->
        gen_inverted_conjecture_fact(SourceConjId, KindCombi, MinNParam, MaxNParam, MaxMaxN, IndBound, Bound, CorrespondanceNamesVars, up,   UpTable,  UpRoot,  UpConjecture), % cmodif ???
        write(UpConjecture), nl
    ;
        true
    ).

% generate a new conjecture on a lower or upper bound that was derive from an already existing conjecture whose formula was a quadratic term.
%  SourceConjId           : identifier of the original conjecture that we try to invert % cmodif ???
%  KindCombi              : kind of combinatorial object for which generates missing conjectures
%  MinNParam              : minimum number of input parameters of the conjectures of the conjecture file
%  MaxNParam              : maximum number of input parameters of the conjectures of the conjecture file
%  MaxMaxN                : largest size of combinatorial object we consider
%  IndBound               : index of characteristic for which we generate a new bound
%  Bound                  : characteristic for which we generate a new bound
%  CorrespondanceNamesVars: correspondance between names and logical variables used in Root and in the conjecture that will be generated
%  Kind                   : 'low' if will generate a conjecture on a lower bound, 'up' if will generate a conjecture on an upper bound
%  Table                  : table containing the data that will be used to test whether the newly generated conjecture holds or not
%  Root                   : square root of the quadratic term; used to generate the new bound of the form geq Root if Kind=low (or leq Root if Kind=up)
%  Conjecture             : new conjecture that will be generated
gen_inverted_conjecture_fact(SourceConjId, KindCombi, MinNParam, MaxNParam, MaxMaxN, IndBound, Bound, CorrespondanceNamesVars, Kind, Table, Root, Conjecture) :- % cmodif ???
    (functor(Root, fdiv, 2) -> true ; write(print_header_extracted_bound(Root)), nl, halt),
    CorrespondanceNamesVars = CorrNames-CorrVars,
    length(CorrNames, NParams),                                                               % get number of parameters we want to extract from Table
    atoms_concat(['data/',KindCombi,'/data'], DirData),                                       % build directory name containing the file corresponding to Table
    gen_table_and_metadata_file_names(DirData, MaxMaxN, Table, TableFile, _),                 % build path to file name corresponding to Table and to largest availabel size MaxMaxN
    consult(TableFile),                                                                       % read signature and facts for table of current conjecture Conjecture
    signature(Table, _, Args),                                                                % get description of the different columns of the table Table
    functor(Args, _, NbCols),                                                                 % get number of columns of the table Table
    combine_two_lists_in_a_list_of_terms(CorrNames, CorrVars, t, TermNamesVars),              % creates a list of term of the form t(Name,Var) from CorrespondanceNamesVars)
    add_index_to_terms_name_var(TermNamesVars, NbCols, Args, ListIndexTermNamesVars),         % add index wrt Args to the elements of TermNamesVars (do not use findall as modify variable !)
    keysort(ListIndexTermNamesVars, SortedListIndexTermNamesVars),                            % sort ListIndexTermNamesVars by increasing index (to match order used in Table and use later this order to unify vars.)
    last(SortedListIndexTermNamesVars, LastIndex-t(LastName,_)),
    ((LastIndex = NParams, LastIndex = IndBound, LastName = Bound) ->                         % check soundness: our new bound should use columns 1 up to columns NParams of table Table as
        true                                                                                  % all bound tables are organised in the following way:
    ;                                                                                         % first we have the input parameter, then the bound parameter, and finally the secondary characteristics
        write(gen_inverted_conjecture_fact), nl, halt
    ),
    extract_target_term(SortedListIndexTermNamesVars, NParams,                                % extract target term that contain the variables mentionned in Root and the bound variable itself
                        TermTarget, ListSortedIndex, LastSortedVar),                          % extract corresponding list of indexes as well as the bound variable
    functor(TermSource, Table, NbCols),                                                       % create a term for extracting a table entry of the table Table
    unify_variables(ListSortedIndex, 1,                                                       % unify terms to get input params.and bound value when reading table entries in check_inverted_bound_wrt_table_entries
                    TermSource, TermTarget),                                                  % (note that the variables in Root and the variable LastSortedVar will get fixed when reading next table entry)
    check_inverted_bound_wrt_table_entries(Kind, TermSource, Root, LastSortedVar),            % check new found bound wrt all entries of its table Table
    arg(1, Root, Root1),                                                                      % get numerator of the root of the quadratic term
    arg(2, Root, Root2),                                                                      % get denominator of the root of the quadratic term
    (Kind = low ->                                                                            % if generate a new conjecture on a lower bound
        functor(Formula, fceil,  2)                                                           % then replace the division by a ceil operation (round up to next integer value)
    ;                                                                                         % if generate a new conjecture on an upper bound
        functor(Formula, ffloor, 2) % round down for an upper bound                           % then replace the division by a floor operation (round down to the previous integer value)
    ),
    arg(1, Formula, Root1),                                                                   % create the numerator of the new bound formula
    arg(2, Formula, Root2),                                                                   % create the denominator of the new bound formula
    signature(Table, MaxMaxN, Args),                                                          % get information on columns of biggest table associated with new bound    
    functor(Args, _, NbCols),                                                                 % get number of column of table Table (the associated with the largest size MaxMaxN)
    gen_pairs(CorrNames, CorrVars, CorrPairs),                                                % get pairs of names and corresponding variable in the formula
    findall(col(Table,I), (I in 1..NbCols, indomain(I), arg(I, Args, t(_,   primary,input))), TableColInputParams),
    findall(Name,         (I in 1..NbCols, indomain(I), arg(I, Args, t(Name,primary,input))), Names),
    get_vars_corresponding_to_names(Names, CorrPairs, Vars),                                  % generate conjecture fact that will be added to the appropriate conjecture file
    increment_cpt(conjecture_id, NextConjId),                                                 % cmodif
    functor(MapId, Kind, 1),                                                                  % construct the map id to which the conjecture we construct belongs % cmodif
    arg(1, MapId, Bound),                                                                     % cmodif
    flag(Flag),
    (Flag = 0 ->
    Conjecture = conjecture(id(KindCombi,MapId,NextConjId),                                   % cmodif
                            Kind,                                                             % kind of the conjecture we generate: low or up
                            col(Table,IndBound),                                              % column of the table corresponding to the parameter for which we generate the conjecture
                            Bound,                                                            % name of the parameter for which we generate the conjecture
                            MaxMaxN,                                                          % largest size of combinatorial object we consider
                            10,                                                               % dummy cost for the formula of a conjecture obtained by inversion
                            t(TableColInputParams,                                            % list of input parameters of the conjecture where each element is of the form col(name,index)
                              Names,                                                          % list of names of input parameters of the conjecture
                              Vars,                                                           % list of variables of input parameters of the conjecture
                              Formula),
                            inverted(SourceConjId),                                           % cmodif ???
                            [])                                                               % cmodif ???
    ;
    Conjecture = conjecture(Kind,                                                             % kind of the conjecture we generate: low or up
                            col(Table,IndBound),                                              % column of the table corresponding to the parameter for which we generate the conjecture
                            Bound,                                                            % name of the parameter for which we generate the conjecture
                            MaxMaxN,                                                          % largest size of combinatorial object we consider
                            10,                                                               % dummy cost for the formula of a conjecture obtained by inversion
                            t(TableColInputParams,                                            % list of input parameters of the conjecture where each element is of the form col(name,index)
                              Names,                                                          % list of names of input parameters of the conjecture
                              Vars,                                                           % list of variables of input parameters of the conjecture
                              Formula))                                                       % cmodif ???
    ),
    retractall(signature(_,_,_)),       % remove signature fact  of current table
    functor(TermSource, Table, NbCols), % remove table     facts of current table
    retractall(TermSource),
    extract_target_term(SortedListIndexTermNamesVars, NParams,                                % extract target term that contain the variables mentionned in Root and the bound variable itself
                        TermTarget, ListSortedIndex, LastSortedVar),                          % extract corresponding list of indexes as well as the bound variable
    functor(TermSource, Table, NbCols),                                                       % create a term for extracting a table entry of the table Table
    atoms_concat(['data/',KindCombi,'/found_conjectures_',
                  KindCombi,'_',Kind,'_',Bound,'_',MinNParam,'_',MaxNParam,'.pl'], ConjectureFileName), % modif % create the name of the conjecture file where we need to add the new conjecture found by inversion
    open(ConjectureFileName, append, Stream),                                                 % open the conjecture file where to add the new conjecture (create a new file if did not exist already)
%   portray_clause(Stream, Conjecture),                                                       % add the new conjecture fact at the end
    close(Stream).                                                                            % close conjecture file

add_index_to_terms_name_var([], _, _, []) :- !.
add_index_to_terms_name_var([t(Name,Var)|R], NbCols, Args, [Index-t(Name,Var)|S]) :-
    findall(I, (I in 1..NbCols,
                indomain(I),
                arg(I, Args, t(Name,K,IO)),
                (memberchk(K-IO, [primary-input,low-output,up-output]) -> true ; write(add_index_to_terms_name_var), nl, halt)), [Index]),
    add_index_to_terms_name_var(R, NbCols, Args, S).

extract_target_term(SortedListIndexTermNamesVars, NParams, TermTarget, ListSortedIndex, LastSortedVar) :-
    functor(TermTarget, t, NParams),
    extract_target_term(SortedListIndexTermNamesVars, 1, TermTarget, ListSortedIndex),
    arg(NParams, TermTarget, LastSortedVar).

extract_target_term([], _, _, []) :- !.
extract_target_term([Index-t(_,Var)|R], I, TermTarget, [Index|S]) :-
    arg(I, TermTarget, Var),
    I1 is I+1,
    extract_target_term(R, I1, TermTarget, S).

% check the new inverted lower or upper bound found wrt all table entries attached to the new bound
check_inverted_bound_wrt_table_entries(Kind, TermSource, Root, LastVar) :-
    call(TermSource),
    eval_formula_term(Root, ValRoot),
    (Kind = low ->
        (ValRoot =< LastVar -> true ; write(check_inverted_bound_wrt_table_entries(Kind, TermTermSource, Root, ValRoot, LastVar)), nl, halt)
    ;
        (ValRoot >= LastVar -> true ; write(check_inverted_bound_wrt_table_entries(Kind, TermTermSource, Root, ValRoot, LastVar)), nl, halt)
    ),
    false.
check_inverted_bound_wrt_table_entries(_, _, _, _).

% iterate through the names for which has to find the corresponding variables used in the formula of the conjecture
% as using a findall changes the variables !!!
get_vars_corresponding_to_names([], _, []) :- !.
get_vars_corresponding_to_names([Name|R], CorrPairs, [Var|S]) :-
    memberchk(Name-Var, CorrPairs),
    get_vars_corresponding_to_names(R, CorrPairs, S).

%----------
% [monome([t(n mod max,2)],1),              (n mod max)^2 - max.(n mod max) + n.max
%  monome([t(max,1),t(n mod max,1)],-1),    (max - 1)^2 - max.(max-1) + n.max            monome([t(max - 1,2)],        1) --> monome([t(max,2)],1),       monome([t(max,1)],-1), monome([],1)
%  monome([t(n,1),t(max,1)],1)]                                                          monome([t(max,1),t(max-1,1)],-1) --> monome([t(max,2)],1),       monome([t(max,1)],-1)
% majorant: [monome([t(max,1)],1),monome([],-1)]    max - 1                              monome([t(n,1),t(max,1)],     1) --> monome([t(n,1),t(max,1)],1)
% [monome([t([monome([t(max,1)],1),monome([],-1)],2)],1)-[1],                            CALCULER LA PUISSANCE DE CHAQUE TERME SUBSTITUEE ET FAIRE LE PRODUIT: FAIRE LE PRODUIT DE DEUX POLYNOMES
%  monome([t(max,1),t([monome([],0)],1)],-1)-[2],                                        (IL FAUT QUE LES OBJETS INTERMÉDIARES SOIENT SAINS)
%  monome([t(n,1),t(max,1)],1)-[]]
%        substitute(Kind, Monomes, M2, t(Minorant,Majorant),                                  % in the list of monomes replace the term M2 by its minorant
%                   NewMonomesIndexes),                                                       % or majorant depending of Kind and the sign of its coefficient
%        develop(NewMonomesIndexes, NewMonomes0),                                             % expand the substitued monomes
%        append(NewMonomes0, NewMonomes),                                                     % flatify the list of monomes


% substitute_and_develop([monome([t(n mod max,2)],1),                   (n mod max)^2 - max.(n mod max) + n.max             (max-1)^2  . 1      max^2 - 2.max + 1
%                         monome([t(max,1),t(n mod max,1)],-1),         remplacer n mod max par max-1 et développer
%                         monome([t(n,1),t(max,1)],1)],
%                         up,
%                         n mod max,
%                         t([monome([],0)],
%                           [monome([t(max,1)],1),monome([],-1)]))

%[monome([monome([t(max,2)],1),
%         monome([t(max,1)],-2),
%         monome([],1)],1),
% monome([t(max,1),monome([],0)],-1),
% monome([t(n,1),t(max,1)],1)]

substitute_and_simplify(Monomes, Kind, ReplacedTerm, t(Minorant,Majorant), SimplifiedMonomes) :-
    substitute_and_develop(Monomes, Kind, ReplacedTerm, t(Minorant,Majorant), DevelopedMonomes),
    append(DevelopedMonomes, FlatDevelopedMonomes),
    simplify_polynome(FlatDevelopedMonomes, SimplifiedMonomes).
%   write('developed monomes: '), write(DevelopedMonomes), nl,
%   write('flat developed monomes: '), write(FlatDevelopedMonomes), nl,
%   write('simplified monomes: '), write(SimplifiedMonomes), nl.

substitute_and_develop([], _, _, _, []) :- !.
substitute_and_develop([Monome|R], Kind, ReplacedTerm, t(Minorant,Majorant), Result) :-
    substitute_and_develop_monome(Monome, Kind, ReplacedTerm, t(Minorant,Majorant), NewMonome),
    (NewMonome = [] -> Result = S ; Result = [NewMonome|S]), % as [] corresponds to 0 it is skipped
    substitute_and_develop(R, Kind, ReplacedTerm, t(Minorant,Majorant), S).

substitute_and_develop_monome(Monome, Kind, ReplacedTerm, t(Minorant,Majorant), NewMonomesCoef) :-
    Monome = monome(ListVarDegree, Coef),
%   write('monome: '), write(Monome), nl,
    substitute_monome(ListVarDegree, Coef, Kind, ReplacedTerm, t(Minorant,Majorant), ListTermDegree, Substitute),
    (Substitute = 1 ->
        develop_monome(ListTermDegree, DevelopedMonome),
        prod_polynomes(DevelopedMonome, polynom(NewMonomes)),
        prod_monomes_coef(NewMonomes, Coef, NewMonomesCoef)
%       write('list term degree: '), write(ListTermDegree), nl,
%       write('developed monomes: '), write(DevelopedMonome), nl,
%       write('new monomes: '), write(NewMonomes), nl,
%       write('new monomes coef: '), write(NewMonomesCoef), nl
    ;
        NewMonomesCoef = [Monome]
%       write('new monomes coef (no substitution): '), write(NewMonomesCoef), nl
    ).

prod_monomes_coef([], _, []) :- !.
prod_monomes_coef([monome(Term,C)|R], Coef, Result) :-
    NewC is Coef*C,
    (NewC = 0 ->
        Result = S
    ;
        Result = [monome(Term,NewC)|S]
    ),
    prod_monomes_coef(R, Coef, S).

substitute_monome([], _, _, _, _, [], Substitute) :- !,
    (integer(Substitute) -> true ; Substitute = 0).                                           % if no substitution was done then set Substitute to 0
substitute_monome([t(Term,Degree)|R], Coef, Kind, ReplacedTerm, t(Minorant,Majorant), [NewTermDegree|S], Substitute) :-
    (Term = ReplacedTerm ->                                                                   % if term in current monome list corresponds to the term to replace
        get_replacement_wrt_kind_and_coef(Kind, t(Minorant,Majorant), Coef, ReplacementTerm), % then get the replacement term (depend of type of bound and of sign of monome coefficient
        NewTermDegree = r(ReplacementTerm,Degree),                                            % used functor r to marq the fact that will need to perform some simplification
        Substitute = 1                                                                        % indicate that a substitution was done
    ;
        NewTermDegree = [monome([t(Term,Degree)],1)]                                          % no substitution: copy the term as a list of monomes (one single monome) as will have to make the product
    ),
    substitute_monome(R, Coef, Kind, ReplacedTerm, t(Minorant,Majorant), S, Substitute).      % process the rest of the list of terms of the current monome

develop_monome([], []) :- !.
develop_monome([r(Term,Degree)|R], [polynom(Monomes)|RestMonomes]) :- !,
    power_polynome(polynom(Term), Degree, polynom(Monomes)),
    develop_monome(R, RestMonomes).
develop_monome([M|R], [polynom(M)|S]) :-
    develop_monome(R, S).

% return the minorant or majorant (i.e. the replacement to use) wrt the the kind of bound (low or up) and wrt the sign of the coefficient
get_replacement_wrt_kind_and_coef(Kind, t(Minorant,Majorant), Coef, Replacement) :-
     (Kind = up -> (Coef >= 0 -> Replacement = Majorant ; Replacement = Minorant) ;
                   (Coef >= 0 -> Replacement = Minorant ; Replacement = Majorant) ).

power_polynome(_, 0, polynom([monome([],1)])) :- !.                                           % compute the power of a polynom Polynome to a give degree Degree
power_polynome(Polynome, 1, Polynome) :- !.
power_polynome(Polynome, Degree, PolynomeDegree) :-
    HalfDegree is Degree // 2,
    power_polynome(Polynome, HalfDegree, PolynomeHalfDegree),
    prod_two_polynomes(PolynomeHalfDegree, PolynomeHalfDegree, PolynomeD),
    Odd is Degree mod 2,
    (Odd = 1 ->
        prod_two_polynomes(Polynome, PolynomeD, PolynomeDegree)
    ;
        PolynomeDegree = PolynomeD
    ).

prod_polynomes([], []) :- !.
prod_polynomes([Polynome], Polynome) :- !.                                                    % given a list of polynoms, compute the product of the polynoms of this list
prod_polynomes([Polynome1,Polynome2|R], ProdPolynomes) :-
    prod_two_polynomes(Polynome1, Polynome2, Polynome12),
    prod_polynomes([Polynome12|R], ProdPolynomes).

prod_two_polynomes(Polynome1, Polynome2, Polynome12) :-                                       % given two polynoms, compute their product
    Polynome1  = polynom(Monomes1),
    Polynome2  = polynom(Monomes2),
    Polynome12 = polynom(Monomes12),
    prod_two_polynomes0(Monomes1, Monomes2, Monomes12).

prod_two_polynomes0(Polynome1, Polynome2, ResPolynome) :-                                     % compute the product of two polynomes Polynome1 and Polynome2
    prod_two_polynomes0(Polynome1, Polynome2, Polynome12, []),                                % make the product of all pairs of monomes steeming from Polynome1 and Polynome2
    simplify_polynome(Polynome12, ResPolynome).                                               % factor out similar monomes

prod_two_polynomes0([], _, NewAnchor, NewAnchor) :- !.
prod_two_polynomes0([Monome1|R], Polynome2, Anchor, NewAnchor) :-
    prod_polynome_monome(Polynome2, Monome1, Anchor, NextAnchor),
    prod_two_polynomes0(R, Polynome2, NextAnchor, NewAnchor).

prod_polynome_monome([], _, NewAnchor, NewAnchor) :- !.                                       % given a list of monomes and a monome, compute their product
prod_polynome_monome([Monome2|R], Monome1, Anchor, NewAnchor) :-
    prod_two_monomes(Monome1, Monome2, Monome12),
    Anchor = [Monome12|NextAnchor],
    prod_polynome_monome(R, Monome1, NextAnchor, NewAnchor).

minus_two_polynomes(Polynome1, Polynome2, Polynome12) :-                                      % given two polynoms Polynome1 and Polynome2, compute Polynome1-Polynome2
    Polynome1  = polynom(Monomes1),
    Polynome2  = polynom(Monomes2),
    Polynome12 = polynom(Monomes12),
    minus_two_polynomes0(Monomes1, Monomes2, Monomes12).

minus_two_polynomes0(Monomes1, Monomes2, Monomes12) :-
    prod_monomes_coef(Monomes2, -1, MinusMonomes2),
    append(Monomes1, MinusMonomes2, Monomes1MinusMonomes2),
    simplify_polynome(Monomes1MinusMonomes2, Monomes12).

simplify_polynome(Polynome, SimplifiedPolynome) :-                                            % simplify polynome Polynome by grouping together similar monomes
    compute_key_monomes(Polynome, KeyPolynome),
    keysort(KeyPolynome, SortedKeyPolynome),
    keys_and_values(SortedKeyPolynome, _, SortedPolynome),
    merge_consecutive_similar_monomes(SortedPolynome, SimplifiedPolynome).

merge_consecutive_similar_monomes(Polynome, SimplifiedPolynome) :-
    merge_consecutive_similar_monomes0(Polynome, SPolynome),
    (SPolynome = [] ->                                                                        % an empty list should be interpreted as constant 0
        SimplifiedPolynome = monome([], 0)                                                    % create a monome corresponding to 0
    ;                                                                                         % if simplification did not give value 0
        SimplifiedPolynome = SPolynome                                                        % then return obtained simplification
    ).

merge_consecutive_similar_monomes0([Monome], [Monome]) :- !.                                   % if only one monome then return it
merge_consecutive_similar_monomes0([Monome1,Monome2|R], SimplifiedPolynome) :-
    Monome1 = monome(Terms1, Coef1),                                                          % get first  monome
    Monome2 = monome(Terms2, Coef2),                                                          % get second monome
    (Terms1 = Terms2 ->                                                                       % if first and second monomes have the same set of variables (remember that variables of a monome are sorted)
        Coef12 is Coef1+Coef2,                                                                % sum up coefficients of two consecutive monomes that have the same set of variables
        (Coef12 = 0 ->                                                                        % if the coefficients of the two monomes cancel out
            (R = [] ->
                SimplifiedPolynome = []
            ;
                merge_consecutive_similar_monomes0(R, SimplifiedPolynome)                     % then simplify the remaining monomes
            )
        ;                                                                                     % if the coefficients of the two monomes do not cancel out
            Monome12 = monome(Terms1, Coef12),                                                % the create a merged monome
            merge_consecutive_similar_monomes0([Monome12|R], SimplifiedPolynome)              % and try to simplify the merged monome with the remaining monomes
        )
    ;                                                                                         % if first and second monomes do not have the same set of variables
        merge_consecutive_similar_monomes0([Monome2|R], Polynome),                            % then first simplify the second monomes and the remaining monomes
        SimplifiedPolynome = [Monome1|Polynome]                                               % and construct the simplified polynome
    ).

compute_key_monomes([], []) :- !.                                                             % compute the key for each monome of a polynome in order to later
compute_key_monomes([Monome|R], [Key-Monome|S]) :-                                            % sort the monomes and group together similar monomes of a polynome
    compute_key_monome(Monome, Key),
    compute_key_monomes(R, S).

compute_key_monome(monome(Terms,_), t(NegSumDegrees,Terms)) :-                                % compute the key of a monome: sum of the degrees and variable names with exponents
    findall(Degree, member(t(_,Degree),Terms), Degrees),
    sumlist(Degrees, SumDegrees),
    NegSumDegrees is -SumDegrees.                                                             % multiply sum of degrees by -1 as want to sort monomes by decreasing degrees

prod_two_monomes(monome(_,0), _, monome([],0)) :- !.                                          % if coefficient of first  monome is zero then return 0
prod_two_monomes(_, monome(_,0), monome([],0)) :- !.                                          % if coefficient of second monome is zero then return 0
prod_two_monomes(monome([],Coef1), monome([],Coef2), monome([],Coef12)) :- !,                 % if no variable return just a coefficient
    Coef12 is Coef1*Coef2.
prod_two_monomes(monome([],Coef1), monome(Terms2,Coef2), monome(Terms2,Coef12)) :- !,         % if no variable on first term return variables of second term and updated coefficient
    Coef12 is Coef1*Coef2.
prod_two_monomes(monome(Terms1,Coef1), monome([],Coef2), monome(Terms1,Coef12)) :- !,         % if no variable on second term return variables of first term and updated coefficient
    Coef12 is Coef1*Coef2.
prod_two_monomes(monome(Terms1,Coef1), monome(Terms2,Coef2), monome(SortedVars,Coef12)) :-
    prod_terms_two_monomes(Terms1, Terms2, Anchor, []),
    Coef12 is Coef1*Coef2,
    sort_list_terms2_by_reversing_args(Anchor, SortedVars).

prod_terms_two_monomes([], [], NewAnchor, NewAnchor) :- !.                                    % do the product of the lists of variables of two monomes
prod_terms_two_monomes([], Terms2, Anchor, NewAnchor) :- !,                                   % copy the second list at the end of the anchored list
    copy_monomes_to_anchored_list(Terms2, Anchor, NewAnchor).
prod_terms_two_monomes([t(Var1,Degree1)|R], Terms2, Anchor, NewAnchor) :-
    (del_chk(Terms2, t(Var1,Degree2), RestTerms2) ->
        Degree12 is Degree1 + Degree2,
        (Degree12 = 0 ->                                                                      % if computed exponent is 0
            Anchor = NextAnchor                                                               % then do not copy monome as Var1^0 = 1
        ;                                                                                     % else copy monome with updated degree
            Anchor = [t(Var1,Degree12)|NextAnchor]
        )
    ;
        (Degree1 = 0 ->                                                                       % if exponent of current monome is 0
            Anchor = NextAnchor                                                               % then do not copy monome as Var1^0 = 1
        ;                                                                                     % else copy monome
            Anchor = [t(Var1,Degree1)|NextAnchor]
        ),
        RestTerms2 = Terms2
    ),
    prod_terms_two_monomes(R, RestTerms2, NextAnchor, NewAnchor).

sort_list_terms2_by_reversing_args(Terms, SortedTerms) :-                                     % sort a list of monomes in order to put consecutively
    add_key_arg(Terms, KeyTerms),                                                             % similar monomes in order to regroup them later on
    keysort(KeyTerms, SortedKeyTerms),
    keys_and_values(SortedKeyTerms, _, SortedTerms).

% given a list L1 of terms of arity 2, build a new list L2 where each element of L2 is an element of L1
% to which we add a key consisting of the element L1 from which we inverse the argument
% (as will sort first on the decreasing degree and then on the lexicographically increasing variable names)
add_key_arg([], []) :- !.
add_key_arg([Term|R], [Key-Term|S]) :-
    functor(Term, Functor, 2),
    arg(1, Term, Arg1),
    arg(2, Term, Arg2),
    convert_arg_before_sorting(Arg1, NewArg1),
    convert_arg_before_sorting(Arg2, NewArg2),
    functor(Key, Functor, 2),
    arg(1, Key, NewArg2),
    arg(2, Key, NewArg1),
    add_key_arg(R, S).

convert_arg_before_sorting(Arg, NewArg) :-
    (integer(Arg) -> NewArg is -Arg ;                                                         % invert integer as sort by decreasing degree
                     NewArg = Arg   ).                                                        % the rest is kept unchanged as sorted by increasing order

copy_monomes_to_anchored_list([], NewAnchor, NewAnchor) :- !.
copy_monomes_to_anchored_list([t(Var,Degree)|R], Anchor, NewAnchor) :-
    (Degree = 0 ->                                                                            % if exponent of current monome is 0
        Anchor = NextAnchor                                                                   % then do not copy monome as Var1^0 = 1
    ;                                                                                         % else copy monome
        Anchor = [t(Var,Degree)|NextAnchor]
    ),
    copy_monomes_to_anchored_list(R, NextAnchor, NewAnchor).

del_chk([E|R], E, R) :- !.                                                                    % extract the first occurrence of an element from a list and
del_chk([E|R], F, [E|S]) :-                                                                   % return the list from which the first occurrence of that element was removed
    del_chk(R, F, S).

try1 :-
    Monome1 = monome([t(x,1),t(y,1)], 1),
    Monome2 = monome([t(x,1),t(y,1)], 1),
    Monome3 = monome([], 0),
    Monome4 = monome([t(x,2),t(y,1),t(z,2),t(w,3)], 1),
    prod_two_monomes(Monome1, Monome2, Res1),
    write(Res1), nl,
    prod_2monomes(Monome1, Monome2, Res2),
    write(Res2), nl,
    prod_two_monomes(Monome1, Monome3, Res3),
    write(Res3), nl,
    prod_2monomes(Monome1, Monome3, Res4),
    write(Res4), nl,
    prod_two_monomes(Monome1, Monome4, Res5),
    write(Res5), nl,
    prod_2monomes(Monome1, Monome4, Res6),
    write(Res6), nl.

% [monome([t(x,1),t(y,1),t(z,1)], 2),
%  monome([t(x,1),t(z,1)],        4),
%  monome([t(y,2)],               1),
%  monome([t(y,1)],               2),
%  monome([t(y,1)],              -3),
%  monome([],                    -6)]

% [polynom([monome([t(x,3)],1),
%           monome([t(x,2),t(y,1)],3),
%           monome([t(y,3)],1),
%           monome([t(y,2),t(x,1)],3)])]
try2 :-
    Polynome1 = polynom([monome([t(x,1),t(z,1)],2), monome([t(y,1)], 1), monome([],-3)]),
    Polynome2 = polynom([monome([t(y,1)],       1), monome([],       2)               ]),
    Polynome3 = polynom([monome([t(x,1)],       1), monome([t(y,1)], 1)               ]),
    Polynome4 = polynom([monome([t(x,1)],       1), monome([t(y,1)],-1)               ]),
    prod_two_polynomes(Polynome1, Polynome2, Res1),
    write(Res1), nl,
    prod_polynomes([Polynome3,Polynome3,Polynome3], Res2),
    write(Res2), nl,
    prod_polynomes([Polynome4,Polynome4,Polynome4], Res3),
    write(Res3), nl,
    prod_polynomes([Polynome3,Polynome3,Polynome3,Polynome3], Res4),
    write(Res4), nl,
    prod_polynomes([Polynome4,Polynome4,Polynome4,Polynome4], Res5),
    write(Res5), nl,
    power_polynome(Polynome3, 3, Res6),
    write(Res6), nl, (Res2 = Res6 -> true ; write(pb1), nl, halt),
    power_polynome(Polynome4, 3, Res7),
    write(Res7), nl, (Res3 = Res7 -> true ; write(pb2), nl, halt),
    power_polynome(Polynome3, 4, Res8),
    write(Res8), nl, (Res4 = Res8 -> true ; write(pb3), nl, halt),
    power_polynome(Polynome4, 4, Res9),
    write(Res9), nl, (Res5 = Res9 -> true ; write(pb4), nl, halt).
