% This compute the difference between two list of conjectures (one list contain bool and poly formulae and the other just poly formulae) of a map.

:- use_module(library(lists)).
:- use_module(library(clpfd)).
:- use_module(utility).





get_conj(ListTypesFormula0, BoolOrPoly, KindCombi, KindBound, Bound, ListConjecturesSorted,NbConj):-
    functor(Bound,LowUp,1),
    arg(1,Bound,KindBound),
    atoms_concat([KindCombi,'_',LowUp,'_',KindBound], FilesOutSuffix),
	atoms_concat(['data',BoolOrPoly,'/',KindCombi,'/conjectures_',KindCombi],DirConj),
    atoms_concat([DirConj,'/found_conjectures_',FilesOutSuffix,'.pl'], ConjecturesFileName),
    consult(ConjecturesFileName),
    functor(Conjecture,conjecture,9),
	findall(Table,(call(Conjecture),
            		arg(3,Conjecture,col(Table,_))
                   ),ListTables0),
    sort(ListTables0,ListTables),
    findall(Conjecture,(
              member(Table,ListTables),%Table = low_maxc_maxs_mina,
              call(Conjecture),
              arg(3,Conjecture,col(Table,_I)),
              arg(8,Conjecture,HighTypeFormula), %HighTypeFormula = cond_ex,
              arg(7,Conjecture,Formula),
              arg(4,Formula,BoolPolyFormula),
              functor(BoolPolyFormula,TypeFormula,_),
              (ListTypesFormula0 = [cond_ex] -> ListTypesFormula = [if] ; ListTypesFormula0 = ListTypesFormula),
              memberchk(TypeFormula,ListTypesFormula),
              (ListTypesFormula = [bool] -> true;
               ListTypesFormula = [cases] -> true;
               ListTypesFormula = [if] -> HighTypeFormula = cond_ex;
              memberchk(HighTypeFormula,[formula,cond])
               )),
              ListConjectures),
    retractall(tabl(_,_,_)),
    length(ListConjectures,NbConj),%write(NbConj-ListConjectures),nl,halt,
    sort(ListConjectures,ListConjecturesSorted),
    retractall(Conjecture).

get_maps(Maps):-
	consult('cmds_for_maps.pl'),
    findall(m(Object,Bound,KindBound),(
                                       obj_map(_,Object,Bound,Kind),
                                       functor(KindBound,Kind,1)
                                       ),Maps),
	retractall(obj_map(_,_,_,_)).



%%%%%%%%%% BoolOrCasesOrCondEx = if or BoolOrCasesOrCondEx = bool or BoolOrCasesOrCondEx = cases
top(BoolOrCasesOrCondEx):-nl,

    PolyFormula = [polynom,plus,minus,abs,min,max,prod,floor,ceil,mod,cmod,dmod,fmod,power,cdiv,fdiv,ffloor,fceil,geq0,sum_consec,square,sqrt,if],
                                
                                
    get_maps(Maps),
    findall(MapStat,(
    				member(Map,Maps),
    				Map = m(KindCombi, KindBound, Bound),%\+KindCombi = cgroup,
    				stat_found_conj(PolyFormula,[BoolOrCasesOrCondEx], KindCombi, KindBound, Bound,MapStat)
                     ),ListMapStat),
    member(KindCombi,[graph,tree,forest,forest0,partition,partition0,group,cgroup]),
    findall(MapStatKindCombi,(
                              member(MapStatKindCombi,ListMapStat),
                              MapStatKindCombi = map(KindCombi, _,_,_,_,_)
                              ),ListMapStatKindCombi),
    somme_mapstat(BoolOrCasesOrCondEx,ListMapStatKindCombi,KindCombi,[0,0]),nl,nl,
    fail.
top(_).
           
somme_mapstat(BoolOrCasesOrCondEx,[],KindCombi,[BoolRemplPoly,BoolSansPoly]):-
    NbBoolConj is BoolRemplPoly + BoolSansPoly,
    (KindCombi = forest0 -> KindCombi0 = forest2; KindCombi = KindCombi0),
 	atoms_concat(['stats(',KindCombi0,',',BoolOrCasesOrCondEx,'_rempl_poly(',BoolRemplPoly,'),new_',BoolOrCasesOrCondEx,'(',BoolSansPoly,'),total_',BoolOrCasesOrCondEx,'(',NbBoolConj,'))'],Stats),
    write(Stats),!.
somme_mapstat(BoolOrCasesOrCondEx,[MapStat|R],KindCombi,[BoolRemplPoly0,BoolSansPoly0]):-
           MapStat = map(KindCombi, _Bound,T1,T2,_,total_poly(_NbPolyConj)),
	functor(T1,_,1),
	functor(T2,_,1),
	arg(1,T1,BoolRemplPoly),
	arg(1,T2,BoolSansPoly),
    BoolRemplPoly1 is BoolRemplPoly0 + BoolRemplPoly,
    BoolSansPoly1 is BoolSansPoly0 + BoolSansPoly,
    somme_mapstat(BoolOrCasesOrCondEx,R,KindCombi,[BoolRemplPoly1,BoolSansPoly1]).
           

stat_found_conj(PolyFormula,[BoolOrCasesOrCondEx], KindCombi, KindBound, Bound,MapStat):-
    get_conj([BoolOrCasesOrCondEx], '_test_1_tous', KindCombi, KindBound, Bound, ListDoublConjBool,NbBoolConj),
    get_conj(PolyFormula, '_test_1_poly_cond', KindCombi, KindBound, Bound, ListDoublConjPoly,NbPolyConj),
    findall(Char,(member(Conj,ListDoublConjBool),
                 arg(2,Conj,LowUpSec),
                 arg(3,Conj,col(Table,NbCol)),
                 functor(Conj2,conjecture,9),
                 arg(2,Conj2,LowUpSec),
                 arg(3,Conj2,col(Table,NbCol)),
                 memberchk(Conj2,ListDoublConjPoly),
                 arg(4,Conj,Char)),
           ListBoolRemplPoly),
    length(ListBoolRemplPoly,BoolRemplPoly),
    BoolSansPoly is NbBoolConj - BoolRemplPoly,
    functor(MapStat,map,6),
    arg(1,MapStat,KindCombi),
	arg(2,MapStat,Bound),
	arg(3,MapStat,FBoolRemplPoly),
    atom_concat(BoolOrCasesOrCondEx,'_rempl_poly',NBoolRemplPoly),
    functor(FBoolRemplPoly,NBoolRemplPoly,1),
    arg(1,FBoolRemplPoly,BoolRemplPoly),
	arg(4,MapStat,FBoolSansPoly),
	atom_concat('new_',BoolOrCasesOrCondEx,NBoolSansPoly),
	functor(FBoolSansPoly,NBoolSansPoly,1),
	arg(1,FBoolSansPoly,BoolSansPoly),
	arg(5,MapStat,FNbBoolConj),
	atom_concat('total_',BoolOrCasesOrCondEx,NNbBoolConj),
	functor(FNbBoolConj,NNbBoolConj,1),
	arg(1,FNbBoolConj,NbBoolConj),
	arg(6,MapStat,FNbPolyConj),
	functor(FNbPolyConj,total_poly,1),
	arg(1,FNbPolyConj,NbPolyConj).
