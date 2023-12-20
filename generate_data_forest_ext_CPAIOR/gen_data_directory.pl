%%%Get results of bound seeker from CALCUL CANADA %%%%%%%%%%

:- use_module(library(lists)).
:- use_module(library(file_systems)).
:- use_module(library(process)).
:- use_module(library(clpfd)).



gen_directory:-
	member(Object,[forest,forest0,tree]),
	atoms_concat(['mkdir data_',Object],BashCommand0),
	atoms_concat(['mkdir ext_',Object],BashCommand1),
	process_create(path(sh),['-c', BashCommand0], [wait(exit(0))]),
	process_create(path(sh),['-c', BashCommand1], [wait(exit(0))]),
	Size in 2..22,
	indomain(Size),
	atoms_concat(['mkdir data_',Object,'/data',Size],BashCommand),
	process_create(path(sh),['-c', BashCommand], [wait(exit(0))]),
	fail.
gen_directory.




atoms_concat([Atom|R], Final) :-
    to_atom(Atom, AtomC),
    atoms_concat(R, AtomC, Final).

atoms_concat([], Final, Final) :- !.
atoms_concat([Atom|R], Prev, Final) :-
    to_atom(Atom, AtomC),
    atom_concat(Prev, AtomC, Cur),
    atoms_concat(R, Cur, Final).


% convert to atoms
to_atom(X,X):-
        atom(X),
        !.
to_atom(X,Y):-
        number(X),
        number_codes(X,L),
        atom_codes(Y,L).
