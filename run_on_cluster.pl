%%%Get results of bound seeker from CALCUL CANADA %%%%%%%%%%

:- use_module(library(lists)).
:- use_module(library(file_systems)).
:- use_module(library(process)).
:- use_module(library(clpfd)).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
     %%%%%                    GENERATION DES TÂCHES POUR CALCUL CANADA
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

combojects([graph,forest,forest0,tree,partition,partition0,group,cgroup]).

submit_job(ResultsVersion):-
	NumJobsGroup = 1,
	soumettre_jobs(NumJobsGroup,ResultsVersion).

soumettre_jobs(NumJobsGroup,ResultsVersion):-
	IDG in 1..NumJobsGroup,
	indomain(IDG),
	atoms_concat(['sbatch data',ResultsVersion,'/jobs_',IDG,'/job_group_',IDG,'.sh > data',ResultsVersion,'/job_record_',IDG,'.tex'],BashCommand),
	process_create(path(sh),['-c', BashCommand], [wait(exit(0))]),
	fail.
soumettre_jobs(_,_).


gen_tache(ResultsVersion):-
    make_dir_all_objs(ResultsVersion),
    atoms_concat(['maps_to_run_',ResultsVersion,'.pl'],MapsToRunFile),
    consult(MapsToRunFile),
    assert(jobIDG(0)),
    job_to_run(IDG0,TimeGroupJob,Jobs),
    \+ Jobs = [],
    jobIDG(IDG00),
    retract(jobIDG(IDG00)),
    IDG is IDG00 + 1,
    assert(jobIDG(IDG)),
    (IDG0 = to_split -> Hours = 96, Minutes = 00,
                      compute_num_threads(Jobs,0,NumThreads)
                      ;
                        Hours is TimeGroupJob div 60,
                        Minutes is TimeGroupJob mod 60,
                        length(Jobs,NumThreads)
     ),
    atoms_concat(['data',ResultsVersion,'/jobs_',IDG],DirJobGroup),
    make_directory(DirJobGroup),
    atoms_concat([DirJobGroup,'/obj_map_id_times_rksplit_',IDG,'.pl'],ObjMapIdTimesRksplit),
    open(ObjMapIdTimesRksplit,write,StreamJ),
    format(StreamJ,':- multifile obj_map_id_times_rksplit/5.~n',[]),
    format(StreamJ,':- dynamic obj_map_id_times_rksplit/5.~n~n',[]),
    format(StreamJ,' %obj_map_id_times_rksplit(Obj,Bound,JobID,NumTimes,RankSplit)~n~n',[]),
    atoms_concat([DirJobGroup,'/job_group_',IDG,'.sh'],JobGroupFile),
    atoms_concat([DirJobGroup,'/threads_',IDG,'.tex'], ThreadsJobGroupFile),
    open(ThreadsJobGroupFile,write,Stream),
    gen_threads_job_group_file(IDG0,1,1,Jobs,Stream,StreamJ),
    close(Stream),
    close(StreamJ),
    open(JobGroupFile,write,Sout),
    format(Sout,'#!/bin/bash~n',[]),
    format(Sout,'#SBATCH --time=~w:~w:00~n',[Hours, Minutes]),
    format(Sout,'#SBATCH --account=def-cquimper~n',[]),
    format(Sout,'#SBATCH --mem-per-cpu=10G~n',[]),
    format(Sout,'#SBATCH --array=1-~w~n',[NumThreads]),
    format(Sout,'#SBATCH --output=data~w/jobs_~w/job_%a.out~n',[ResultsVersion,IDG]),
    format(Sout,'eval ./gen_paralle_conj.sh `awk "NR==$SLURM_ARRAY_TASK_ID" ~w`~n',[ThreadsJobGroupFile]),
    close(Sout),
    fail.

gen_tache(ResultsVersion):-
atoms_concat(['cp maps_to_run_',ResultsVersion,'.pl data',ResultsVersion],BashCommand),
process_create(path(sh),['-c', BashCommand], [wait(exit(0))]),
retractall(job_to_run(_,_,_)).


make_dir_all_objs(ResultsVersion):-
combojects(Objs),
atoms_concat(['data',ResultsVersion],KeepingDirResults),
make_directory(KeepingDirResults),
consult('cmds_for_maps.pl'),
member(Obj,Objs),
atoms_concat([KeepingDirResults,'/',Obj,'_v',ResultsVersion],FinalDirResultObj),
make_directory(FinalDirResultObj),
atoms_concat([KeepingDirResults,'/',Obj],InterDirResultObj),
make_directory(InterDirResultObj),
atoms_concat([KeepingDirResults,'/',Obj,'/conjectures_',Obj],ConjDir),
make_directory(ConjDir),
atoms_concat([KeepingDirResults,'/',Obj,'/trace_',Obj],TraceDir),
make_directory(TraceDir),
obj_map(_,Obj,Att,LowUp),
atoms_concat([KeepingDirResults,'/',Obj,'/',LowUp,'_',Att],BoundDir),
make_directory(BoundDir),
fail.

make_dir_all_objs(_):-
retractall(obj_map(_,_,_,_)).

compute_num_threads([],NumThreads,NumThreads):-!.
compute_num_threads([jtr(_,_,_,NumTimes)|R],NumThreads0,NumThreads):-
NumThreads1 is NumThreads0 + NumTimes,
compute_num_threads(R,NumThreads1,NumThreads).


gen_threads_job_group_file(_,_,_,[],_,_):-!.
gen_threads_job_group_file(IDG0,J,I,[Job|R],Stream,StreamJ):-
(IDG0 = to_split -> Job = jtr(Obj,Bound,Cmd,NumTimes),
                    write_treads(Stream,J,1,Cmd,NumTimes,Obj,Bound,StreamJ,Js);
                    Job = jtr(Obj,Bound,Cmd0,NumTimes,RankSplit),
                    atoms_concat(['\'',Cmd0,'(1,3,',NumTimes,',',RankSplit,').\''],Cmd),
                    format(Stream,'~w~n',[Cmd]),
                    format(StreamJ,'obj_map_id_times_rksplit(~w,~w,~w,~w,~w).~n',[Obj,Bound,I,NumTimes,RankSplit])
 ),I1 is I + 1,
gen_threads_job_group_file(IDG0,Js,I1,R,Stream,StreamJ).

write_treads(_,J,I,_,Times,_,_,_,J):-I > Times,!.
write_treads(Stream,J,I,Cmd0,Times,Obj,Bound,StreamJ,Jsplits):-
    atoms_concat(['\'',Cmd0,'(1,3,',Times,',',I,').\''],Cmd),
    format(Stream,'~w~n',[Cmd]),
    I1 is I + 1,
    J1 is J + 1,
    format(StreamJ,'obj_map_id_times_rksplit(~w,~w,~w,~w,~w).~n',[Obj,Bound,J,Times,I]),
    write_treads(Stream,J1,I1,Cmd0,Times,Obj,Bound,StreamJ,Jsplits).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
     %%%%%                    RECUPERATION DES RESULTATS CALCUL CANADA
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

get_results(ResultsVersion):-
	rebuild_jobs_groups_results(ResultsVersion).

rebuild_jobs_groups_results(ResultsVersion):-
	rebuild_results(ResultsVersion),
	get_number_of_jobs_goups_to_run(ResultsVersion,NumJobs),
	cp(NumJobs,ResultsVersion),
	atoms_concat(['data',ResultsVersion],KeepingDirResults),
	cat_final_results_obj(KeepingDirResults,ResultsVersion).


get_number_of_jobs_goups_to_run(ResultsVersion,_):-
	assert(num_jobs(0)),
	atoms_concat(['data',ResultsVersion,'/maps_to_run_',ResultsVersion,'.pl'],MapsToRun),
	consult(MapsToRun),
	job_to_run(_,_,Jobs),
	\+ Jobs = [],
	num_jobs(NumJobs0),
	retract(num_jobs(_)),
	NumJobs1 is NumJobs0 + 1,
	assert(num_jobs(NumJobs1)),
	fail.

get_number_of_jobs_goups_to_run(_,NumJobs):-
	num_jobs(NumJobs),
	retractall(num_jobs(_)),
	retractall(job_to_run(_,_,_)).


rebuild_results(ResultsVersion):-
	get_number_of_jobs_goups_to_run(ResultsVersion,NumJobs),
	rebuild_results0(NumJobs,ResultsVersion).



rebuild_results0(NumJobs,ResultsVersion):-
	atoms_concat(['data',ResultsVersion],KeepingDirResults),
	GroupNum in 1..NumJobs,
	indomain(GroupNum),
	atoms_concat([KeepingDirResults,'/jobs_',GroupNum],KeepingLocationJobsGroup),
	atoms_concat([KeepingLocationJobsGroup,'/obj_map_id_times_rksplit_',GroupNum,'.pl'],ObjMapIdTimesRk),
	retractall(obj_map_id_times_rksplit(_,_,_,_,_)),
	consult(ObjMapIdTimesRk),
	obj_map_id_times_rksplit(Obj,Bound,JobID,_,_),
	atoms_concat([KeepingLocationJobsGroup,'/job_',JobID],JobFile),
	atoms_concat(['cp ',JobFile,'.out',' ',KeepingDirResults,'/',Obj,'/',Bound,'/job_',JobID,'_',GroupNum,'.out'],BashCommand),
	process_create(path(sh),['-c', BashCommand], [wait(exit(0))]),
	fail.

rebuild_results0(_,_):-
	retractall(obj_map_id_times_rksplit(_,_,_,_,_)).


cat_final_results_obj(KeepingDirResults,ResultsVersion):-
	consult('cmds_for_maps.pl'),
	combojects(Objs),
	obj_map(_,Obj,Att,LowUp),
	member(Obj,Objs),
	atoms_concat([LowUp,'_',Att],Bound),
	atoms_concat([KeepingDirResults,'/',Obj,'/',Bound],BoundDir),
	atoms_concat([KeepingDirResults,'/',Obj,'_v',ResultsVersion,'/',Obj,'_',Bound,'.tex'],FinalDirResultObjFile),
	atoms_concat(['cat ',BoundDir,'/','*.out > ',FinalDirResultObjFile],BashCommand0),
	process_create(path(sh),['-c', BashCommand0], [wait(exit(0))]),
	atoms_concat(['cat ',BoundDir,'/','*.out > ',KeepingDirResults,'/',Obj,'/',Obj,'_',Bound,'.tex'],BashCommand1),
	process_create(path(sh),['-c', BashCommand1], [wait(exit(0))]),
	fail.

cat_final_results_obj(KeepingDirResults,ResultsVersion):-
	retractall(obj_map(_,_,_,_)),
	combojects(Objs),
	member(Obj,Objs),
	atoms_concat([KeepingDirResults,'/',Obj,'_v',ResultsVersion],FinalDirResultObj),
	atoms_concat(['cat ',KeepingDirResults,'/',Obj,'/*.tex > ',FinalDirResultObj,'/results_',Obj,'.tex'],BashCommand1),
	process_create(path(sh),['-c', BashCommand1], [wait(exit(0))]),
	atoms_concat(['cp -r ',KeepingDirResults,'/',Obj,'/conjectures_',Obj,' ',FinalDirResultObj],BashCommand2),
	process_create(path(sh),['-c', BashCommand2], [wait(exit(0))]),
	atoms_concat(['cp -r ',KeepingDirResults,'/',Obj,'/trace_',Obj,' ',FinalDirResultObj],BashCommand3),
	process_create(path(sh),['-c', BashCommand3], [wait(exit(0))]),
	fail.


cat_final_results_obj(_,_).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
     %%%%%                    RESTRUCTURATION DES CONJECTURES CALCUL CANADA
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

cp(NumJobs,ResultsVersion):-
	cp(NumJobs,ResultsVersion,'conjectures'),
	cp(NumJobs,ResultsVersion,'trace').

cp(NumJobs,ResultsVersion,ConjOrTrace):-
	(ConjOrTrace = 'trace' -> ConjOrTraceBool = trace;
 	ConjOrTraceBool = conj),
	cat(NumJobs,ResultsVersion,ConjOrTraceBool).

cat(NumJobs,ResultsVersion,conj):-
	GroupNum in 1..NumJobs,
	indomain(GroupNum),
	atoms_concat(['data',ResultsVersion,'/jobs_',GroupNum],KeepingLocationJobsGroup),
	atoms_concat([KeepingLocationJobsGroup,'/obj_map_id_times_rksplit_',GroupNum,'.pl'],ObjMapIdTimesRk),
	retractall(obj_map_id_times_rksplit(_,_,_,_,_)),
	consult(ObjMapIdTimesRk),
	obj_map_id_times_rksplit(Obj,Bound,_,Time,_),
	cat_conj(Time,Obj,Bound,ResultsVersion,conj),
	fail.

cat(_,ResultsVersion,trace):-
	consult('cmds_for_maps.pl'),
	combojects(Objs),
	obj_map(_,Obj,Att,LowUp),
	member(Obj,Objs),
	atoms_concat([LowUp,'_',Att],Bound),
	cat_conj(_,Obj,Bound,ResultsVersion,trace),
	fail.

cat(_,_,_):-
	retractall(obj_map_id_times_rksplit(_,_,_,_,_)),
	retractall(obj_map(_, _, _, _)).

cat_conj(Time,Obj,Bound,ResultsVersion,conj):-
	atoms_concat(['data',ResultsVersion,'/',Obj,'/found_conjectures_',Obj,'_',Bound],PrefixConjFile),
	atoms_concat(['data',ResultsVersion,'/',Obj,'/conjectures_',Obj,'/found_conjectures_',Obj,'_',Bound,'.pl'],ConjFile),
	open(ConjFile,write,Stream),
	write_conjecture_file_header(Stream),
	functor(Conj,conjecture,9),
	write_conj_or_missing(Stream,PrefixConjFile,Time,Conj),
	functor(MissingConj,missing,3),
	format(Stream,'~n',[]),
	write_conj_or_missing(Stream,PrefixConjFile,Time,MissingConj),
	close(Stream).

cat_conj(_,Obj,Bound,ResultsVersion,trace):-
	atoms_concat(['data',ResultsVersion,'/',Obj,'/trace_',Obj,'_',Bound,'_*.pl'],PrefixTraceFile),
	atoms_concat(['data',ResultsVersion,'/',Obj,'/trace_',Obj,'/trace_',Obj,'_',Bound,'.pl'],TraceFile),
	atoms_concat(['cat ',PrefixTraceFile,' > ',TraceFile],BashCommand),
	process_create(path(sh),['-c', BashCommand], [wait(exit(0))]).

write_conj_or_missing(Stream,PrefixConjFile,Time,FunctorConj):-
	%prolog_flag(syntax_errors,_,quiet),
	I in 1..Time,
	indomain(I),
	atoms_concat([PrefixConjFile,'_1_3_',Time,'_',I,'.pl'],DecoupeConjFile),
	retractall(FunctorConj),
	consult(DecoupeConjFile),
	call(FunctorConj),
	format(Stream,'~w.~n',[FunctorConj]),
	fail.
write_conj_or_missing(_,_,_,FunctorConj):-
	%prolog_flag(syntax_errors,_,error),
	retractall(FunctorConj).

write_conjecture_file_header(Sout) :-
    format(Sout, '% Contains all found conjectures generated by main, where each conjecture is a conjecture\\9 fact of the form:~n', []), % cmodif
    format(Sout, '%  . id(KindCombi, MapId, ConjId): conjecture identifier,~n', []),  % cmodif
    format(Sout, '%  . Kind                        : low (if lower bound); up (if upper bound); primary, secondary (if equality),~n', []),
    format(Sout, '%  . col(Table,Col)              : table and column for which the conjecture holds (left-hand side of the conjecture),~n', []),
    format(Sout, '%  . Name                        : name corresponding to col(Table,Col),~n', []),
    format(Sout, '%  . MaxN                        : size that was used for generating the conjecture,~n', []),
    format(Sout, '%  . Cost                        : cost associated with the conjecture,~n', []),
    format(Sout, '%  . Formula                     : formula associated with the conjecture (right-hand side of the conjecture),~n', []),
    format(Sout, '%  . ConjFamily                  : family to which belong the conjecture,~n', []), % cmodif
    format(Sout, '%  . Option                      : option that was used to generate the conjecture.~n', []), % cmodif
    format(Sout, '% Contains also all characteritics for which could not find any formula, see missing\\3 facts.~n~n', []), % modif
    format(Sout, ':- multifile conjecture/9.~n', []),  % cmodif
    format(Sout, ':- multifile missing/3.~n',    []),  % modif
    format(Sout, ':- dynamic conjecture/9.~n',   []),  % cmodif
    format(Sout, ':- dynamic missing/3.~n~n',    []).  % modif



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% GENERATE JOB TO DO %%%%%%%%%%%%%%%%%%%%%





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
