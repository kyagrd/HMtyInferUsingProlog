% vim: syntax=prolog: sw=2: ts=2: expandtab: ai:
:- set_prolog_flag(occurs_check,true).
:- op(500,yfx,$).

type(C,var(X),       T) :- first(X:T,C).
type(C,lam(X,E),A -> B) :- type([X:A|C], E,  B).
type(C,X $ Y,        B) :- type(C,X,A -> B), type(C,Y,A).

first(K:V,[K1:V1|Xs]) :- K=K1, V=V1.
first(K:V,[K1:V1|Xs]) :- K\==K1, first(K:V, Xs). % no cut but using var cmp
