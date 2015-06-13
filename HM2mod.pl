:- set_prolog_flag(occurs_check,true).
:- op(500,yfx,$).

use_module(library(apply)). % for maplist
use_module(librar(gensym)). % for gensym

kind(KC,var(Z),K1) :- first(Z:K,KC), instantiate(K,K1).
kind(KC,F $ G, K2) :- kind(KC,F,K1 -> K2), kind(KC,G,K1).
kind(KC,A -> B,o)  :- kind(KC,A,o), kind(KC,B,o).

type(KC,C,var(X),     T1) :- first(X:T,C), instantiate(T,T1).
type(KC,C,lam(X,E), A->B) :- type(KC,[X:mono(A)|C],E,B),
                             kind(KC,A->B,o).
type(KC,C,X $ Y,       B) :- type(KC,C,X,A->B),
                             type(KC,C,Y,A,  ).
type(KC,C,let(X=E0,E1),T) :- type(KC,C,              E0,A),
                             type(KC,[X:poly(C,A)|C],E1,T).

instantiate(poly(C,T),T1) :- copy_term(t(C,T),t(C,T1)).
instantiate(mono(T),  T).

first(K:V,[K1:V1|Xs]) :- K=K1 -> V=V1 ; first(K:V,Xs).

variablize(var(X)) :- gensym(t,X).


