% vim: syntax=prolog: sw=2: ts=2: expandtab: ai:
:- use_module(library(dcg/basics)).
%5 :- use_module(library(pio)).
:- set_prolog_flag(occurs_check,true).
:- op(500,yfx,$).

tokenize(Ts) --> tok(Ts), blanks.
tok(["(" |Ts]) --> blanks, `(` , tok(Ts).
tok([")" |Ts]) --> blanks, `)` , tok(Ts).
tok(["\\"|Ts]) --> blanks, `\\`, tok(Ts).
tok(["." |Ts]) --> blanks, `.` , tok(Ts).
tok([X   |Ts]) --> blanks, identifier(X), tok(Ts).
tok([]) --> blanks.

identifier(X) --> [C|Cs],
                  { code_type(C,prolog_atom_start)
                  , codelist_type(Cs,prolog_identifier_continue)
                  , atom_codes(X,[C|Cs]) }.

codelist_type([],     T).
codelist_type([C|Cs], T) :- code_type(C,prolog_identifier_continue),
                            codelist_type(Cs,T).

tm_var(X) --> [X], {atom(X)}. 

tm1(X) --> ["("], tm(X), [")"].
tm1(var(V))   --> tm_var(V).

tm(lam(X,E)) --> ["\\"], tm_var(X), ["."], tm(E).
tm(E)        --> many1_tm1([T|Ts]), { foldl_ap(T,Ts,E) }.

many1_tm1([T|Ts]) --> tm1(T), many1_tm1(Ts). 
many1_tm1([]) --> [].

foldl_ap(E, []     , E).
foldl_ap(E0,[E1|Es], E) :- foldl_ap(E0$E1, Es, E).



type(C,var(X),       T) :- first(X:T,C).
type(C,lam(X,E),A -> B) :- type([X:A|C], E,  B).
type(C,X $ Y,        B) :- type(C,X,A -> B), type(C,Y,A).

first(K:V,[K1:V1|Xs]) :- K = K1, V=V1.
first(K:V,[K1:V1|Xs]) :- K\==K1, first(K:V, Xs).



type_of_program(Cs, Ty) :-
  phrase(tokenize(Ts), Cs), phrase(tm(E), Ts), type([],E,Ty).

%% :- forward expr/3.
%% :- forward term/3.
%% :- forward factor/3.

%% 
%% expr(C) --> term(A), [+], expr(B), {C is A+B}.
%% expr(C) --> term(A), [-], expr(B), {C is A-B}.
%% expr(A) --> term(A).
%% 
%% term(C) --> factor(A), [*], term(B), {C is A*B}.
%% term(C) --> factor(A), [/], term(B), {C is A/B}.
%% term(A) --> factor(A).
%% 
%% factor(A) --> [A], {integer(A)}.
%% factor(C) --> ['('], expr(C), [')'].

