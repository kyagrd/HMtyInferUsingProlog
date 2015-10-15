% vim: syntax=prolog: sw=2: ts=2: expandtab: ai:

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Demonstrating an idea of what TIPER would be doining using Prolog:
% both parsing and type checking/inference based on LP specifications
%
% Prolog has been used in parsing epecially in the NLP community, so
% parsing itself is nothing new. Just proof of concept. But it is a
% wonder why Parsec style library has not been widely used ....
% (maybe I didn't Google with the right keywords???)
%
% -- Ki Yung  Ahn
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- use_module(library(dcg/basics)).
% :- use_module(library(pio)).
:- set_prolog_flag(occurs_check,true).
:- op(500,yfx,$).



%%%% Tokenizer (Lexer)
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


%%%% Parsec style Parser implementation for STLC
tm(lam(X,E)) --> ["\\"], tm_var(X), ["."], tm(E).
tm(E)        --> many_tm1([T|Ts]), { foldl_ap(T,Ts,E) }.

tm1(X)      --> ["("], tm(X), [")"].
tm1(var(V)) --> tm_var(V).

tm_var(X) --> [X], {atom(X)}. 

many_tm1([T|Ts]) --> tm1(T), many_tm1(Ts). 
many_tm1([])     --> [].

foldl_ap(E, []     , E).
foldl_ap(E0,[E1|Es], E) :- foldl_ap(E0$E1, Es, E).


%%%% STLC type system spec as in my FLOPS submission
type(C,var(X),       T) :- first(X:T,C).
type(C,lam(X,E),A -> B) :- type([X:A|C], E,  B).
type(C,X $ Y,        B) :- type(C,X,A -> B), type(C,Y,A).

first(K:V,[K1:V1|Xs]) :- K = K1, V=V1.
first(K:V,[K1:V1|Xs]) :- K\==K1, first(K:V, Xs).


%%%% putting it all together
type_of_program(Cs, Ty) :-
  phrase(tokenize(Ts), Cs), phrase(tm(E), Ts), type([],E,Ty).


% Usage:
% 
% ?- type_of_program(`(\\y.y)`, T).      
% T = (_G1806->_G1806) .
%
% ?- type_of_program(`(\\x.\\y.y x)`, T).        
% T = (_G1889-> (_G1889->_G1899)->_G1899) .
%
% ?- type_of_program(`(\\x.\\y.y x) (\\y.y)`, T).
% T = (((_G1928->_G1928)->_G1908)->_G1908) .
%


%%%
%%% With the pio library in SWI-Prolog, we can parse from file as well
%%% http://www.swi-prolog.org/pldoc/man?section=summary-lib-pio
%%% which would be useful for providing a early proof-of-concept of TIPER
%%%

%%% TODO
%%% error messages in both parser and type checking/inference
%%% just having false as result is not very helpful
%%%
