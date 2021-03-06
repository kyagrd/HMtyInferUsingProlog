:- set_prolog_flag(occurs_check,true).
:- op(500,yfx,$).

type(C,var(X),       T1) :- first(X:T,C), instantiate(T,T1).
type(C,lam(X,E), A -> B) :- type([X:mono(A)|C],E,B).
type(C,X $ Y,        B ) :- type(C,X,A -> B), type(C,Y,A).
type(C,let(X=E0,E1), T ) :- type(C,E0,A), type([X:poly(C,A)|C],E1,T).

first(K:V,[K1:V1|Xs]) :- K = K1, V=V1.
first(K:V,[K1:V1|Xs]) :- K\==K1, first(K:V, Xs).

instantiate(poly(C,T),T1) :- copy_term(t(C,T),t(C,T1)).
instantiate(mono(T),T).

main(T) :-
  X = var(x), Y = var(y), Z = var(z),
  TM_id = lam(x,X),
  TM_S = lam(x,lam(y,lam(z,(X$Z)$(Y$Z)))),
  TM_bad = lam(x,X$X),
  TM_e1 = let(id=TM_id,var(id)$var(id)),
  TM_e2 = lam(y,let(x=lam(z,Y),X$X)),
  type([],TM_e2, T).

