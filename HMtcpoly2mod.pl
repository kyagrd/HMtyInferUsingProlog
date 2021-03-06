%%%% Hindley Milner + type constructor polymorphism + rank-1 kind poly

:- set_prolog_flag(occurs_check,true).
:- op(500,yfx,$).

kind(KC,var(Z),K1) :- first(Z:K,KC), instantiate(K,K1).
kind(KC,F $ G, K2) :- kind(KC,F,K1 -> K2), kind(KC,G,K1).
kind(KC,A -> B,o)  :- kind(KC,A,o), kind(KC,B,o).

type(KC,C,var(X),     T1) :- first(X:T,C), inst_type(KC,T,T1).
type(KC,C,lam(X,E), A->B) :- type(KC,[X:mono(A)|C],E,B),
                             kind(KC,A->B,o).
type(KC,C,X $ Y,       B) :- type(KC,C,X,A->B),
                             type(KC,C,Y,A).
type(KC,C,let(X=E0,E1),T) :- type(KC,C,E0,A),
                             type(KC,[X:poly(C,A)|C],E1,T).

first(K:V,[K1:V1|Xs]) :- K = K1, V=V1.
first(K:V,[K1:V1|Xs]) :- K\==K1, first(K:V, Xs).

instantiate(poly(C,T),T1) :- copy_term(t(C,T),t(C,T1)).
instantiate(mono(T),T).

inst_type(KC,poly(C,T),T2) :- copy_term(t(C,T),t(C,T1)), 
  free_variables(T,Xs), free_variables(T1,Xs1), % Xs and Xs1 are same length
  samekinds(KC,Xs,Xs1), T1=T2. %% unify T1 T2 later (T2 might not be var)
inst_type(KC,mono(T),T).

samekinds(KC,[X|Xs],[Y|Ys]) :- %  helper predicate for inst_type
  (X\==Y -> (kind(KC,X,K),kind(KC,Y,K))),
  samekinds(KC,Xs,Ys).
samekinds(KC,[],[]).

variablize(var(X)) :- gensym(t,X).


ctx0([ 'Nat':mono(o)
     , 'List':mono(o->o)
     ],
     [ 'Zero':mono(Nat)
     , 'Succ':mono(Nat -> Nat)
     , 'Nil' :poly([] %% ['Z':mono(Nat), 'S':mono(Nat -> Nat)]
                  ,List$A)
     , 'Cons':poly([] %%['Z':mono(Nat), 'S':mono(Nat -> Nat)]
                  ,A->((List$A)->(List$A)))
     ])
  :- Nat = var('Nat'), List = var('List').

main(T) :- ctx0(KC,C), append(KC,KC0,KC1),
  X = var(x), Y = var(y), Z = var(z),
  Zero = var('Zero'), Succ = var('Succ'),
  Cons = var('Cons'), Nil = var('Nil'),
  TM_id = lam(x,X),
  TM_S = lam(x,lam(y,lam(z,(X$Z)$(Y$Z)))),
  TM_bad = lam(x,X$X),
  TM_e1 = let(id=TM_id,var(id)$var(id)),
  TM_e2 = lam(y,let(x=lam(z,Y),X$X)),
  type(KC,C1,TM_e2,T), monoKC(KC0).

monoKC([]).
monoKC([_:mono(_)|KC]) :- monoKC(KC).

%%%% TODO test some poly kinded type consturctors
