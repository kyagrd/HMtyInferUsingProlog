%%%% Hindley Milner + type constructor polymorphism + rank-1 kind poly

:- set_prolog_flag(occurs_check,true).
:- op(500,yfx,$).

kind(KC,var(Z),K1) :- first(Z:K,KC), instantiate(K,K1).
kind(KC,F $ G, K2) :- kind(KC,F,K1 -> K2), kind(KC,G,K1).
kind(KC,A -> B,o)  :- kind(KC,A,o), kind(KC,B,o).

type(KC,C,var(X),     T1,G,G1) :- first(X:T,C), inst_type(KC,T,T1,G,G1).
type(KC,C,lam(X,E), A->B,G,G1) :- type(KC,[X:mono(A)|C],E,B,G0,G1),
                                  G0 = [kind(KC,A->B,o) | G]. % delay kind goal
type(KC,C,X $ Y,       B,G,G1) :- type(KC,C,X,A->B,G, G0),
                                  type(KC,C,Y,A,  G0,G1).
type(KC,C,let(X=E0,E1),T,G,G1) :- type(KC,C,E0,A,G, G0),
                                  type(KC,[X:poly(C,A)|C],E1,T,G0,G1).

first(X:T,[X1:T1|Zs]) :- X = X1 -> T = T1 ; first(X:T, Zs).

instantiate(poly(C,T),T1) :- copy_term(t(C,T),t(C,T1)).
instantiate(mono(T),T).

inst_type(KC,poly(C,T),T2,G,G1) :- copy_term(t(C,T),t(C,T1)), 
  free_variables(T,Xs), free_variables(T1,Xs1), % Xs and Xs1 are same length
  samekinds(KC,Xs,Xs1,G,G1), T1=T2. %% unify T1 T2 later (T2 might not be var)
inst_type(KC,mono(T),T,G,G).

samekinds(KC,[X|Xs],[Y|Ys],Gs,Gs1) :- %  helper predicate for inst_type
  (X\==Y -> Gs0=[kind(KC,X,K),kind(KC,Y,K)|Gs]; Gs0=Gs),
  samekinds(KC,Xs,Ys,Gs0,Gs1).
samekinds(KC,[],[],Gs,Gs).

variablize(var(X)) :- gensym(t,X).

infer_type(KC,C,E,T) :-
  type(KC,C,E,T,[],Gs0), %%% handle delayed kind sanity check below
  copy_term(Gs0,Gs),
  bagof(Ty, member(kind(_,Ty,_),Gs), Tys),
  free_variables(Tys,Xs), maplist(variablize,Xs), % replace free tyvar to var(t)
  bagof(A:K,member(var(A),Xs),KC1),
  appendKC(Gs,KC1,Gs1), % extend with KC1 for new vars
  maplist(call,Gs1). % run all goals in Gs1

appendKC([],_,[]).
appendKC([kind(KC,X,K)|Gs],KC1,[kind(KC2,X,K)|Gs1]) :-
  append(KC1,KC,KC2), appendKC(Gs,KC1,Gs1).




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

main(T) :- ctx0(KC,C),
  X = var(x), Y = var(y), Z = var(z),
  Zero = var('Zero'), Succ = var('Succ'),
  Cons = var('Cons'), Nil = var('Nil'),
  TM_id = lam(x,X),
  TM_S = lam(x,lam(y,lam(z,(X$Z)$(Y$Z)))),
  TM_bad = lam(x,X$X),
  TM_e1 = let(id=TM_id,var(id)$var(id)),
  TM_e2 = lam(y,let(x=lam(z,Y),X$X)),
  infer_type(KC,C,TM_e2,T).

%%%% TODO test some poly kinded type consturctors
