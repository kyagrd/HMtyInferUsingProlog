%%%% Hindley Milner + type constructor polymorphism + rank-1 kind poly

:- set_prolog_flag(occurs_check,true).
:- op(500,yfx,$).

kind(KC,var(Z),K1) :- first(Z:K,KC), instantiate(K,K1).
kind(KC,F $ G, K2) :- kind(KC,F,K1 -> K2), kind(KC,G,K1).
kind(KC,A -> B,o)  :- kind(KC,A,o), kind(KC,B,o).

type(KC,C,var(X),     T1) --> { first(X:T,C) }, inst_type(KC,T,T1).
type(KC,C,lam(X,E), A->B) --> type(KC,[X:mono(A)|C],E,B), [kind(KC,A->B,o)].
type(KC,C,X $ Y,       B) --> type(KC,C,X,A->B), type(KC,C,Y,A).
type(KC,C,let(X=E0,E1),T) --> type(KC,C,E0,A), type(KC,[X:poly(C,A)|C],E1,T).

first(X:T,[X1:T1|Zs]) :- X = X1, T = T1.
first(X:T,[X1:T1|Zs]) :- X\==X1, first(X:T, Zs).

instantiate(mono(T),T).
instantiate(poly(C,T),T1) :- copy_term(t(C,T),t(C,T1)).

inst_type(KC,poly(C,T),T2) -->
  { copy_term(t(C,T),t(C,T1)), 
    free_variables(T,Xs), free_variables(T1,Xs1) }, % Xs and Xs1 are same length
  samekinds(KC,Xs,Xs1), { T1=T2 }. %% unify T1 T2 later (T2 might not be var)
inst_type(KC,mono(T),T) --> [].

samekinds(KC,[X|Xs],[Y|Ys]) --> { X\==Y }, [kind(KC,X,K),kind(KC,Y,K)],
                                samekinds(KC,Xs,Ys).
samekinds(KC,[X|Xs],[X|Ys]) --> [], samekinds(KC,Xs,Ys).
samekinds(KC,[],[]) --> [].

variablize(var(X)) :- gensym(t,X).

infer_type(KC,C,E,T) :-
  phrase( type(KC,C,E,T), Gs0 ), %%% handle delayed kind sanity check below
  copy_term(Gs0,Gs), % Gs0 = Gs, % 
  bagof(Ty, member(kind(_,Ty,_),Gs), Tys),
  free_variables(Tys,Xs), maplist(variablize,Xs), % replace free tyvar to var(t)
  maplist(call,Gs). % run all goals in Gs1

appendKC([],_,[]).
appendKC([kind(KC,X,K)|Gs],KC1,[kind(KC2,X,K)|Gs1]) :-
  append(KC1,KC,KC2), appendKC(Gs,KC1,Gs1).




ctx0([ 'Nat':mono(o)
     , 'List':mono(o->o)
     | _
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
