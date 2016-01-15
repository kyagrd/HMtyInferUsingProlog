:- set_prolog_flag(occurs_check,true).
:- op(500,yfx,$).

kind(KC,var(X),   K1) :- first(X:K,KC), instantiate(K,K1).
kind(KC,F $ G,    K2) :- K2\==row, kind(KC,F,K1->K2), K1\==row, kind(KC,G,K1).
kind(KC,A -> B,    o) :- kind(KC,A,o), kind(KC,B,o).
kind(KC,{R},       o) :- kind(KC,R,row).
kind(KC,[],      row).
kind(KC,[X:T|R], row) :- kind(KC,T,o), kind(KC,R,row).

type(KC,C,var(X),    T1) --> { first(X:T,C) }, inst_type(KC,T,T1).
type(KC,C,lam(X,E),A->B) --> type(KC,[X:mono(A)|C],E,B), [kind(KC,A->B,o)].
type(KC,C,X $ Y,      B) --> type(KC,C,X,A->B), type(KC,C,Y,A).
type(KC,C,let(X=E0,E),T) --> type(KC,C,E0,A), type(KC,[X:poly(C,A)|C],E,T).
type(KC,C,{[]},     {R}) --> [kind(KC,R,row)].
type(KC,C,{[X=E|L]},{R}) --> type(KC,C,E,T), { first(X:T,R) }, type(KC,C,{L},{R}).
type(KC,C,sel(L,X),    T) --> { first(X:T,R) }, type(KC,C,L,{R}).

first(K:V,[K1:V1|Xs]) :- K = K1, V=V1.
first(K:V,[K1:V1|Xs]) :- K\==K1, first(K:V, Xs).

instantiate(mono(T),T).
instantiate(poly(C,T),T1) :- copy_term(t(C,T),t(C,T1)).

inst_type(KC,mono(T),T) --> [].
inst_type(KC,poly(C,T),T2) -->
  { copy_term(t(C,T),t(C,T1)), 
    free_variables(T,Xs), free_variables(T1,Xs1) }, % Xs and Xs1 are same length
  samekinds(KC,Xs,Xs1), { T1=T2 }. %% unify T1 T2 later (T2 might not be var)

samekinds(KC,[X|Xs],[Y|Ys]) --> { X\==Y }, [kind(KC,X,K),kind(KC,Y,K)],
                                samekinds(KC,Xs,Ys).
samekinds(KC,[X|Xs],[X|Ys]) --> [], samekinds(KC,Xs,Ys).
samekinds(KC,[],[]) --> [].

variablize(var(X)) :- gensym(t,X).

appendKC([],_,[]).
appendKC([kind(KC,X,K)|Gs],KC1,[kind(KC2,X,K)|Gs1]) :-
  append(KC1,KC,KC2), appendKC(Gs,KC1,Gs1).

infer_type(KC,C,E,T) :-
  phrase( type(KC,C,E,T), Gs0 ), %%% handle delayed kind sanity check below
  % maplist(printnl,Gs0), nl, nl,
  copy_term(Gs0,Gs), % Gs0 = Gs, % 
  % maplist(printnl,Gs), nl, nl,
  bagof(Ty,member(kind(_,Ty,_),Gs),Tys),
  % maplist(printnl,Tys), nl, nl,
  free_variables(Tys,Xs),
  % maplist(printnl,Xs), nl, nl,
  maplist(variablize,Xs), % replace free tyvar to var(t)
  maplist(call,Gs). % run all goals in Gs1


printnl(X) :- print(X), nl.


ctx0([ 'Nat':mono(o)
     , 'List':mono(o->o)
     , 'Pair':mono(o->o->o)
     | _
     ],
     [ 'Zero':mono(Nat)
     , 'Succ':mono(Nat -> Nat)
     , 'Nil' :poly([], List$A)
     , 'Cons':poly([], A->((List$A)->(List$A)))
     , 'Pair':poly([], A0->B0->Pair$A0$B0)
     ])
  :- Nat = var('Nat'), List = var('List'), Pair=var('Pair').

main(T) :- ctx0(KC,C),
  X = var(x), Y = var(y), Z = var(z),
  Zero = var('Zero'), Succ = var('Succ'),
  Cons = var('Cons'), Nil = var('Nil'),
  Pair = var('Pair'),
  TM_id = lam(x,X),
  TM_S = lam(x,lam(y,lam(z,(X$Z)$(Y$Z)))),
  TM_bad = lam(x,X$X),
  TM_e1 = let(id=TM_id,var(id)$var(id)),
  TM_e2 = lam(y,let(x=lam(z,Y),X$X)),
  TM_e3 = {[z=lam(x,var(x))]},
  TM_e4 = lam(r,sel(var(r),x)),
  TM_e5 = lam(r,Pair$sel(var(r),y)$sel(var(r),x)),
  TM_e6 = {[x=lam(x,var(x)),y=lam(x,var(x))]},
  TM_e7 = TM_e5 $ TM_e6,
  TM_e8 = lam(r,Pair$sel(var(r),y)$var(r))${[x=lam(x,var(x))]},
  infer_type(KC,C,TM_e5,T).


