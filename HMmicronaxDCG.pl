% vim: sw=2: ts=2: expandtab:
%%%% Hindley Milner + type constructor polymorphism + rank-1 kind poly
%%%% with single depth non-nested pattern matches
%%%% Mendler-style iteration over possibly non-regular ADTs but no GADTs

:- set_prolog_flag(occurs_check,true).
:- op(500,yfx,$).

kind(KC,var(Z),K1) :- first(Z:K,KC), instantiate(K,K1).
kind(KC,F $ G, K2) :- kind(KC,F,K1 -> K2), kind(KC,G,K1).
kind(KC,A -> B,o)  :- kind(KC,A,o), kind(KC,B,o).
kind(KC,mu(F), K)  :- kind(KC,F,K->K).

type(KC,C,var(X),     T1) --> { first(X:T,C) }, inst_type(KC,T,T1).
type(KC,C,lam(X,E), A->B) --> type(KC,[X:mono(A)|C],E,B), [kind(KC,A->B,o)].
type(KC,C,X $ Y,       B) --> type(KC,C,X,A->B), type(KC,C,Y,A).
type(KC,C,let(X=E0,E1),T) --> type(KC,C,E0,A), type(KC,[X:poly(C,A)|C],E1,T).
type(KC,C,in(N,E),     T) --> type(KC,C,E,T0),
                              { unfold_N_ap(1+N,T0,F,[mu(F)|Is]),
                                foldl_ap(mu(F),Is,T) }.
%%%%% Alts is a pattern lambda. (Alts $ E) is "case E of Alts" in Haskell
type(KC,C,     Alts,A->T) --> type_alts(KC,C,Alts,A->T), [kind(KC,A->T,o)].

type(KC,C,mit(X,Alts),mu(F)->T) -->
  { is_list(Alts), gensym(r,R),
    KC1 = [R:mono(o)|KC], C1 = [X:poly(C,var(R)->T)|C] },
  type_alts(KC1,C1,Alts,F$var(R)->T).

type(KC,C,mit(X,Is-->T0,Alts),A->T) -->
  { is_list(Alts), gensym(r,R),
    foldl_ap(mu(F),Is,A), foldl_ap(var(R),Is,RIs),
    KC1 = [R:mono(K)|KC], C1 = [X:poly(C,RIs->T0)|C] },
  [kind(KC,F,K->K), kind(KC,A->T,o)], % delayed goals
  { foldl_ap(F,[var(R)|Is],FRIs) },
  type_alts(KC1,C1,Alts,FRIs->T).


type_alts(KC,C,[Alt],          A->T) --> type_alt(KC,C,Alt,A->T).
type_alts(KC,C,[Alt,Alt2|Alts],A->T) --> type_alt(KC,C,Alt,A->T),
                                         type_alts(KC,C,[Alt2|Alts],A->T).

type_alt(KC,C,P->E,A->T) --> % assume single depth pattern (C x0 .. xn)
  { P =.. [Ctor|Xs], upper_atom(Ctor),
    findall(var(X),member(X,Xs),Vs),
    foldl_ap(var(Ctor),Vs,PE),% PE=var('Cons')$var(x)$var(xs) when E='Cons'(x,xs)
    findall(X:mono(Tx),member(X,Xs),C1,C) }, % C1 extends C with bindings for Xs
  type(KC,C1,PE,A), type(KC,C1,E,T).

% assume upper atoms are tycon or con names and lower ones are var names
upper_atom(A) :- atom(A), atom_chars(A,[C|_]), char_type(C,upper).
lower_atom(A) :- atom(A), atom_chars(A,[C|_]), char_type(C,lower).

unfold_N_ap(0,E,    E,[]).
unfold_N_ap(N,E0$E1,E,Es) :-
  N>0, M is N-1, unfold_N_ap(M,E0,E,Es0), append(Es0,[E1],Es).

foldl_ap(E, []     , E).
foldl_ap(E0,[E1|Es], E) :- foldl_ap(E0$E1, Es, E).

first(X:T,[X1:T1|Zs]) :- X = X1, T = T1.
first(X:T,[X1:T1|Zs]) :- X\==X1, first(X:T, Zs).

instantiate(poly(C,T),T1) :- copy_term(t(C,T),t(C,T1)).
instantiate(mono(T),T).

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
  copy_term(Gs0,Gs),
  bagof(Ty, member(kind(_,Ty,_),Gs), Tys),
  free_variables(Tys,Xs), maplist(variablize,Xs), % replace free tyvar to var(t)
  bagof(A:K,member(var(A),Xs),KC1),
  appendKC(Gs,KC1,Gs1), % extend with KC1 for new vars
  maplist(call,Gs1). % run all goals in Gs1

appendKC([],_,[]).
appendKC([kind(KC,X,K)|Gs],KC1,[kind(KC2,X,K)|Gs1]) :-
  append(KC1,KC,KC2), appendKC(Gs,KC1,Gs1).

% data B r a = BN | BC a (r(r a))
% B : (* -> *) -> (* -> *)
% BN: B r a
% BC: a -> r(r a) -> B r a

ctx0([ 'N':mono(o->o)
     , 'L':mono(o->o->o)
     , 'B':mono((o->o)->(o->o))
     ],
     [ 'Z':poly([] , N$R1)
     , 'S':poly([] , R1 -> N$R1)
     , 'N':poly([] , L$A2$R2)
     , 'C':poly([] , A2->(R2->(L$A2$R2)))
     , 'BN':poly([] , B$R3$A3)
     , 'BC':poly([] , A3 -> R3$(R3$A3) -> B$R3$A3)
     , 'plus':poly([], mu(N) -> mu(N) -> mu(N))
     %% , 'undefined':poly([], X1231245424)
     ])
  :- N = var('N'), L = var('L'), B = var('B').

main(T) :- ctx0(KCtx,Ctx),
  X = var(x), Y = var(y), W = var(w),
  Z = var('Z'), S = var('S'),
  Zero=in(0,Z), Succ=lam(x,in(0,S$X)),
  N = var('N'), C = var('C'),
  Nil=in(0,N), Cons=lam(x,lam(xs,in(0,C$X$var(xs)))),
  BN = var('BN'), BC = var('BC'),
  BNil=in(1,BN), BCons=lam(x,lam(xs,in(1,BC$X$var(xs)))),
  TM_id = lam(x,X),
  TM_S = lam(x,lam(y,lam(w,(X$W)$(Y$W)))),
  TM_bad = lam(x,X$X),
  TM_e1 = let(id=TM_id,var(id)$var(id)),
  TM_e2 = lam(y,let(x=lam(w,Y),X$X)),
  TM_e3a = (C$Zero$Nil),
  TM_e3f = ['N'->Zero,'C'(x,xs)->X], %% $ (C$Zero$Nil),
  TM_e3 = ['N'->Zero,'C'(x,xs)->X] $ (C$Zero$Nil),
  TM_lendumb0 = mit(len,['N'->Zero]),
  TM_lendumb = mit(len,['N'->Zero,'C'(x,xs)->Zero]),
  TM_len = mit(len,['N'->Zero,'C'(x,xs)->Succ$(var(len)$var(xs))]),
  TM_e4 = let(length=TM_len, Cons$ (var(length)$(Cons$Zero$Nil))
                                 $ (Cons$ (var(length)$(Cons$Nil$Nil)) $ Nil) ),
  TM_e5 = mit(bsum, [I]-->((I->mu(N))->mu(N)),
             [ 'BN'       -> lam(f,Zero)
             , 'BC'(x,xs) -> lam(f,
                   var(plus) $ (var(f)$X)
                             $ (var(bsum) $ var(xs)
                                          $ lam(ys,var(bsum)$var(ys)$var(f)) )
                                )
             ]),
  infer_type(KCtx,Ctx,TM_e5,T).

% tested on SWI-Prolog version 7.2.0

%%%% TODO test some poly kinded type consturctors

