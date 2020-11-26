#!/usr/bin/env swipl

:- use_module(library(clpfd)).
:- use_module(library(achelois)).

:- initialization(main, main).

root(Root) :-
    source_file(File),
    atom_concat(_, 't', File),
    file_directory_name(File, Root).

main(_) :-
    % Proof = loc_type(_, _, [x:empty-bool], source, with(empty), v(x), any-bool, _),
    % Loc = filter(list(any-(list-(any-bool)),
    %     list(any-bool, v(x), emptylist(any-bool)),
    %     list(any-(list-(any-bool)),
    %         list(any-bool, v(y), list(any-bool, v(x), emptylist(any-bool))),
    %         emptylist(any-(list-(any-bool))))), one),
    Loc = filter(v(x), one),
    Gamma = [x:any-bool, y:any-bool],
    Mu = [x-loc(0,loc(0)),y-loc(1,loc(1))],
    Rho = [0-resource(bool,false), 1-resource(bool,true)],
    run_locator(Gamma, Mu, Rho, Loc).
    % Proof = loc_type(_, _, [x:any-bool], source, with(empty), Loc, _, _),
    % EvalProof = loc_eval(_, _, ([x-loc(0,loc(0))],[0-resource(bool,false)],Loc), _),
    % eval_step(EvalProof),
    % well_typed(Proof) ->
    %     write_proof(Proof),
    %     write_proof(EvalProof).

    % writeln('\\text{\\textcolor{red}{FAILED!}}').

no_vars([]).
no_vars([loc(_,_) : _|Delta]) :- no_vars(Delta).

proof_compat([], Delta) :- no_vars(Delta).
proof_compat([X:T|Gamma], Delta) :-
    select(X:T, Delta, Rest),
    proof_compat(Gamma, Rest).

run_locator(_Gamma, _Mu, _Rho, Loc) :-
    located(Loc),
    writeln('$\\square$').

% TODO: Can we avoid cuts?
run_locator(Gamma, Mu, Rho, Loc) :-
    not(located(Loc)),
    TyPrf = loc_type(_, _, Gamma, source, with(empty), Loc, Tau, Delta),
    % writeln(TyPrf),
    well_typed(TyPrf), !,
    writeln('\\paragraph{Typecheck}'),
    write_proof(TyPrf),

    EvalPrf = loc_eval(_, _, (Mu,Rho,Loc), (NewMu,NewRho,NewLoc)),
    eval_step(EvalPrf), !,
    writeln('\\paragraph{Evaluation Step}'),
    write_proof(EvalPrf),

    update_env(EvalPrf, Gamma, NewGamma),
    ProgressTyPrf = loc_type(_, _, NewGamma, source, with(empty), NewLoc, Tau, NewDelta),
    well_typed(ProgressTyPrf), !,
    writeln('\\paragraph{Progress Typecheck}'),
    write_proof(ProgressTyPrf),

    format_env(Gamma, GammaStr),
    format_env(NewGamma, NewGammaStr),
    format_env(Delta, DeltaStr),
    format_env(NewDelta, NewDeltaStr),
    format('$\\Gamma = ~w, \\qquad \\Delta = ~w$\\\\~n', [GammaStr, DeltaStr]),
    format('$\\Gamma'' = ~w, \\qquad \\Delta'' = ~w$\\\\~n', [NewGammaStr, NewDeltaStr]),

    !,

    proof_compat(Delta, NewDelta),

    run_locator(NewGamma, NewMu, NewRho, NewLoc).

write_proof(Prf) :-
    format_proof(Prf, Out),
    writeln('\\begin{mathpar}'),
    writeln(Out),
    writeln('\\end{mathpar}').

format_proof(loc_type(Prems, Rule, Gamma, M, F, Loc, T, Delta), Formatted) :-
    maplist(format_proof, Prems, PremProofs),
    atomic_list_concat(PremProofs, '\\\\', FormatPrems),
    format_mode(M, MStr),
    format_env(Gamma, GammaStr),
    format_env(Delta, DeltaStr),
    format_type(T, TStr),
    format_loc(Loc, LocStr),
    format_func(F, FStr),
    format(atom(Formatted),
           '\\inferrule*[right=~w]{ ~w }{~w \\flowproves_{~w} ~w ; ~w : ~w \\flowprovesout ~w}',
           [Rule, FormatPrems, GammaStr, MStr, FStr, LocStr, TStr, DeltaStr]).
format_proof(loc_eval(Prems, Rule, (Mu,Rho,Loc), (NewMu,NewRho,NewLoc)), Formatted) :-
    maplist(format_proof, Prems, PremProofs),
    atomic_list_concat(PremProofs, '\\\\', FormatPrems),
    format_loc(Loc, LocStr),
    format_loc(NewLoc, NewLocStr),
    format_var_env(Mu, MuStr),
    format_storage(Rho, RhoStr),
    format_var_env(NewMu, NewMuStr),
    format_storage(NewRho, NewRhoStr),
    format(atom(Formatted),
           '\\inferrule*[right=~w]{ ~w }{\\angles{ (~w, ~w), ~w } \\to \\angles{ (~w, ~w), ~w } }',
           [Rule, FormatPrems, MuStr, RhoStr, LocStr, NewMuStr, NewRhoStr, NewLocStr]).

format_var_env(Mu, Out) :-
    maplist(format_var_env_entry, Mu, EntryStrs),
    atomic_list_concat(EntryStrs, ',', EntryStr),
    format(atom(Out), '\\{ ~w \\}', [EntryStr]).
format_var_env_entry(X - L, Out) :-
    format_var(X, XStr),
    format_loc(L, LStr),
    format(atom(Out), '~w \\mapsto ~w', [XStr, LStr]).

format_storage(Rho, Out) :-
    maplist(format_storage_entry, Rho, EntryStrs),
    atomic_list_concat(EntryStrs, ',', EntryStr),
    format(atom(Out), '\\{ ~w \\}', [EntryStr]).
format_storage_entry(X-resource(T,V), Out) :-
    format_base_type(T, TStr),
    format_val(V, VStr),
    format(atom(Out), '~w \\mapsto (~w, ~w)', [X, TStr, VStr]).

format_val(N, Out) :- integer(N), format(atom(Out), '~w', [N]).
format_val(true, '\\true').
format_val(false, '\\false').
format_val([], '[]').
format_val([H|T], Out) :-
    maplist(format_loc, [H|T], LocsStrs),
    atomic_list_concat(LocsStrs, ',', LocsStr),
    format(atom(Out), '[ ~w ]', [LocsStr]).

gather_list(emptylist(T), flat_list(T, [])).
gather_list(list(T, Head, Tail), flat_list(T, [Head|Rest])) :-
    gather_list(Tail, flat_list(T, Rest)).

format_loc(nat(N), Out) :- format(atom(Out), '~w', [N]).
format_loc(bool(true), '\\true').
format_loc(bool(false), '\\false').
format_loc(v(X), X).
format_loc(emptylist(ElemT), Out) :-
    format_type(ElemT, TStr),
    format(atom(Out), '[ ~w ; ]', [TStr]).
format_loc(list(ElemT, Head, Tail), Out) :-
    gather_list(list(ElemT, Head, Tail), flat_list(ElemT, Elems)),
    maplist(format_loc, Elems, ElemsStrs),
    atomic_list_concat(ElemsStrs, ',', ElemsStr),
    format_type(ElemT, TStr),
    format(atom(Out), '[ ~w ; ~w ]', [TStr, ElemsStr]).
format_loc(filter(Loc, Q), Out) :-
    format_loc(Loc, LocStr),
    format_quant(Q, QStr),
    format(atom(Out), '~w[ ~w \\tsuchthat ]', [LocStr, QStr]).
format_loc(loc(L, loc(K)), Out) :- format(atom(Out), '(~w,~w)', [L, K]).
format_loc(loc(L, amount(N)), Out) :- format(atom(Out), '(~w, \\amount(~w))', [L, N]).

format_mode(X, 'M') :- var(X).
format_mode(source, 'S').
format_mode(dest, 'D').

format_base_type(nat, '\\natt').
format_base_type(bool, '\\boolt').
format_base_type(list-T, Out) :-
    format_type(T, TStr),
    format(atom(Out), '\\tableT(\\cdot)~~~w', [TStr]).

format_quant(empty, '\\emptyq').
format_quant(one, '\\one').
format_quant(any, '\\any').
format_quant(nonempty, '\\nonempty').

format_func(id, '\\id_{\\types}').
format_func(with(Q), Out) :-
    format_quant(Q, QStr),
    format(atom(Out), '\\with_{~w}', [QStr]).
format_func(add(Q), Out) :-
    format_quant(Q, QStr),
    format(atom(Out), '\\oplus {~w}', [QStr]).
format_func(subtract(Q), Out) :-
    format_quant(Q, QStr),
    format(atom(Out), '\\ominus {~w}', [QStr]).
format_func(max(F,G), Out) :-
    format_func(F, FStr),
    format_func(G, GStr),
    format(atom(Out), '\\max(~w, ~w)', [FStr, GStr]).

format_type(Q-T, Out) :-
    format_quant(Q, QStr),
    format_base_type(T, TStr),
    format(atom(Out), '~w~~~w', [QStr, TStr]).

format_var_type(X:T, Out) :-
    format_var(X, XStr),
    format_type(T, TStr),
    format(atom(Out), '~w : ~w', [XStr, TStr]).

format_var(X, X) :- atom(X).
format_var(loc(L, loc(K)), Out) :- format(atom(Out), '(~w,~w)', [L, K]).
format_var(loc(L, amount(N)), Out) :- format(atom(Out), '(~w, \\amount(~w))', [L, N]).

format_env([], '\\emptyset').
format_env([H|T], Out) :-
    maplist(format_var_type, [H|T], OutStrs),
    atomic_list_concat(OutStrs, ',', Temp),
    format(atom(Out), '\\{ ~w \\}', [Temp]).

as_quant(0, empty).
as_quant(1, one).
as_quant(N, nonempty) :- N #> 1.

add_quant(Q, empty, Q).
add_quant(empty, Q, Q).
add_quant(nonempty, _R, nonempty).
add_quant(_R, nonempty, nonempty).
add_quant(one, R, nonempty) :- dif(R, empty).
add_quant(R, one, nonempty) :- dif(R, empty).
add_quant(any, any, any).

subtract_quant(Q, empty, Q).
subtract_quant(empty, _, empty).
subtract_quant(any, _, any).
subtract_quant(Q, any, any) :- dif(Q, empty).
subtract_quant(one, one, empty).
subtract_quant(nonempty, nonempty, any).

quant_lt_base(empty, any).
quant_lt_base(any, one).
quant_lt_base(one, nonempty).
quant_lt(Q, R) :- quant_lt_base(Q, R).
quant_lt(Q, R) :- quant_lt_base(Q, S), quant_lt(S, R).

max_quant(Q, Q, Q).
max_quant(Q, R, Q) :- quant_lt(R, Q).
max_quant(Q, R, R) :- quant_lt(Q, R).

max_type(Q-T, R-T, S-T) :- max_quant(Q, R, S).

apply_func(id, T, T).
apply_func(with(Q), _-T, Q-T).
apply_func(add(R), Q-T, S-T) :- add_quant(Q, R, S).
apply_func(subtract(R), Q-T, S-T) :- subtract_quant(Q, R, S).
apply_func(max(F,G), T1, T2) :-
    apply_func(F, T1, T1F),
    apply_func(G, T1, T1G),
    max_type(T1F, T1G, T2).

subtype(Q-T, R-T) :- subquant(Q, R).
subquant(empty, any).
subquant(one, any).
subquant(nonempty, any).
subquant(one, nonempty).

well_typed(loc_type([], 'Nat', Gamma, source, _F, nat(N), Q-nat, Gamma)) :-
    as_quant(N, Q).

well_typed(loc_type([], 'Bool', Gamma, source, _F, bool(_B), any-bool, Gamma)).

well_typed(loc_type([], 'Var', Gamma, _M, F, v(X), Q-T, Delta)) :-
    select(X : Q-T, Gamma, Temp),
    apply_func(F, Q-T, NewT),
    select(X : NewT, Delta, Temp).

well_typed(loc_type([], 'Loc', Gamma, _M, F, loc(L, K), Q-T, Delta)) :-
    select(loc(L, K) : Q-T, Gamma, Temp),
    apply_func(F, Q-T, NewT),
    select(loc(L, K) : NewT, Delta, Temp).

well_typed(loc_type([], 'VarDef', Gamma, dest, F, vardef(X, T), empty-T, Delta)) :-
    apply_func(F, empty-T, NewT),
    select(X:NewT, Delta, Gamma).

well_typed(loc_type([], 'EmptyList', Gamma, source, _F, emptylist(ElemT), empty-(list-ElemT), Gamma)).

well_typed(loc_type([HeadPrf, TailPrf], 'ConsList', Gamma, source, F, list(ElemT, Head, Tail), NewQuant-(list-ElemT), Xi)) :-
    HeadPrf = loc_type(_, _, Gamma, source, F, Head, ElemT, Delta),
    well_typed(HeadPrf),

    TailPrf = loc_type(_, _, Delta, source, F, Tail, Q-(list-ElemT), Xi),
    well_typed(TailPrf),

    add_quant(Q, one, NewQuant).

well_typed(loc_type([ChildPrf], 'Filter', Gamma, M, F, filter(Loc, Q), Q-T, Delta)) :-
    ChildPrf = loc_type(_, _, Gamma, M, max(subtract(Q), F), Loc, _-T, Delta),
    well_typed(ChildPrf).
    % quant_lt(Q, R).

well_typed(loc_type([ChildPrf], 'Copy', Gamma, source, F, copy(Loc), DemotedT, Gamma)) :-
    ChildPrf = loc_type(_, _, Gamma, source, id, Loc, T, Gamma),
    demote(T, DemotedT).

well_typed(loc_type([ChildPrf], 'SubQuant', Gamma, M, F, Loc, T, Delta)) :-
    dif(T, T2), % Not strictly required, but it'd be pointless to use the rule like this
    subtype(T2, T),

    ChildPrf = loc_type(_, _, Gamma, M, F, Loc, T2, Delta),
    well_typed(ChildPrf).

demote(Q-BaseT, Q-DemotedBaseT) :-
    demoteBase(BaseT, DemotedBaseT).

% TODO: Will need to expand this more
demoteBase(nat, nat).
demoteBase(bool, bool).

fst(A-_,A).
snd(_-B,B).

fresh([], 0).
fresh([H|T], N) :-
    maplist(fst, [H|T], Keys),
    max_member(M, Keys),
    N #= M + 1.

empty_val(nat, 0).
empty_val(bool, false).
empty_val(list-_, []).

located(loc(_,_)).
located(emptylist(_)).
located(list(_, Head, Tail)) :- located(Head), located(Tail).

eval_step(loc_eval([], 'ENat',
            (Mu,Rho,nat(N)),
            (Mu,[L-resource(nat,N)|Rho],loc(L, amount(N))))) :-
    fresh(Rho, L).

eval_step(loc_eval([], 'EBool',
            (Mu,Rho,bool(B)),
            (Mu,[L-resource(bool,B)|Rho],loc(L, loc(L))))) :-
    fresh(Rho, L).

eval_step(loc_eval([], 'EVar',
            (Mu,Rho,v(X)),
            (Mu,Rho,L))) :-
    member(X-L, Mu).

eval_step(loc_eval([], 'VarDef',
            (Mu,Rho,vardef(X, T)),
            ([X-L|Mu],[L-resource(T, V)|Rho],loc(L, loc(L))))) :-
    fresh(Rho, L),
    empty_val(T, V).

eval_step(loc_eval([HeadPrf], 'EConsListHeadCongr',
            (Mu,Rho,list(T,Head,Tail)),
            (NewMu,NewRho,list(T,NewHead,Tail)))) :-
    HeadPrf = loc_eval(_, _, (Mu,Rho,Head), (NewMu,NewRho,NewHead)),
    eval_step(HeadPrf).

eval_step(loc_eval([TailPrf], 'EConsListTailCongr',
            (Mu,Rho,list(T,Head,Tail)),
            (NewMu,NewRho,list(T,Head,NewTail)))) :-
    located(Head),
    TailPrf = loc_eval(_, _, (Mu,Rho,Tail), (NewMu,NewRho,NewTail)),
    eval_step(TailPrf).

update_env(loc_eval([], 'ENat', (_,_,nat(N)), (_,_,loc(L,amount(N)))),
           Gamma, [loc(L,amount(N)) : Q-nat|Gamma]) :-
    as_quant(N, Q).

update_env(loc_eval([], 'EBool', (_,_,bool(_)), (_,_,loc(L,loc(L)))),
            Gamma, [loc(L,loc(L)) : any-bool|Gamma]).

update_env(loc_eval([], 'EVar', (_,_,v(X)), (_,_,L)),
            Gamma, FinalGamma) :-
    select(X : Q-T, Gamma, Temp),
    select(X : empty-T, NewGamma, Temp),
    (
        member(L : _, NewGamma),
        NewGamma = FinalGamma
        % select(L : _, NewGamma, Temp2),
        % select(L : Q-T, FinalGamma, Temp2)
    ;
        select(L : Q-T, FinalGamma, NewGamma)
    ).

update_env(loc_eval([], 'EVarDef', (_,_,vardef(X,T)), (_,_,L)),
            Gamma, [X : empty-T, L : empty-T|Gamma]).

update_env(loc_eval([HeadPrf], 'EConsListHeadCongr', _, _), Gamma, NewGamma) :-
    update_env(HeadPrf, Gamma, NewGamma).

update_env(loc_eval([TailPrf], 'EConsListTailCongr', _, _), Gamma, NewGamma) :-
    update_env(TailPrf, Gamma, NewGamma).

