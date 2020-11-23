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
    Loc = list(any-bool, v(x), list(any-bool, v(x), emptylist(any-bool))),
    Proof = loc_type(_, _, [x:any-bool], source, with(empty), Loc, _, _),
    EvalProof = loc_eval(_, _, ([x-loc(0,loc(0))],[0-resource(bool,false)],Loc), _),
    eval_step(EvalProof),
    well_typed(Proof) ->
        format_proof(Proof, Out),
        writeln(Out),
        writeln('\\end{mathpar}'),
        writeln('\\begin{mathpar}'),
        format_proof(EvalProof, EvalOut),
        writeln(EvalOut);

    writeln('\\text{\\textcolor{red}{FAILED!}}').

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
    format(atom(Formatted),
           '\\inferrule*[right=~w]{ ~w }{\\angles{ (~w, ~w), ~w } \\to \\angles{ (~w, ~w), ~w } }',
           [Rule, FormatPrems, Mu, Rho, LocStr, NewMu, NewRho, NewLocStr]).

format_loc(nat(N), Out) :- format(atom(Out), '~w', [N]).
format_loc(bool(true), '\\true').
format_loc(bool(false), '\\false').
format_loc(v(X), X).
format_loc(emptylist(ElemT), Out) :-
    format_type(ElemT, TStr),
    format(atom(Out), '[ ~w ; ]', [TStr]).
format_loc(list(ElemT, Head, Tail), Out) :-
    format_type(ElemT, TStr),
    format_loc(Head, HeadStr),
    format_loc(Tail, TailStr),
    format(atom(Out), '[ ~w ; ~w, ~w ]', [TStr, HeadStr, TailStr]).
format_loc(loc(L, K), Out) :- format(atom(Out), '(~w,~w)', [L, K]).

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

format_type(Q-T, Out) :-
    format_quant(Q, QStr),
    format_base_type(T, TStr),
    format(atom(Out), '~w~~~w', [QStr, TStr]).

format_var_type(X:T, Out) :-
    format_type(T, TStr),
    format(atom(Out), '~w : ~w', [X, TStr]).

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

apply_func(id, T, T).
apply_func(with(Q), _-T, Q-T).

subtype(Q-T, R-T) :- subquant(Q, R).
subquant(empty, any).
subquant(one, any).
subquant(nonempty, any).
subquant(one, nonempty).

well_typed(loc_type([], 'Nat', Gamma, source, _F, nat(N), Q-nat, Gamma)) :-
    as_quant(N, Q).

well_typed(loc_type([], 'Bool', Gamma, source, _F, bool(_B), any-bool, Gamma)).

well_typed(loc_type([], 'Var', Gamma, _M, F, v(X), Q-T, Delta)) :-
    select(X:Q-T, Gamma, Temp),
    apply_func(F, Q-T, NewT),
    select(X:NewT, Delta, Temp).

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

well_typed(loc_type([ChildPrf], 'SubQuant', Gamma, M, F, Loc, T, Delta)) :-
    dif(T, T2), % Not strictly required, but it'd be pointless to use the rule like this
    subtype(T2, T),

    ChildPrf = loc_type(_, _, Gamma, M, F, Loc, T2, Delta),
    well_typed(ChildPrf).

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
% eval_step(loc_eval([TailPrf], 'EConsListTailCongr',
%             (Mu,Rho,list(T,Head,Tail)),
%             (NewMu,NewRho,list(T,NewHead,Tail)))) :-
%     HeadPrf = loc_eval(_, _, (Mu,Rho,Head), (NewMu,NewRho,NewHead)),
%     eval_step(HeadPrf).

