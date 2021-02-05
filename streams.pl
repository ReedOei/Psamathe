:- use_module(library(clpfd)).

add_quant(any, _, any).
add_quant(oo, _, oo).
add_quant(0, Q, Q).

join_mode(M, M, M).

join_env(Gamma, Gamma, Gamma).

prove(well_typed('Zero', [], Gamma, zero, ty(0, M, T), Gamma)).
prove(well_typed('Fail', [], Gamma, fail, Tau, Gamma)).
prove(well_typed('Iden', [], Gamma, id(N), ty(1, nonasset, iden), Gamma)).
prove(well_typed('Var', [], Gamma, X, ty(oo, M, T), Gamma)) :-
    member(X-ty(oo, M, T), Gamma).
prove(well_typed('Var', [], Gamma, X, ty(Q, M, T), Delta)) :-
    select(X-ty(Q, M, T), Gamma, Delta).
prove(well_typed('Copy', [EPrf], Gamma, copy(E), DemotedTau, Gamma)) :-
    EPrf = well_typed(_, _, Gamma, E, Tau, Delta),
    prove(EPrf),
    demote(Tau, DemotedTau).
prove(well_typed('Multiset-Empty', [], Gamma, [], ty(0, M, multiset(Tau)), Delta)).
prove(well_typed('Multiset-Cons', [Prf, TailPrf], Gamma, [H|T], ty(Q, M, multiset(Tau)), Xi)) :-
    Prf = well_typed(_, _, Gamma, H, Tau, Delta),
    prove(Prf),
    TailPrf = well_typed(_, _, Delta, T, ty(R, M, multiset(Tau)), Xi),
    prove(TailPrf),
    add_quant(1, R, Q).
prove(well_typed('Pair', [LeftPrf, RightPrf], Gamma, Left-Right, ty(1, M, pair(Tau, Sigma)), Xi)) :-
    LeftPrf = well_typed(_, _, Gamma, Left, Tau, Delta),
    prove(LeftPrf),
    RightPrf = well_typed(_, _, Delta, Right, Sigma, Delta),
    prove(RightPrf),
    Tau = ty(_, M1, _),
    Sigma = ty(_, M2, _),
    join_mode(M1, M2, M_).
prove(well_typed('App', [FunPrf, ArgPrf], Gamma, app(F,E), Sigma, Xi)) :-
    FunPrf = well_typed(_, _, Gamma, F, ty(Q, M, fun(Tau, Sigma)), Delta),
    prove(FunPrf),
    ArgPrf = well_typed(_, _, Delta, E, Tau, Xi).
prove(well_typed('Sum', [Prf], Gamma, sum(E), Tau, Delta)) :-
    % TODO: We need to add a check for resources
    Prf = well_typed(_, _, Gamma, E, ty(Q, M, multiset(Tau)), Delta),
    prove(Prf).
prove(well_typed('Sub', [E1Prf, E2Prf], Gamma, sub(E1, E2), Tau, Xi)) :-
    E1Prf = well_typed(_, _, Gamma, E1, Tau, Delta),
    prove(E1Prf),
    E2Prf = well_typed(_, _, Delta, E2, Tau, Xi),
    prove(E2Prf).
% TODO: Need to make sure this is right...and that we can drop the resources.
prove(well_typed('Fun-Lin', [Prf], Gamma, lambda(X, Tau, E), ty(1, asset, fun(Tau, Sigma)), Delta)) :-
    Prf = well_typed(_, _, [X-Tau|Gamma], E, Sigma, Delta),
    prove(Prf).
prove(well_typed('Fun-Inf', [Prf], Gamma, lambda(X, Tau, E), ty(oo, nonasset, fun(Tau, Sigma)), Delta)) :-
    Prf = well_typed(_, _, [X-Tau], E, Sigma, _),
    prove(Prf).
prove(well_typed('Try', [TryPrf, CatchPrf], Gamma, try(E1, E2), Tau, Out)) :-
    TryPrf = well_typed(_, _, Gamma, E1, Tau, Delta),
    prove(TryPrf),
    CatchPrf = well_typed(_, _, Gamma, E2, Tau, Xi),
    prove(CatchPrf),
    join_env(Delta, Xi, Out).
prove(well_typed('Label', [Prf], Gamma, label(E), ty(Q, M1, multiset(ty(1, M2, pair(ty(1, nonasset, iden), ty(Q2, M2, T))))), Delta)) :-
    Prf = well_typed(_, _, Gamma, E, ty(Q, M, multiset(ty(Q2, M2, T))), Delta),
    prove(Prf).
prove(well_typed('Assert', [Prf], Gamma, assert(X, Q, E), Tau, Delta)) :-
    select(X-ty(Q2,M,T), Gamma, Temp),
    Prf = well_typed(_, _, [X-ty(Q,M,T)|Temp], E, Tau, Delta),
    prove(Prf).
prove(well_typed('LetPair', [EPrf, BodyPrf], Gamma, let(X, Y, E1, E2), Pi, Xi)) :-
    % TODO: Need to drop the variables
    EPrf = well_typed(_, _, Gamma, E1, ty(1, M, pair(Tau, Sigma)), Delta),
    prove(EPrf),
    BodyPrf = well_typed(_, _, [X-Tau, Y-Sigma|Delta], E2, Pi, Xi),
    prove(BodyPrf).
prove(well_typed('LetMultiset', [EPrf, BodyPrf], Gamma, let(X, E1, E2), Pi, Xi)) :-
    EPrf = well_typed(_, _, Gamma, E1, ty(Q, M, multiset(Tau)), Delta),
    prove(EPrf),
    BodyPrf = well_typed(_, _, [X-Tau|Delta], E2, Pi, Xi),
    prove(BodyPrf).
prove(well_typed('GroupWith', [FPrf, E1Prf, E2Prf], Gamma, groupWith(Q, F, E1, E2), ty(Q, M, multiset(ty(R, M2, T))), Out)) :-
    % TODO: Need to ensure that Tau has decidable equality
    FPrf = well_typed(_, _, Gamma, F, ty(oo, nonasset, fun(ty(1, InM, pair(Tau, type(_, M5, pair(Sigma, Pi)))), ty(R, M2, T))), Delta),
    prove(FPrf),
    E1Prf = well_typed(_, _, Delta, E1, ty(Q1, M1, multiset(ty(1, M3, pair(Tau, Sigma)))), Xi),
    prove(E1Prf),
    E2Prf = well_typed(_, _, Xi, E2, ty(Q2, M4, multiset(ty(1, M5, pair(Tau, Pi)))), Out),
    prove(E2Prf),
    join_mode(M3, M5, InM).

