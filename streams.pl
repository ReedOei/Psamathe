    op nil : -> TyEnv [ctor] .
    op _:_ : Qid Ty -> TyEnv [ctor] .
    op _;_ : TyEnv TyEnv -> TyEnv [ctor comm assoc id: nil] .

    --- op _-|_ : Ty TyEnv -> TyRes [ctor frozen] .
    op _|-_:_ : TyEnv Expr Ty -> TyEnv [frozen] .

    vars Gamma Delta Xi Gamma1 Gamma2 : TyEnv .

prove(well_typed('Iden', [], Gamma, id(N), ty(1, nonasset, iden), Gamma)).
prove(well_typed('Var', [], Gamma, X, ty(oo, M, T), Gamma)) :-
    member(X-ty(oo, M, T), Gamma).
prove(well_typed('Var', [], Gamma, X, ty(Q, M, T), Delta)) :-
    select(X-ty(Q, M, T), Gamma, Delta).
prove(well_typed('Copy', [EPrf], Gamma, copy(E), DemotedTau, Gamma)) :-
    EPrf = well_typed(_, _, Gamma, E, Tau, Delta),
    prove(EPrf),
    demote(Tau, DemotedTau).

    op _@_ : TyQuant TyQuant -> TyQuant [comm assoc id: 0] .
    eq * @ Q = * .
    eq oo @ Q = oo .
    eq N1 @ N2 = N1 + N2 .

    rl Gamma |- { mt } : 0 M multiset Tau => Gamma .
    --- crl Gamma |- { Vs } => | Vs | M multiset (Q M T) -| Delta
    ---     if checkEach(Gamma, Vs) => Q M T -| Delta .

    op _\/_ : Mode Mode -> Mode [comm assoc id: nonasset] .

    crl Gamma |- [ E1 ; E2 ] : 1 M (Q1 M1 T1 x Q2 M2 T2) => Xi
        if Gamma |- E1 : Q1 M1 T1 => Delta /\
           Delta |- E2 : Q2 M2 T2 => Xi /\
           M == M1 \/ M2 .

    crl Gamma |- E1 E2 : Sigma => Xi
        if Gamma |- E1 : 1 asset (Tau -> Sigma) => Delta /\
           Delta |- E2 : Tau => Xi .

    op resource : -> Ty .

    crl Gamma |- zero => 1 M T -| Gamma
        if resource => Q M T .

    rl Gamma |- fail => * nonasset unit -| Gamma .

    --- TODO: We need to add a check for resources
    crl Gamma |- sum(E) => Tau -| Delta
        if Gamma |- E => Q M multiset Tau -| Delta .

    crl Gamma |- sub(E1, E2) => Tau -| Xi
        if Gamma |- E1 => Tau -| Delta /\
           Delta |- E2 => Tau -| Xi .

    --- TODO: Need to make sure this is right...and that we can drop the resources.
    crl Gamma |- (lambda X : Tau . E) => 1 asset (Tau -> Sigma) -| Delta
        if (Gamma ; X : Tau) |- E => Sigma -| Delta .
    crl Gamma |- (lambda X : Tau . E) => oo nonasset (Tau -> Sigma) -| Gamma
        if (X : Tau) |- E => Sigma -| Delta .

    op joinEnv : TyEnv TyEnv -> TyEnv [comm assoc id: nil] .
    crl Gamma |- try { E1 } catch { E2 } => Tau -| joinEnv(Delta, Xi)
        if Gamma |- E1 => Tau -| Delta /\
           Gamma |- E2 => Tau -| Xi .

    crl Gamma |- label(E) => Q M multiset (1 M2 (1 nonasset iden x (Q2 M2 T))) -| Delta
        if Gamma |- E => Q M multiset (Q2 M2 T) -| Delta .

    crl (Gamma ; X : Q2 M T) |- assert X is Q in E => Tau -| Delta
        if (Gamma ; X : Q M T) |- E => Tau -| Delta .

    --- TODO: Need to drop the variables
    crl Gamma |- let [ X ; Y ] := E1 in E2 => Pi -| Xi
        if Gamma |- E1 => 1 M (Tau x Sigma) -| Delta /\
           (Delta ; (X : Tau) ; (Y : Sigma)) |- E2 => Pi -| Xi .

    crl Gamma |- let [ X ] := E1 in E2 => Sigma -| Xi
        if Gamma |- E1 => Q M multiset Tau -| Delta /\
           (Delta ; X : Tau) |- E2 => Sigma -| Xi .

    op groupWith : TyQuant Expr Expr Expr -> Expr [ctor frozen] .
    crl Gamma |- groupWith(Q, F, E1, E2) => Q M (multiset (R M T)) -| Gamma1
        --- TODO: Need to ensure that Tau has decidable equality
        if Gamma |- F => oo nonasset (1 M2 (Tau x Q3 (M2 \/ M4) (Sigma x Pi)) -> R M T) -| Delta /\
           Delta |- E1 => Q1 M1 (multiset (1 M2 (Tau x Sigma))) -| Xi /\
           Xi |- E2 => Q2 M3 (multiset (1 M4 (Tau x Pi))) -| Gamma1 .

