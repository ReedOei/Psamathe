<storage>
    ...
    (Loc |-> resource(Main, Balance |-> BalanceLoc))
    (BalanceLoc |-> resource(nat, 1))
    ...
</storage>
requires Main ==K String2Id("Main") andBool Balance ==K String2Id("balance")
