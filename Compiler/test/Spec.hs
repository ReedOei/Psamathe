import Test.Hspec

import Text.Parsec

import AST
import Parser

main :: IO ()
main = hspec $ do
    parserTests

parserTests = do
    describe "parseStmt" $ do
        it "parses simple flows" $ do
            parse parseStmt "" "x --> y" `shouldBe` Right (Flow (Var "x") (Var "y"))
            parse parseStmt "" "[ any nat ; ] --> var m : map any nat => any nat" `shouldBe` Right (Flow (Multiset (Any,Nat) []) (NewVar "m" (Table ["key"] (One,Record ["key"] [("key",(Any,Nat)),("value",(Any,Nat))]))))
        it "parses simple backwards flows" $
            parse parseStmt "" "y <-- 1" `shouldBe` Right (Flow (IntConst 1) (Var "y"))

        it "parses transformer flows" $
            parse parseStmt "" "x --> f() --> var t : nat" `shouldBe` Right (FlowTransform (Var "x") (Call "f" []) (NewVar "t" Nat))
        it "parses backwards transformer flows" $
            parse parseStmt "" "var ts : multiset any nat <-- g(y) <-- [ any nat; ]" `shouldBe` Right (FlowTransform (NewVar "ts" (Table [] (Any,Nat))) (Call "g" [Var "y"]) (Multiset (Any,Nat) []))

        it "parses try-catch statements" $
            parse parseStmt "" "try {} catch {}" `shouldBe` Right (Try [] [])

        it "parses flows with selector arrow" $
            parse parseStmt "" "x --[ 5 ]-> y" `shouldBe` Right (Flow (Select (Var "x") (IntConst 5)) (Var "y"))
        it "parses backwards flows with selector arrow" $
            parse parseStmt "" "var t : bool <-[ z ]-- [ any bool; true, false] " `shouldBe` Right (Flow (Select (Multiset (Any,PsaBool) [BoolConst True,BoolConst False]) (Var "z")) (NewVar "t" PsaBool))

        it "parses flows with filters" $ do
            parse parseStmt "" "A --[ nonempty such that isWinner(winNum) ]-> var winners : mutliset one Ticket" `shouldBe` Right (Flow (Filter (Var "A") Nonempty "isWinner" [Var "winNum"]) (NewVar "winners" (Named "mutliset")))
        it "parses backwards flows with filters" $ do
            parse parseStmt "" "vals <-[ any such that nonzero() ]-- src" `shouldBe` Right (Flow (Filter (Var "src") Any "nonzero" []) (Var "vals"))

