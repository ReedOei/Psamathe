{-# LANGUAGE FlexibleContexts #-}

import Control.Lens ((^.))
import Control.Monad.State

import Data.Either (isRight)

import Test.Hspec

import Text.Parsec

import AST
import Env
import Preprocessor
import Parser

main :: IO ()
main = hspec $ do
    preprocessorTests
    parserTests

parseAndCheck parser str =
    case parse parser "" str of
        res@Left{} -> do
            res `shouldSatisfy` isRight -- We want to fail
            undefined
        Right term -> pure term

x `shouldBeStmts` stmtsStr = do
    res <- parseAndCheck (do { x <- many parseStmt; eof; pure x }) stmtsStr
    x `shouldReturn` res

-- | A version of evalState that asserts that there were no errors before returning the result
evalEnv env toEval = do
    let (res, finalEnv) = runState toEval env
    finalEnv^.errors `shouldBe` []
    pure res

preprocessorTests = do
    describe "preprocessCond" $ do
        it "expands simple preconditions" $ do
            evalEnv newEnv (preprocessCond (BinOp OpLe (Var "x") (Var "y")))
                `shouldBeStmts` "y --[ x ]-> y"

            evalEnv newEnv (preprocessCond (BinOp OpEq (Select (Var "x") (Var "vs")) (Var "y")))
                `shouldBeStmts` unlines ["x[vs] --[ y ]-> x[vs]",
                                         "y --[ x[vs] ]-> y"]

            evalEnv newEnv (preprocessCond (BinOp OpLe (IntConst 1) (IntConst 3)))
                `shouldBeStmts` unlines ["1 --> var v0 : nat",
                                         "3 --> var v1 : nat",
                                         "v1 --[ v0 ]-> v1"]

        it "expands conjunctions of preconditions" $ do
            evalEnv newEnv (preprocessCond (Conj [BinOp OpNe (Var "x") (Var "y"), BinOp OpIn (Var "x") (Multiset (Any,Nat) [ IntConst 0, IntConst 1 ])]))
                `shouldBeStmts` unlines ["try {",
                                         "    x --[ y ]-> x",
                                         "    y --[ x ]-> y",
                                         "    revert",
                                         "} catch {}",
                                         "[ any nat; 0,1 ] --> var v1 : multiset any nat",
                                         "v1 --[ x ]-> v1"]

parserTests = do
    describe "parseStmt" $ do
        it "parses simple flows" $ do
            parse parseStmt "" "x --> y"
                `shouldBe` Right (Flow (Var "x") (Var "y"))
            parse parseStmt "" "[ any nat ; ] --> var m : map any nat => any nat"
                `shouldBe` Right (Flow (Multiset (Any,Nat) []) (NewVar "m" (Table ["key"] (One,Record ["key"] [("key",(Any,Nat)),("value",(Any,Nat))]))))
        it "parses simple backwards flows" $
            parse parseStmt "" "y <-- 1"
                `shouldBe` Right (Flow (IntConst 1) (Var "y"))

        it "parses transformer flows" $
            parse parseStmt "" "x --> f() --> var t : nat"
                `shouldBe` Right (FlowTransform (Var "x") (Call "f" []) (NewVar "t" Nat))
        it "parses backwards transformer flows" $
            parse parseStmt "" "var ts : multiset any nat <-- g(y) <-- [ any nat; ]"
                `shouldBe` Right (FlowTransform (NewVar "ts" (Table [] (Any,Nat))) (Call "g" [Var "y"]) (Multiset (Any,Nat) []))

        it "parses try-catch statements" $
            parse parseStmt "" "try {} catch {}"
                `shouldBe` Right (Try [] [])

        it "parses flows with selector arrow" $
            parse parseStmt "" "x --[ 5 ]-> y"
                `shouldBe` Right (Flow (Select (Var "x") (IntConst 5)) (Var "y"))
        it "parses backwards flows with selector arrow" $
            parse parseStmt "" "var t : bool <-[ z ]-- [ any bool; true, false] "
                `shouldBe` Right (Flow (Select (Multiset (Any,PsaBool) [BoolConst True,BoolConst False]) (Var "z")) (NewVar "t" PsaBool))

        it "parses flows with filters" $ do
            parse parseStmt "" "A --[ nonempty such that isWinner(winNum) ]-> var winners : mutliset one Ticket"
                `shouldBe` Right (Flow (Filter (Var "A") Nonempty "isWinner" [Var "winNum"]) (NewVar "winners" (Named "mutliset")))
        it "parses backwards flows with filters" $ do
            parse parseStmt "" "vals <-[ any such that nonzero() ]-- src"
                `shouldBe` Right (Flow (Filter (Var "src") Any "nonzero" []) (Var "vals"))

        it "parses preconditions" $ do
            parse parseStmt "" "only when 1 < 2"
                `shouldBe` Right (OnlyWhen (BinOp OpLt (IntConst 1) (IntConst 2)))
            parse parseStmt "" "only when x = y and z in w"
                `shouldBe` Right (OnlyWhen (Conj [BinOp OpEq (Var "x") (Var "y"), BinOp OpIn (Var "z") (Var "w")]))

        it "parses revert" $ do
            parse parseStmt "" "revert"
                `shouldBe` Right Revert

