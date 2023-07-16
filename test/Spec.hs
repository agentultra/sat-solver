import Data.Algorithm.SAT
import Data.Maybe
import qualified Data.Map as M
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

prop_conj :: Int -> Property
prop_conj n =
  forAll (genAssignment n) $ \sigma ->
  forAllShrink (genFormula n) shrink $ \f ->
  forAllShrink (genFormula n) shrink $ \f' ->
  counterexample ("f `conj` f' == " ++ show (f `conj` f')) $
  eval sigma (f `conj` f') === ((&&) <$> eval sigma f <*> eval sigma f')

prop_disj :: Int -> Property
prop_disj n =
  forAll (genAssignment n) $ \sigma ->
  forAllShrink (genFormula n) shrink $ \f ->
  forAllShrink (genFormula n) shrink $ \f' ->
  counterexample ("f `disj` f' == " ++ show (f `disj` f')) $
  eval sigma (f `disj` f') === ((||) <$> eval sigma f <*> eval sigma f')

prop_solve_spec' :: Assignment -> Formula -> Maybe Formula -> Property
prop_solve_spec' _as f (Just f') =
  forAll (genAssignmentFor f) $ \as ->
    counterexample ("subst:      " ++ show (map (M.mapWithKey (test as)) $ getClauses f)) $
    counterexample "f" (eval as f === Just False) .&&.
    counterexample "f'" (eval as f' === Just False)
prop_solve_spec' as  f Nothing = evalPartial as f === True

prop_solve_spec :: Formula -> Property
prop_solve_spec f =
  let (f', a) = fromJust $ runSolver (solve f) in
    counterexample ("assignment: " ++ show a) $
    counterexample ("unsat core: " ++ show f') $
    counterexample ("free vars:  " ++ show (freeVars f)) $
    counterexample ("clauses:    " ++ show (getClauses f)) $
    counterexample ("subst:      " ++ show (map (M.mapWithKey (test a)) $ getClauses f)) $

    prop_solve_spec' a f f'

test_simplification_on_contr :: SpecWith ()
test_simplification_on_contr =
  it "unitClausePropagation on contradiction" $
    runSolver' (unitClausePropagation f) `shouldBe` (false, Assgn $ M.fromList [(x0, True)])
  where
    f = fromListLit [ [Pos x0], [Neg x0] ]
    x0 = Var 0

test_weirdly_unsat :: SpecWith ()
test_weirdly_unsat =
  it "check systematic simplification" $
    runSolver' (solve f) `shouldBe` (Nothing, Assgn assgn)
  where
    f = fromListLit [ [Pos x0, Neg x1, Pos x2], [Neg x0, Pos x1, Neg x2] ]
    x0 = Var 0
    x1 = Var 1
    x2 = Var 2
    assgn = M.fromList [(x0, True), (x1, True), (x2,False)]


singleExample :: Formula -> Solver (Formula, Formula)
singleExample f = do
  f'  <- unitClausePropagation f
  f'' <- pureLitElimination f'
  return (f', f'')

singleTest :: Property
singleTest =
  let x0 = Var 0
      x1 = Var 1
      x2 = Var 2
      f = fromListLit [ [Pos x0], [Neg x0, Pos x1, Pos x2], [Pos x1, Neg x2], [Pos x0, Pos x1, Pos x2] ]
      ((f', f''), a) = runSolver' (singleExample f) in
    counterexample ("assignment: " ++ show a) $
    f'  === fromListLit [ [Pos x1, Neg x2], [Pos x1, Pos x2] ] .&&.
    f'' === true

main :: IO ()
main = do
  hspec $ do
    prop "conj" prop_conj
    prop "disj" prop_disj
    prop "single test" singleTest
    prop "solve spec" prop_solve_spec
    test_simplification_on_contr
    test_weirdly_unsat
  putStrLn "-----"
  sample $ do
    a <- arbitrary
    return (a, runSolver (solve a))
