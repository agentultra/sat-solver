import Data.Algorithm.SAT
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

single_example f = do
  f'  <- unitClausePropagation f
  f'' <- pureLitElimination f'
  return (f', f'')

single_test =
  let x0 = Var 0
      x1 = Var 1
      x2 = Var 2
      f = fromListLit [ [Pos x0], [Neg x0, Pos x1, Pos x2], [Pos x1, Neg x2], [Pos x0, Pos x1, Pos x2] ]
      ((f', f''), a) = runSolver (single_example f) in
    counterexample ("assignment: " ++ show a) $
    counterexample ("f:   " ++ show f) $
    counterexample ("f':  " ++ show f') $
    counterexample ("f'': " ++ show f'') $
    f === f'

main :: IO ()
main = hspec $ do
  prop "conj" prop_conj
  prop "disj" prop_disj
  prop "single test" single_test
