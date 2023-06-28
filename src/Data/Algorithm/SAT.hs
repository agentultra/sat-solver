module Data.Algorithm.SAT where

import Control.Monad.State
import Data.List as L
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Maybe
import Data.Monoid
import Lens.Micro
import qualified Data.List.Ordered as Ord
import Test.QuickCheck

newtype Var = Var Int
  deriving (Eq, Ord)

instance Show Var where
  show (Var x) = "x" ++ show x

data Lit = Pos Var | Neg Var

instance Show Lit where
  show (Pos x) = show x
  show (Neg x) = "¬" ++ show x

mkLit :: Bool -> Var -> Lit
mkLit True  v = Pos v
mkLit False v = Neg v

-- in conjunctive normal form:
--   a formula is a conjunction of clauses
--   a clause is disjunction of literals
--   a literal is a variable with or without negation
newtype Formula = Formula [Map Var Bool]
  -- deriving Show

newtype Assignment = Assgn (Map Var Bool)
  deriving Show

showClause :: Map Var Bool -> String
showClause fs
  | null fs = "false"
  | otherwise = intercalate " ∨ " [ show (mkLit sign v) | (v,sign) <- M.toList fs ]

instance Show Formula where
  show (Formula fs)
    | null fs   = "true"
    | otherwise = intercalate " ∧ " $ map (\c -> "(" ++ showClause c ++ ")") fs

assignment :: Lens' Assignment (Map Var Bool)
assignment f (Assgn m) = Assgn <$> f m

test :: Assignment -> Var -> Bool -> Maybe Bool
test (Assgn m) v p = fmap (/= p) . M.lookup v $ m

eval :: Assignment -> Formula -> Maybe Bool
eval asgn (Formula fs) = and <$> mapM (fmap or . M.traverseWithKey (test asgn)) fs

conj :: Formula -> Formula -> Formula
conj (Formula xs) (Formula ys) = Formula $ xs ++ ys

disjClause :: Map Var Bool -> Map Var Bool -> Maybe (Map Var Bool)
disjClause mx my = do
  let mz = M.mergeWithKey (\_k x y -> guard (x /= y))
            (const M.empty) (const M.empty) mx my
  let mz' = mx `M.union` my
  guard (not (M.null mz) || M.null mz')
  return mz'

disj :: Formula -> Formula -> Formula
disj (Formula xs) (Formula ys) =
  Formula $ Ord.nub $ catMaybes [ disjClause x y | x <- xs, y <- ys ]

data FmlAssgnPair = FAP Formula Assignment

genClause :: Int -> Gen (Map Var Bool)
genClause n = do
  l <- forM [0..n] (\i ->
    fmap (Var i,) <$> arbitrary)
  return $ M.fromList $ catMaybes l

instance Arbitrary Var where
  arbitrary = Var <$> arbitrary

instance Arbitrary Formula where
  arbitrary = genFormula =<< arbitrary
  shrink (Formula fs) = mkFormula <$> shrink fs

instance Arbitrary Assignment where
  arbitrary = genAssignment =<< arbitrary
  shrink (Assgn fs) = Assgn <$> shrink fs


instance Arbitrary FmlAssgnPair where
  arbitrary = do
    Small n <- arbitrary
    assgn <- M.fromList <$> forM [0..n] (\i -> (Var i,) <$> arbitrary)
    Small (c :: Int) <- arbitrary
    fs <- forM [0..c] $ const $ genClause n
    return $ FAP (Formula fs) (Assgn assgn)

mkFormula :: [Map Var Bool] -> Formula
mkFormula fs
  | any null fs = Formula [M.empty]
  | otherwise   = Formula fs

genFormula :: Int -> Gen Formula
genFormula n = do
  Small (c :: Int) <- arbitrary
  mkFormula <$> forM [0..c] (const $ genClause n)

genAssignment :: Int -> Gen Assignment
genAssignment n =
  Assgn <$> (M.fromList <$> forM [0..n] (\i -> (Var i,) <$> arbitrary))

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

test_suite :: IO ()
test_suite = do
  quickCheck prop_conj
  quickCheck prop_disj

newtype M a = M { runM :: State Assignment a }
  deriving (Functor,Applicative,Monad)

assign :: Var -> Bool -> M ()
assign v b = M $ modify $ assignment %~ M.insert v b

satisfy :: Lit -> M ()
satisfy (Pos v) = assign v True
satisfy (Neg v) = assign v False

isUnitClause :: Map Var Bool -> Maybe Lit
isUnitClause clause
  | M.size clause == 1 = uncurry (flip mkLit) <$> M.lookupMin clause
  | otherwise = Nothing

varOccurrences :: Formula -> Map Var (Int, Int)
varOccurrences (Formula fs) =
  M.map (both %~ getSum) . M.unionsWith (<>) . map (M.map countOne) $ fs
  where
    countOne :: Bool -> (Sum Int, Sum Int)
    countOne True = (1, 0)
    countOne False = (0, 1)

-- in x /\ ... x is a unit clause
unitClausePropagation :: Formula -> M Formula
unitClausePropagation (Formula fs) = do
  fs' <- forM fs $ \clause ->
    case isUnitClause clause of
      Just l -> satisfy l >> return Nothing
      Nothing -> return $ Just clause
  return $ Formula $ catMaybes fs'

-- a pure literal is when a variable appears only as a positive literal or a negative literal
pureLitElimination :: Formula -> M Formula
pureLitElimination f@(Formula fs) = do
    M $ modify $ assignment %~ insertLit
    return $ Formula fs'
  where
    isPure (p, n) = p == 0 || n == 0
    pureLit = M.filter isPure $ varOccurrences f
    isPosLit (_, n) = n == 0
    insertLit m = M.map isPosLit pureLit `M.union` m
    fs' = filter (\c -> M.null (M.intersection c pureLit)) fs

instance Show a => Show (M a) where
  show (M a) = show (runState a (Assgn M.empty))


-- property base tests: running pureLitElimination gets us an
-- evaluation that is no less defined that before

-- (x ∨ y ∨ z) ∧ (x ∨ ¬ y ∨ z) ∧ (y ∨ ¬ z)
-- x := true



-- x ∧ (¬ x ∨ ¬ y ∨ z) ∧ (y ∨ ¬ z)
-- x := true
-- (¬ y ∨ z) ∧ (y ∨ ¬ z)
