module Data.Algorithm.SAT where

import Control.Monad.State
import qualified Data.List as L
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

fromLit :: Lit -> (Var, Bool)
fromLit (Pos v) = (v, True)
fromLit (Neg v) = (v, False)

-- in conjunctive normal form:
--   a formula is a conjunction of clauses
--   a clause is disjunction of literals
--   a literal is a variable with or without negation
newtype Formula = Formula { getClauses :: [Map Var Bool] }
  deriving (Eq, Ord)

newtype Assignment = Assgn (Map Var Bool)
  deriving Show

showClause :: Map Var Bool -> String
showClause fs
  | null fs = "false"
  | otherwise = L.intercalate " ∨ " [ show (mkLit sign v) | (v,sign) <- M.toList fs ]

instance Show Formula where
  show (Formula fs)
    | null fs   = "true"
    | otherwise = L.intercalate " ∧ " $ map (\c -> "(" ++ showClause c ++ ")") fs

assignment :: Lens' Assignment (Map Var Bool)
assignment f (Assgn m) = Assgn <$> f m

test :: Assignment -> Var -> Bool -> Maybe Bool
test (Assgn m) v p = fmap (/= p) . M.lookup v $ m

eval :: Assignment -> Formula -> Maybe Bool
eval asgn (Formula fs) = and <$> mapM (fmap or . M.traverseWithKey (test asgn)) fs

conj :: Formula -> Formula -> Formula
conj (Formula xs) (Formula ys) = mkFormula $ xs ++ ys

disjClause :: Map Var Bool -> Map Var Bool -> Maybe (Map Var Bool)
disjClause mx my = do
  let mz = M.mergeWithKey (\_k x y -> guard (x /= y))
            (const M.empty) (const M.empty) mx my
  let mz' = mx `M.union` my
  guard (M.null mz || M.null mx || M.null my)
  return mz'

disj :: Formula -> Formula -> Formula
disj (Formula xs) (Formula ys) =
  Formula $ Ord.nubSort $ catMaybes [ disjClause x y | x <- xs, y <- ys ]

data FmlAssgnPair = FAP Formula Assignment

genClause :: Int -> Gen (Map Var Bool)
genClause n = do
  l <- forM [0..n] (\i ->
    fmap (Var i,) <$> arbitrary)
  return $ M.fromList $ catMaybes l

fromListLit :: [[Lit]] -> Formula
fromListLit xs = mkFormula $ M.fromList . map fromLit <$> xs

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

newtype Solver a = Solver { getSolver :: State Assignment a }
  deriving (Functor,Applicative,Monad)

runSolver :: Solver a -> (a, Assignment)
runSolver m = runState (getSolver m) (Assgn M.empty)

assign :: Var -> Bool -> Solver ()
assign v b = Solver $ modify $ assignment %~ M.insert v b

satisfy :: Lit -> Solver ()
satisfy (Pos v) = assign v True
satisfy (Neg v) = assign v False

isUnitClause :: Map Var Bool -> Maybe Lit
isUnitClause clause
  | M.size clause == 1 = uncurry (flip mkLit) <$> M.lookupMin clause
  | otherwise          = Nothing

varOccurrences :: Formula -> Map Var (Int, Int)
varOccurrences (Formula fs) =
  M.map (both %~ getSum) . M.unionsWith (<>) . map (M.map countOne) $ fs
  where
    countOne :: Bool -> (Sum Int, Sum Int)
    countOne True  = (1, 0)
    countOne False = (0, 1)

hasTrueLit :: Assignment -> Map Var Bool -> Bool
hasTrueLit (Assgn a) cl =
  not $ M.null $
    M.filter id $
    M.intersectionWith (==) a cl

pruneFalseLit :: Assignment -> Formula -> Formula
pruneFalseLit (Assgn asgn) (Formula f) =
  mkFormula $
    Ord.nubSort $
    map (\c ->
           M.differenceWith
              (\b b' -> b <$ guard (b == b'))
              c asgn) f

-- run a function that updates the assignment and returns a formula
-- and use the new assignments to simplify the resulting formula
updateAssignment :: Solver Formula -> Solver Formula
updateAssignment (Solver m) = Solver $ do
  (Assgn asgn) <- get
  put (Assgn M.empty)
  Formula f <- m
  a'@(Assgn asgn') <- get
  put (Assgn $ asgn' `M.union` asgn)
  let f' = filter (not . hasTrueLit a') f
  return $ pruneFalseLit a' (Formula f')

-- in x /\ ... x is a unit clause
unitClausePropagation :: Formula -> Solver Formula
unitClausePropagation (Formula fs) = updateAssignment $ do
  fs' <- forM fs $ \clause ->
    case isUnitClause clause of
      Just l -> satisfy l >> return Nothing
      Nothing -> return $ Just clause
  return $ Formula $ catMaybes fs'

-- a pure literal is when a variable appears only as a positive literal or a negative literal
pureLitElimination :: Formula -> Solver Formula
pureLitElimination f@(Formula fs) = updateAssignment $ do
    Solver $ modify $ assignment %~ insertLit
    return $ Formula fs'
  where
    isPure (p, n) = p == 0 || n == 0
    pureLit = M.filter isPure $ varOccurrences f
    isPosLit (_, n) = n == 0
    insertLit m = M.map isPosLit pureLit `M.union` m
    fs' = filter (\c -> M.null (M.intersection c pureLit)) fs

instance Show a => Show (Solver a) where
  show (Solver a) = show (runState a (Assgn M.empty))
