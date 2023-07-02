{-# LANGUAGE TemplateHaskell #-}

module Data.Algorithm.SAT where

import Control.Applicative
import Control.Monad.State
import qualified Data.List as L
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe
import Data.Monoid
import Lens.Micro
import Lens.Micro.Mtl hiding (assign)
import Lens.Micro.TH
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

data SolverState
  = SolverState
  { _assignments :: Assignment
  , _guesses :: Int
  , _simplifications :: Int
  }
  deriving Show

makeLenses ''SolverState

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
test (Assgn m) v p = fmap (== p) . M.lookup v $ m

eval :: Assignment -> Formula -> Maybe Bool
eval asgn (Formula fs) = and <$> mapM (fmap or . M.traverseWithKey (test asgn)) fs

-- Evaluate formula on partial assignment and returns false if the assignment
-- cannot guarantee that the formula evaluates to true
evalPartial :: Assignment -> Formula -> Bool
evalPartial asgn (Formula fs) =
  and $ map (or . M.map (fromMaybe False) . M.mapWithKey (test asgn)) fs

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

genAssignmentFor :: Formula -> Gen Assignment
genAssignmentFor f = do
  vals <- forM (freeVars f) $ \v -> (v,) <$> arbitrary
  return $ Assgn $ M.fromList vals

initSolverState :: SolverState
initSolverState
  = SolverState
  { _assignments = Assgn M.empty
  -- , _stack = mempty
  }

newtype Solver a = Solver { getSolver :: StateT SolverState Maybe a }
  deriving ( Functor
           , Applicative
           , Alternative
           , Monad
           , MonadState SolverState
           )

runSolver :: Solver a -> Maybe (a, Assignment)
runSolver solver = runStateT (getSolver solver) initSolverState & mapped._2 %~ _assignments

runSolver' :: Solver a -> (a, Assignment)
runSolver' = fromJust . runSolver

assign :: Var -> Bool -> Solver ()
assign v b = assignments %= (assignment %~ M.insert v b)

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

freeVars :: Formula -> [Var]
freeVars = M.keys . varOccurrences

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
  (Assgn asgn) <- use assignments
  assignments .= Assgn M.empty
  Formula f <- m
  a'@(Assgn asgn') <- use assignments
  assignments .= Assgn (asgn' `M.union` asgn)
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
    assignments %= (assignment %~ insertLit)
    return $ Formula fs'
  where
    isPure (p, n) = p == 0 || n == 0
    pureLit = M.filter isPure $ varOccurrences f
    isPosLit (_, n) = n == 0
    insertLit m = M.map isPosLit pureLit `M.union` m
    fs' = filter (\c -> M.null (M.intersection c pureLit)) fs

instance Show a => Show (Solver a) where
  show (Solver a) = show (runStateT a initSolverState)

progress :: Solver a -> Solver (a, Bool)
progress (Solver m) = Solver $ do
  Assgn sigma  <- use assignments
  r <- m
  Assgn sigma' <- use assignments
  return (r, M.size sigma /= M.size sigma')

assigned :: Assignment -> Var -> Bool
assigned (Assgn m) v = v `M.member` m

failIfUnsat :: Maybe Formula -> Solver (Maybe Formula)
failIfUnsat x = Nothing <$ guard (isNothing x)

true :: Formula
true = Formula []
false :: Formula
false = Formula [M.empty]

solve' :: Formula -> [Var] -> Solver (Maybe Formula)
solve' f vs =
  if f == true then return Nothing
    else if f == false then return (Just f)
    else do
      simplifications += 1
      (f', b) <- progress $ unitClausePropagation f >>= pureLitElimination
      if b
        then solve' f' vs
        else do
          sigma <- use assignments
          case dropWhile (assigned sigma) vs of
            [] -> return $ Just f'
            v : vs' -> do
              guesses += 1
              (assign v True >> (failIfUnsat =<< solve' f' vs')) <|>
                (assign v False >> (failIfUnsat =<< solve' f' vs')) <|>
                return (Just f')

-- Given a formula `f`, try to find a true value assignment to the
-- variables it contains so that `f` will evaluate to true
solve :: Formula -> Solver (Maybe Formula)
solve f = solve' f (freeVars f)
