module Data.Algorithm.SAT where

import Control.Monad.State
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Maybe
import Data.Monoid
import Lens.Micro

newtype Var = Var Int
  deriving (Eq, Ord, Show)

data Lit = Pos Var | Neg Var

-- in conjunctive normal form:
--   a formula is a conjunction of clauses
--   a clause is disjunction of literals
--   a literal is a variable with or without negation
newtype Formula = Formula [Map Var Bool]
  deriving Show

newtype Assignment = Assgn (Map Var Bool)
  deriving Show

assignment :: Lens' Assignment (Map Var Bool)
assignment f (Assgn m) = Assgn <$> f m

test :: Assignment -> Var -> Bool -> Maybe Bool
test (Assgn m) v p = fmap (/= p) . M.lookup v $ m

eval :: Assignment -> Formula -> Maybe Bool
eval asgn (Formula fs) = and <$> mapM (fmap or . M.traverseWithKey (test asgn)) fs

newtype M a = M { runM :: State Assignment a }
  deriving (Functor,Applicative,Monad)

assign :: Var -> Bool -> M ()
assign v b = M $ modify $ assignment %~ M.insert v b

satisfy :: Lit -> M ()
satisfy (Pos v) = assign v True
satisfy (Neg v) = assign v False

isUnitClause :: Map Var Bool -> Maybe Lit
isUnitClause clause
  | M.size clause == 1 = uncurry mkLit <$> M.lookupMin clause
  | otherwise = Nothing
  where
    mkLit :: Var -> Bool -> Lit
    mkLit v True = Pos v
    mkLit v False = Neg v

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
