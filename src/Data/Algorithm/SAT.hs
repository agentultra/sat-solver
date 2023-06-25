module Data.Algorithm.SAT where

import Control.Monad.State
import Lens.Micro
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Maybe

newtype Var = Var Int
  deriving (Eq, Ord)

data Lit = Pos Var | Neg Var

-- in conjunctive normal form:
--   a formula is a conjunction of clauses
--   a clause is disjunction of literals
--   a literal is a variable with or without negation
newtype Formula = Formula [Map Var Bool]

newtype Assignment = Assgn (Map Var Bool)

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
varOccurrences (Formula fs) = undefined

-- in x /\ ... x is a unit clause
unitClausePropagation :: Formula -> M Formula
unitClausePropagation (Formula fs) = do
  fs' <- forM fs $ \clause ->
    case isUnitClause clause of
      Just l -> satisfy l >> return Nothing
      Nothing -> return $ Just clause
  return $ Formula $ catMaybes fs'

pureLitElimination :: Formula -> M Formula
pureLitElimination (Formula fs) = undefined


-- (x ∨ y ∨ z) ∧ (x ∨ ¬ y ∨ z) ∧ (y ∨ ¬ z)
-- x := true



-- x ∧ (¬ x ∨ ¬ y ∨ z) ∧ (y ∨ ¬ z)
-- x := true
-- (¬ y ∨ z) ∧ (y ∨ ¬ z)
