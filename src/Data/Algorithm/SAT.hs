module Data.Algorithm.SAT where

import Control.Monad.State
import Control.Lens
import Data.Map as M
import Data.Maybe

newtype Var = Var Int
  deriving (Eq, Ord)

data Lit = Pos Var | Neg Var

-- in conjunctive normal form:
--   a formula is a conjunction of clauses
--   a clause is disjunction of literals
--   a literal is a variable with or without negation
data Formula = Formula [[Lit]]

newtype Assignment = Assgn (Map Var Bool)

assignment :: Lens' Assignment (Map Var Bool)
assignment f (Assgn m) = Assgn <$> f m

test :: Assignment -> Lit -> Maybe Bool
test (Assgn m) (Pos v) = v `M.lookup` m
test (Assgn m) (Neg v) = not <$> v `M.lookup` m

eval :: Assignment -> Formula -> Maybe Bool
eval asgn (Formula fs) = and <$> mapM (fmap or . mapM (test asgn)) fs

newtype M a = M { runM :: State Assignment a }
  deriving (Functor,Applicative,Monad)

assign :: Var -> Bool -> M ()
assign v b = M $ modify $ assignment %~ insert v b

satisfy :: Lit -> M ()
satisfy (Pos v) = assign v True
satisfy (Neg v) = assign v False

isUnitClause :: [Lit] -> Maybe Lit
isUnitClause [l] = Just l
isUnitClause _ = Nothing

varOccurrences :: Formula -> Map Var (Int, Int)
varOccurrences (Formula fs) = _


-- in x /\ ... x is a unit clause
unitClausePropagation :: Formula -> M Formula
unitClausePropagation (Formula fs) = do
  fs' <- forM fs $ \clause ->
    case isUnitClause clause of
      Just l -> satisfy l >> return Nothing
      Nothing -> return $ Just clause
  return $ Formula $ catMaybes fs'

pureLitElimination :: Formula -> M Formula
pureLitElimination (Formula fs) = _


-- (x ∨ y ∨ z) ∧ (x ∨ ¬ y ∨ z) ∧ (y ∨ ¬ z)
-- x := true



-- x ∧ (¬ x ∨ ¬ y ∨ z) ∧ (y ∨ ¬ z)
-- x := true
-- (¬ y ∨ z) ∧ (y ∨ ¬ z)
