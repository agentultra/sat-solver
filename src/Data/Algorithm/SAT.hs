module Data.Algorithm.SAT where

import Data.Map as M

newtype Var = Var Int
  deriving (Eq, Ord)

newtype Formula = Formula [[Var]]

newtype Assignment = Assgn (Map Var Bool)

fetch :: Assignment -> Var -> Maybe Bool
fetch (Assgn m) v = v `M.lookup` m

eval :: Assignment -> Formula -> Maybe Bool
eval asgn (Formula fs) = and <$> mapM (fmap or . mapM (fetch asgn)) fs
