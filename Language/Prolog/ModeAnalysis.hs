{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}

module Language.Prolog.ModeAnalysis where

import Language.Prolog.Syntax
import Data.List (concatMap,sort)
import Data.Maybe (fromMaybe)
import Data.Monoid
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

data Mode = Inp | Out deriving (Eq, Show)
type ModeAssignment id = Map id [Mode]

-- inferMode :: Program -> Ident -> Atom id -> ModeAssignment
isWellModded :: (Ord id, Show id) => ModeAssignment id -> Program id -> Bool
isWellModded env = all isWellModdedClause where
  isWellModdedClause (h :- cc) =
      varsm Out h `Set.isSubsetOf` mconcat (varsm Inp h : map (varsm Out) cc)

  varsm mod (Pred p tt) = Set.fromList $ concatMap vars
                            (select tt [i | (i,m) <- zip [0..] (modes p), m == mod])
  varsm mod Cut = mempty
  modes p = fromMaybe (error $ "isWellModded: environment is missing a mode assignment for " ++ show p)
                      (Map.lookup p env)


select :: (Ord t, Enum t, Num t) => [a] -> [t] -> [a]
select xx ii = go 0 xx (sort ii)
    where go _ [] _ = []
          go _ _ [] = []
          go n (x:xx) (i:ii) | n == i = x : go (succ n) xx ii
                             | otherwise = go (succ n) xx (i:ii)
