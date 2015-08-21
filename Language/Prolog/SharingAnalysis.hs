{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, StandaloneDeriving #-}

module Language.Prolog.SharingAnalysis where

import Control.Applicative
import Control.Arrow
import Control.Monad.Free
import Control.Monad.State
import Language.Prolog.Syntax
import qualified Data.Foldable as F
import Data.List (span)
import Data.Monoid
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Term.Var

import Language.Prolog.Signature ()
import Data.Term.Rules

import qualified Prelude as P
import Prelude hiding (concatMap,mapM_)

#ifdef DEBUG
import Debug.Trace
#else
trace _ = id
#endif

type Type id = (id,Int)
type SharingAssignment id = [Set (Type id)]

infer :: (Ord id, Pretty id) => Program id -> SharingAssignment id
infer pgm = map fromClass $ fst $ execState (mapM_ typeclause pgm) (a0,mempty) where
   sig = getSignature pgm
   a0  = [ Class(Set.singleton (f,i)) | (f,ar) <- Map.toList (getArities sig)
                                      , let j = if f `Set.member` getConstructorSymbols sig then 0 else 1
                                      , i <- [j..ar]]
   typeclause (l:-r)    = typePred l >> mapM_ typePred r >> modify (second (const mempty))
   typePred (Pred f tt) = sequence_ [typeTerm t (f,i) | (t,i) <- tt `zip` [1..]]
   typePred _ = return ()
   typeTerm (Pure var) typ = do
     val <- readVar var
     case val of
       Nothing   -> bindVar var typ
       Just typ' -> mergeM typ typ'
   typeTerm (Impure t) typ = f t typ where
    f (Term f tt) typ = mergeM typ (f,0) >> sequence_ [typeTerm t (f,i) | (t,i) <- tt `zip` [1..]]
    f (Int _)     typ = typeTerm (return $ VName "hi1337TypeofInts") typ -- Yes I know, I'm gonna burn in hell...
    f (Float _)   typ = typeTerm (return $ VName "hi1337TypeofDoubles") typ
    f _ _ = return ()

   mergeM typ1 typ2 = modify (first (merge typ1 typ2))
--                      >> get >>= \(cc,_) -> trace (showPpr typ1 ++ " ~ " ++ showPpr typ2 ++ " : " ++ showPpr (map F.toList cc)) (return ())
   readVar v        = do {(_,e) <- get; return (Map.lookup v e)}
   bindVar v t      = modify $ second (Map.insert v t)

-- -----------------------------------------------------
-- Equivalence Classes
-- -----------------------------------------------------
-- (these operators are described in e.g. Baader&Nipkow)
-- I did it the funcional way. There is room for improving efficiency by using references

newtype Class a = Class {fromClass::Set a} deriving (Show, Eq, F.Foldable)

find :: Ord a => a -> [Class a] -> Maybe (Class a, [Class a])
find a cc | (rest1, (it:rest2)) <- span (Set.notMember a . fromClass) cc = Just (it,rest1 ++ rest2)
find _ _ = Nothing

merge :: Ord a => a -> a -> [Class a] -> [Class a]
merge a b cc
  | a /= b
  , Just (Class c1,cc1) <- find a cc
  , Just (Class c2,cc2) <- find b cc1
  = Class (Set.union c1 c2) : cc2
merge _ _ cc = cc
