{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE Rank2Types, TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE DisambiguateRecordFields #-}

module Language.Prolog.Signature (PrologSignature(..), getPrologSignature, getPrologSignature') where

import Control.Monad
import Control.Monad.Free
import Data.Foldable (Foldable, toList)
import qualified Data.Foldable as F
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Term
import Data.Term.Rules
import Language.Prolog.Syntax

data PrologSignature idp idt = PrologSig {constructorSymbols :: Map idt (Set Int), predicateSymbols :: Map idp (Set Int) } deriving (Eq,Show)

getPrologSignature :: (Ord idp, Ord idt) => Program'' idp (Term' idt var) -> PrologSignature idp idt
getPrologSignature cc =  PrologSig aritiesF aritiesP where
    aritiesP = Map.fromListWith mappend [ (f, Set.singleton (length tt)) | Pred f tt   <- F.toList =<< cc]
    aritiesF = Map.fromListWith mappend [ (f, Set.singleton (length tt)) | Pred _ args <- F.toList =<< cc, Impure(Term f tt) <- subterms =<< args ]

getPrologSignature' :: (Ord idp, Ord idt, term ~ Free (termF idt) var, Foldable (termF idt)) =>
                       (forall idt a . termF idt a -> Maybe idt) -- ^ A function to open a term
                    -> Program'' idp term                               -- ^ The program
                    -> PrologSignature idp idt
getPrologSignature' getId cc =  PrologSig aritiesF aritiesP where
    aritiesP = Map.fromListWith mappend [ (f, Set.singleton(length tt)) | Pred f tt   <- F.toList =<< cc]
    aritiesF = Map.fromListWith mappend [ (f, Set.singleton(length $ toList t)) | Pred _ args <- F.toList =<< cc, Impure t <- subterms =<< args, Just f <- [getId t]]