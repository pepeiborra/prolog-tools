{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
{-# LANGUAGE DisambiguateRecordFields #-}

module Language.Prolog.Signature (PrologSignature(..), getPrologSignature) where

import Control.Monad
import Control.Monad.Free
import qualified Data.Foldable as F
import Data.Monoid
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Language.Prolog.Syntax
import TRS.Signature

deriving instance Ord VName

instance (Show id, Ord id) => HasSignature (Program' id var) id where
  getSignature cc = let aritiesP = Map.fromList [ (f, length tt) | Pred f tt   <- F.toList =<< cc]
                        aritiesF = Map.fromList [ (f, length tt) | Pred _ args <- F.toList =<< cc, Impure(Term f tt) <- subterms =<< args ]
                        functors = Map.keysSet aritiesF
                        preds    = Map.keysSet aritiesP
                        in Sig {constructorSymbols = functors, definedSymbols = preds, arity = aritiesP `mappend` aritiesF}

data PrologSignature idt idp = PrologSig {constructorSymbols :: Map idt Int, predicateSymbols :: Map idp Int } deriving (Eq,Show)

getPrologSignature cc =  PrologSig aritiesF aritiesP where
    aritiesP = Map.fromList [ (f, length tt) | Pred f tt   <- F.toList =<< cc]
    aritiesF = Map.fromList [ (f, length tt) | Pred _ args <- F.toList =<< cc, Impure(Term f tt) <- subterms =<< args ]