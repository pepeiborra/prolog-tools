{-# LANGUAGE StandaloneDeriving, TypeSynonymInstances, MultiParamTypeClasses #-}
module Language.Prolog.Signature (module TRS.Signature) where

import Control.Monad
import qualified Data.Foldable as F
import Data.Monoid
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Language.Prolog.Syntax
import TRS.Signature


deriving instance Ord VName

instance (Show id, Ord id) => HasSignature (Program id) id where
  getSignature cc = let aritiesP = Map.fromList [ (f, length tt) | Pred f tt   <- F.toList =<< cc]
                        aritiesF = Map.fromList [ (f, length tt) | Pred _ args <- F.toList =<< cc, Term f tt <- subterms =<< args ]
                        functors = Map.keysSet aritiesF
                        preds    = Map.keysSet aritiesP
                        subterms (In t) = t : (F.concatMap subterms t)
                        in Sig {constructorSymbols = functors, definedSymbols = preds, arity = aritiesP `mappend` aritiesF}