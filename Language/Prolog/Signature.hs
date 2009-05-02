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

data PrologSignature idp idt = PrologSig {constructorSymbols :: Map idt Int, predicateSymbols :: Map idp Int } deriving (Eq,Show)

getPrologSignature :: (Ord idp, Ord idt) => Program'' idp (Term' idt var) -> PrologSignature idp idt
getPrologSignature cc =  PrologSig aritiesF aritiesP where
    aritiesP = Map.fromList [ (f, length tt) | Pred f tt   <- F.toList =<< cc]
    aritiesF = Map.fromList [ (f, length tt) | Pred _ args <- F.toList =<< cc, Impure(Term f tt) <- subterms =<< args ]

getPrologSignature' :: (Ord idp, Ord idt, term ~ Free (termF idt) var, Foldable (termF idt)) =>
                       (forall idt a . termF idt a -> Maybe idt) -- ^ A function to open a term
                    -> Program'' idp term                               -- ^ The program
                    -> PrologSignature idp idt
getPrologSignature' getId cc =  PrologSig aritiesF aritiesP where
    aritiesP = Map.fromList [ (f, length tt) | Pred f tt   <- F.toList =<< cc]
    aritiesF = Map.fromList [ (f, length $ toList t) | Pred _ args <- F.toList =<< cc, Impure t <- subterms =<< args, Just f <- [getId t]]