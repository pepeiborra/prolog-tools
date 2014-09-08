{-# LANGUAGE FlexibleContexts, FlexibleInstances, OverlappingInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveGeneric #-}
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}

module Language.Prolog.Representation where

import Control.Applicative (pure, Applicative(..), (<$>))
import Control.DeepSeq
import Control.Monad
import Control.Monad.Free
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Foldable (Foldable(..), toList)
import Data.List (find)
import Data.Maybe
import Data.Monoid (Monoid(..), getAny)
import qualified Data.Monoid as Monoid
import Data.Typeable
import Data.Traversable
import qualified Data.Set as Set
import Language.Haskell.TH (runIO)
import Text.ParserCombinators.Parsec (parse)
import Text.PrettyPrint.HughesPJClass as Ppr
import Prelude hiding (foldr)
import GHC.Generics (Generic,Generic1)

import Data.AlaCarte
import Data.AlaCarte.Ppr
import Data.Term (HasId(..), HasId1(..), Rename(..), foldTermM)
import qualified Data.Term as Family
import Data.Term.Rules
import Data.Term.Simple hiding (id)
import Data.Term.Var

import qualified Language.Prolog.Syntax as Prolog
import Language.Prolog.Parser (program)
import Language.Prolog.Syntax (Program'', Term', ClauseF(..),  GoalF(Pred, (:=:)), Program)
import Language.Prolog.Utils

-- | Representation Terms
type TermR  idt     = TermR' idt Var
type TermR' idt var = Term1 (Expr (PrologTerm idt)) (Either WildCard var)
type PrologTerm idt = PrologT :+: PrologP :+: T idt :+: V

---representProgram :: Program'' idp (Term' idt var) -> Program'' idp (TermR' idt var)
representProgram :: (Monad m, PrologT :<: f, PrologP :<: f, T idp :<: f, T idt :<: f) =>
                  (v -> m a)            -- ^ What to do with variables
               -> (Expr f -> [a] -> a)  -- ^ How to construct a term
               -> m a                   -- ^ How to fill a 'Prolog.Wildcard'
               -> Program'' idp (Term' idt v)
               -> m (Program'' (Expr f) a)
representProgram var term wc = mapM3 (foldTermM var
                                         (representTerm term wc))
                             . fmap2 representPred

--representProgram :: Program'' idp (Term' idt var) -> Program'' idp (TermR' idt var)
--representProgram = runIdentity . mapM3 (foldTermM (return2 . Right) (representTerm term1 (return wildCard)))

-- | Represent a Prolog Term in a different term structure using PrologT based ids
representTerm :: (Monad m, PrologT :<: f, T idt :<: f) =>
                  (Expr f -> [a] -> a)  -- ^ How to construct a term
               -> m a                   -- ^ How to fill a 'Prolog.Wildcard'
               -> Prolog.TermF idt a
               -> m a

representTerm term wildCard = f where
    f (Prolog.Int i)      = return $ iterate tsucc tzero !! fromInteger i
    f (Prolog.Tuple tt)   = return $ term tup tt
    f (Prolog.Term id tt) = return $ term (mkT id) tt
    f (Prolog.String s)   = return $ term (string s) []
    f  Prolog.Wildcard    = wildCard
    f (Prolog.Cons h t)   = return $ term cons [h,t]
    f (Prolog.Nil)        = return $ term nil []
    tsucc x = term psucc [x] ; tzero = term zero []

representPred :: (PrologP :<: f, T idp :<: f) => GoalF idp a -> GoalF (Expr f) a
representPred = f where
    f (Prolog.Pred id tt) = Prolog.Pred (mkT id) tt
    f (Prolog.Is x y)     = Prolog.Pred is [x,y]
    f  Prolog.Cut         = Prolog.Pred cut []
--    f (Prolog.Not p)      = Prolog.Pred notP [p]
    f (x Prolog.:=: y)    = Prolog.Pred eq [x,y]
--    f (Prolog.Ifte b t e) = Prolog.Pred ifte [b,t,e]
--    f (Prolog.Ift  b t)   = Prolog.Pred ifte [b,t]
    f p = error "representPred: negation and if-then-else not supported"
-- -------------------------
-- * Wildcards for variables
-- -------------------------

data WildCard = WildCard deriving (Enum, Eq, Ord, Bounded, Typeable,Generic)
wildCard :: Monad m => m(Either WildCard var)
wildCard = return (Left WildCard)
instance Pretty  WildCard where pPrint _  = text "_"
instance Show WildCard where show _ =  "_"
instance Rename WildCard where rename _ = id
instance NFData WildCard

-- --------
-- * Term0
-- --------

newtype T id a   = T id deriving (Show, Eq, Ord, Typeable,Generic,Generic1)
type Term0 id = Free (T id)
term0 = Impure . T

mkT :: (T id :<: f) => id -> Expr f
mkT = inject . T
isT :: forall id f. (T id :<: f) => Expr f -> Bool
isT (match -> Just (T{} :: T id (Expr f))) = True; isT _ = False

instance Functor     (T id) where fmap      f (T id) = T id
instance Foldable    (T id) where foldMap   _ _      = mempty
instance Traversable (T id) where traverse  _ (T id) = pure (T id)
instance Bifunctor     T    where bimap     f _ (T id) = T (f id)
instance Bifoldable    T    where bifoldMap f _ (T id) = f id
instance Bitraversable T    where bitraverse fid _ (T id) = T <$> fid id

instance Pretty id => Pretty  (T id a) where pPrint  (T id) = pPrint id
instance Pretty id => PprF (T id)   where pprF (T id) = pPrint id
instance Pretty  (T String a) where pPrint  (T id) = text id
instance PprF    (T String)   where pprF    (T id) = text id

instance NFData id => NFData (T id a) where rnf (T id) = rnf id

type instance Family.Id (T id) = id

instance Ord id => HasId1 (T id) where
  getId1 (T id) = Just id

-- -------
-- * Term1
-- -------
-- Term1 is just Data.Term.Simple.Term1

term1 :: id -> [Term1 id a] -> Term1 id a
term1 = Data.Term.Simple.term

-- -------------------------------
-- * Built-in things
-- -------------------------------
type PrologT = K PrologT_
data PrologT_ = Zero | Succ | Tup | Cons | Nil | String String
                deriving (Show, Eq, Ord, Typeable, Generic)

instance NFData PrologT_ where
  rnf (String s) = rnf s
  rnf x = ()

tup, cons, nil, psucc, zero :: (PrologT :<: f) => Expr f
string :: (PrologT :<: f) => String -> Expr f

tup     = inject (K Tup)
cons    = inject (K Cons); nil = inject (K Nil)
string  = inject . K . String
psucc   = inject (K Succ)
zero    = inject (K Zero)

instance Pretty PrologT_ where
    pPrint Tup = text "tuple"
    pPrint Zero = text "0"; pPrint Succ = char 's'
    pPrint Cons = text "cons"; pPrint Nil = text "nil"
    pPrint (String s) = quotes (text s)

type PrologP  = K PrologP_
data PrologP_ = Is | Eq | Cut | Not | Ifte deriving (Eq,Ord,Show,Typeable,Generic)

instance NFData PrologP_

is,eq,cut,notP,ifte :: (PrologP :<: f) => Expr f
is  = inject (K Is)
eq  = inject (K Eq)
cut = inject (K Cut)
ifte= inject (K Ifte)
notP= inject (K Not)

instance Pretty PrologP_ where
    pPrint Is = text "is"
    pPrint Eq = text "eq"
    pPrint Cut = text "!"
    pPrint Ifte = text "ifte"
    pPrint Not = text "/+"

-- ------------------------------
-- * Various abstract constructors
-- ------------------------------

-- Constructors for abstract values

-- | Any is the constructor for the distinguished domain object
--   any, the bottom of the domain. Every object in the concrete
--   language belongs to the any set.
data Any f = Any deriving (Eq, Ord, Show,Typeable,Generic,Generic1)

-- | A constructor Static to denote static things
data Static a = Static deriving (Eq, Ord, Show, Bounded,Typeable,Generic,Generic1)

-- | The framework introduces a distinguished object V in the abstract language
--   to model variables (no term evaluates to V).
data V a = V deriving (Eq,Ord,Typeable,Generic,Generic1)

-- | A constructor NotVar to denote nonvar things
data NotVar f = NotVar deriving (Eq, Ord, Show, Bounded,Typeable,Generic,Generic1)

-- | Compound is a recursive constructor to analyze the
--   instantiation level of a function symbol
data Compound f = Compound f [f] deriving (Show, Eq, Ord,Typeable,Generic,Generic1)

data FreeArg a = FreeArg deriving (Eq,Ord,Show,Typeable,Generic,Generic1)

any      :: (Any :<: f) => Expr f
notvar   :: (NotVar :<: f) => Expr f
static   :: (Static :<: f) => Expr f
freeArg  :: (FreeArg :<: f) => Expr f
mkV      :: (V :<: f)      => Expr f
compound :: (Compound :<: f) => Expr f -> [Expr f] -> Expr f

any         = inject Any
notvar      = inject NotVar
static      = inject Static
compound id = inject . Compound id
freeArg     = inject FreeArg; isFree (match -> Just FreeArg) = True; isFree _ = False
mkV         = inject V

isV      (match -> Just V)        = True ; isV _ = False
isAny    (match -> Just Any)      = True ; isAny _    = False
isNotvar (match -> Just NotVar{}) = True ; isNotvar _ = False
isStatic (match -> Just Static{}) = True ; isStatic _ = False
isCompound (match -> Just Compound{}) = True ; isCompound _ = False

instance Functor Any      where fmap _ Any    = Any
instance Functor NotVar   where fmap _ NotVar = NotVar
instance Functor Static   where fmap _  _     = Static
instance Functor Compound where fmap f (Compound id tt) = Compound (f id) (fmap f tt)
instance Functor V        where fmap _ V      = V
instance Functor FreeArg  where fmap f _      = FreeArg

instance Foldable Any      where foldMap _ Any    = mempty
instance Foldable NotVar   where foldMap _ NotVar = mempty
instance Foldable Static   where foldMap _  _     = mempty
instance Foldable Compound where foldMap f (Compound id tt) = f id `mappend` foldMap f tt
instance Foldable V        where foldMap _ V      = mempty
instance Foldable FreeArg  where foldMap f _      = mempty

instance Traversable Any      where traverse _ Any    = pure Any
instance Traversable NotVar   where traverse _ NotVar = pure NotVar
instance Traversable Static   where traverse _  _     = pure Static
instance Traversable Compound where traverse f (Compound id tt) =  Compound <$> f id <*> traverse f tt
instance Traversable V        where traverse _ V      = pure V
instance Traversable FreeArg  where traverse f _      = pure FreeArg


instance PprF Any         where pprF _ = text "any"
instance PprF V           where pprF _ = text "V"
instance PprF NotVar      where pprF _ = text "notvar"
instance PprF Static      where pprF _ = text "static"
instance PprF Compound    where
    pprF (Compound id []) = id
    pprF (Compound id dd) = id <> parens (hcat $ punctuate comma dd)
instance PprF FreeArg     where pprF _ = text "free"

instance NFData (Any a)
instance NFData (NotVar a)
instance NFData (Static a)
instance NFData a => NFData (Compound a) where rnf (Compound id tt) = rnf id `seq` rnf tt
instance NFData (V a)
instance NFData (FreeArg a)

-- ** Constructors for abstract compilation

data AbstractCompile a = Denotes a | Domain
   deriving (Eq, Show, Ord, Typeable,Generic)

data NotAny a = NotAny deriving (Eq, Show, Ord,Typeable,Generic)

domain  :: (AbstractCompile :<: f) => Expr f
notAny  :: (NotAny :<: f) => Expr f
denotes :: (AbstractCompile :<: f) => Expr f -> Expr f

denotes = inject . Denotes
domain  = inject Domain
notAny  = inject NotAny

isNotAny (match -> Just NotAny) = True; isNotAny _ = False
isDenotes(match -> Just Denotes{}) = True; isDenotes _ = False

instance Functor NotAny     where fmap _ NotAny     = NotAny
instance Foldable NotAny    where foldMap _ _       = mempty
instance Traversable NotAny where traverse _ NotAny = pure NotAny

instance PprF NotAny where pprF NotAny = text "notAny"

-- --------
-- Origami
-- --------
newtype  K x a = K x deriving (Eq, Ord, Show,Typeable,Generic, Generic1, NFData)
instance Functor     (K x) where fmap _ (K x)     = K x
instance Foldable    (K x) where foldMap _ _      = mempty
instance Traversable (K x) where traverse _ (K x) = Control.Applicative.pure (K x)

instance Pretty x => Pretty  (K x a) where pPrint  (K x) = pPrint x
instance Pretty x => PprF (K x)   where pprF (K x) = pPrint x

-- ------------------------------
-- Defaults and built-ins
-- ------------------------------

Right preludePl = $(do pgm <- runIO (readFile "prelude.pl")
                       case parse program "prelude.pl" pgm of -- parse just for compile time checking
                         Left err  -> error (show err)
                         Right _ -> [| fromRight <$$> parse program "prelude.pl" pgm|]
                   )                 -- actual parsing ^^ happens (again) at run time.
                                     -- I am too lazy to write the required LiftTH instances.
  where fromRight (Right a) = a

preludePreds = Set.fromList [ f | Pred f _ :- _ <- preludePl]

addBuiltInPredicates :: Functor f => [ClauseF (GoalF id (Free f Var))] -> [ClauseF (GoalF id (Free f Var))]
addBuiltInPredicates = insertEqual . insertIs
  where  insertEqual       cc = if getAny $ foldMap2 (Monoid.Any . isEqual) cc then eqclause `mappend` cc else cc
         insertIs          cc = if getAny $ foldMap2 (Monoid.Any . isIs)    cc then isclause `mappend` cc else cc

         eqclause = let x = Prolog.var "X" in [x :=: x       :- []]
         isclause = let x = Prolog.var "X" in [Prolog.Is x x :- []]
         isEqual (_ :=: _) = True; isEqual _ = False
         isIs Prolog.Is{} = True; isIs _ = False

addMissingPredicates :: Program String -> Program String
addMissingPredicates cc0
  | Set.null undefined_cc0 = cc0
  | otherwise = (insertDummy . insertPrelude) cc0

   where undefined_cc0 = undefinedPreds cc0
         undefinedPreds :: Program String -> Set.Set String
         undefinedPreds    cc = Set.fromList [ f | f <- toList (getDefinedSymbols cc `Set.difference` definedPredicates cc)]
         definedPredicates cc = Set.fromList [ f | Pred f _ :- _ <- cc]

         insertPrelude cc = if not (Set.null (Set.intersection (undefinedPreds cc) preludePreds)) then cc' `mappend` cc else cc
           where cc' = foldr renamePred (cc `mappend` preludePl) (toList repeatedIdentifiers)
                 repeatedIdentifiers = preludePreds `Set.intersection` definedPredicates cc0
         insertDummy cc =  [ Pred f (take (getArity cc f) vars) :- [] | f <- toList (undefinedPreds cc)] ++ cc

         renamePred f = fmap2 (rename (findFreeSymbol cc0 f))
           where rename f' (Pred f tt) | f == f' = Pred f' tt
                 rename _ x = x

         vars = [Prolog.var ("X" ++ show i) | i <- [0..]]

         findFreeSymbol sig pre = fromJust $ find (`Set.notMember` getAllSymbols sig) (pre : [pre ++ show i | i <- [0::Int ..]])

-- --------------------
-- Deriving boilerplate
-- --------------------
#ifdef DERIVE
$(derive makeFunctor     ''AbstractCompile)
$(derive makeFoldable    ''AbstractCompile)
$(derive makeTraversable ''AbstractCompile)
#else
deriving instance Functor AbstractCompile
deriving instance Foldable AbstractCompile
deriving instance Traversable AbstractCompile
#endif

instance PprF AbstractCompile where
    pprF (Denotes id) = text "denotes_" <> id
    pprF Domain       = text "domain"
