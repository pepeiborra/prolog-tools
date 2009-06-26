{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-overlapping-patterns #-}

module Language.Prolog.Representation where

import Control.Applicative (pure, Applicative(..), (<$>))
import Data.Bifunctor
import Data.Foldable
import Data.Monoid (Monoid(..))
import Data.Traversable
import Text.PrettyPrint as Ppr

import Data.AlaCarte
import Data.AlaCarte.Ppr
import Data.Term hiding (match)
import Data.Term.Ppr
import Data.Term.Simple
import Data.Term.Var

import qualified Language.Prolog.Syntax as Prolog
import Language.Prolog.Syntax (Program'', Term')
import Language.Prolog.Utils

-- | Representation Terms
type TermR  idt     = TermR' idt Var
type TermR' idt var = Term1 (Expr (PrologTerm idt)) (Either WildCard var)
type PrologTerm idt = PrologT :+: T idt :+: V

---representProgram :: Program'' idp (Term' idt var) -> Program'' idp (TermR' idt var)
representProgram :: (Monad m, PrologT :<: f, T idt :<: f) =>
                  (v -> m a)            -- ^ What to do with variables
               -> (Expr f -> [a] -> a)  -- ^ How to construct a term
               -> m a                   -- ^ How to fill a 'Prolog.Wildcard'
               -> Program'' idp (Term' idt v)
               -> m (Program'' idp a)
representProgram var term wc = mapM3 (foldTermM var
                                         (representTerm term wc))

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
--    f (Prolog.Term id tt) = return $ term (mkT id) tt
    f (Prolog.String s)   = return $ term (string s) []
    f  Prolog.Wildcard    = wildCard
    f (Prolog.Cons h t)   = return $ term cons [h,t]
    f (Prolog.Nil)        = return $ term nil []
    tsucc x = term psucc [x] ; tzero = term zero []

-- -------------------------
-- * Wildcards for variables
-- -------------------------

data WildCard = WildCard deriving (Enum, Eq, Ord, Bounded)
wildCard :: Monad m => m(Either WildCard var)
wildCard = return (Left WildCard)
instance Ppr WildCard           where ppr _ = text "_"

-- --------
-- * Term0
-- --------

data T id a   = T id deriving (Show, Eq, Ord)
type Term0 id = Free (T id)
term0 = Impure . T

mkT :: (T id :<: f) => id -> Expr f
mkT = inject . T
isT (match -> Just (T{})) = True; isT _ = False

instance Functor     (T id) where fmap      f (T id) = T id
instance Foldable    (T id) where foldMap   _ _      = mempty
instance Traversable (T id) where traverse  _ (T id) = pure (T id)
instance Bifunctor    T     where bimap fid _ (T id) = T (fid id)

instance Ppr id => Ppr  (T id a) where ppr  (T id) = ppr id
instance Ppr id => PprF (T id)   where pprF (T id) = ppr id

instance HasId (T id) id where getId (T id) = Just id

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
                deriving (Show, Eq, Ord)

tup, cons, nil, psucc, zero :: (PrologT :<: f) => Expr f
string :: (PrologT :<: f) => String -> Expr f

tup     = inject (K Tup)
cons    = inject (K Cons); nil = inject (K Nil)
string  = inject . K . String
psucc   = inject (K Succ)
zero    = inject (K Zero)

instance Ppr PrologT_ where
    ppr Tup = Ppr.empty
    ppr Zero = text "0"; ppr Succ = char 's'
    ppr Cons = text "cons"; ppr Nil = text "nil"
    ppr (String s) = quotes (text s)

type PrologP  = K PrologP_
data PrologP_ = Is | Eq deriving (Eq,Ord,Show)

is,eq :: (PrologP :<: f) => Expr f
is = inject (K Is)
eq = inject (K Eq)

instance Ppr PrologP_ where
    ppr Is = text "is"
    ppr Eq = text "eq"


-- ------------------------------
-- * Various abstract constructors
-- ------------------------------

-- Constructors for abstract values

-- | Any is the constructor for the distinguished domain object
--   any, the bottom of the domain. Every object in the concrete
--   language belongs to the any set.
data Any f = Any deriving (Eq, Ord, Show)

-- | A constructor Static to denote static things
data Static a = Static deriving (Eq, Ord, Show, Bounded)

-- | The framework introduces a distinguished object V in the abstract language
--   to model variables (no term evaluates to V).
data V a = V deriving (Eq,Ord)

-- | A constructor NotVar to denote nonvar things
data NotVar f = NotVar deriving (Eq, Ord, Show, Bounded)

-- | Compound is a recursive constructor to analyze the
--   instantiation level of a function symbol
data Compound f = Compound f [f] deriving (Show, Eq, Ord)

data FreeArg a = FreeArg deriving (Eq,Ord,Show)

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
instance PprF Compound    where pprF (Compound id dd) = ppr id <> parens (hcat $ punctuate comma $ map ppr dd)
instance PprF FreeArg     where pprF _ = text "free"

-- ** Constructors for abstract compilation

data Denotes idt a = Denotes idt deriving (Eq, Show, Ord)
data NotAny      a = NotAny      deriving (Eq, Show, Ord)
data Domain      a = Domain      deriving (Eq, Show, Ord)

domain  :: (Domain :<: f) => Expr f
notAny  :: (NotAny :<: f) => Expr f
denotes :: (Denotes idt :<: f) => idt -> Expr f

denotes = inject . Denotes
domain  = inject Domain
notAny  = inject NotAny


instance Functor (Denotes idt) where fmap _ (Denotes id) = Denotes id
instance Functor NotAny        where fmap _ NotAny       = NotAny
instance Functor Domain        where fmap _ Domain       = Domain

instance Ppr idt => PprF (Denotes idt) where pprF (Denotes id) = text "denotes_" <> ppr id
instance PprF Domain      where pprF Domain = text "domain"
instance PprF NotAny      where pprF NotAny = text "notAny"

-- --------
-- Origami
-- --------
newtype  K x a = K x deriving (Eq, Ord, Show)
instance Functor     (K x) where fmap _ (K x)     = K x
instance Foldable    (K x) where foldMap _ _      = mempty
instance Traversable (K x) where traverse _ (K x) = Control.Applicative.pure (K x)

instance Ppr x => Ppr  (K x a) where ppr  (K x) = ppr x
instance Ppr x => PprF (K x)   where pprF (K x) = ppr x
