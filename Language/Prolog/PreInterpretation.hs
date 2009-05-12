{-# LANGUAGE CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances, FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- | Abstract Analyses based on Preinterpretations
     * /Abstract domains based on regular types/ John Gallagher, K Henriksen.
       <http://www.springerlink.com/index/QBXV0L2QCU2UNEG4.pdf>
     * /Practical model-based static analysis for definite logic programs/ J Gallagher, D Boulanger, H Saglam.
       <http://www.cs.bris.ac.uk/Publications/Papers/1000067.pdf>
     * /Techniques for scaling up analyses based on pre-interpretations/ John Gallagher, K Henriksen, G Banda.
       <http://www.springerlink.com/index/eewwefchqru48rq4.pdf>
-}

module Language.Prolog.PreInterpretation where

import Control.Applicative
import Control.Monad (replicateM, liftM, join)
import Control.Monad.Free (Free(..), mapFree, foldFree, evalFree)
import Control.Monad.State (MonadState(..), modify, StateT, evalState, evalStateT, lift)
import Control.Monad.Writer (MonadWriter(..),WriterT, runWriterT)
import Data.AlaCarte
import Data.Foldable (foldMap, toList, Foldable)
import qualified Data.Foldable as F
import Data.List ((\\))
import Data.Monoid (Monoid(..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Traversable as T
import Data.Traversable (Traversable(..))
import Language.Prolog.Semantics (MonadFresh(..))
import Language.Prolog.Syntax hiding (Cons, Nil, Wildcard, String, cons, nil, wildcard, string)
import qualified Language.Prolog.Syntax as Prolog
import Language.Prolog.Signature
import Text.PrettyPrint
import Prelude hiding (id, any, succ, pred)
import qualified Prelude

-- Types
-- -----
type TermC  idt     = TermC' idt (Either WildCard VName)
type TermC' idt var = Term1 (Expr (PrologTerm idt)) var

type PrologTerm idt = PrologT :+: T idt

type DatalogTerm  d  = Term0 d (Either WildCard VName)
type DatalogTerm' f  = DatalogTerm (ObjectSet f)
type DatalogProgram idp idt = [ClauseF (GoalF idp (DatalogTerm idt)) ]
type AbstractDatalogProgram  idp idt d = Program'' (AbstractPred idp (Expr(PrologTerm idt))) (DatalogTerm  d)
type AbstractDatalogProgram' idp idt d = Program'' (AbstractPred idp (Expr(PrologTerm idt))) (DatalogTerm' d)

-- | The domain of a disjoint preinterpretation is composed by sets of objects.
--   Domain objects are modeled with open datatypes.
type Domain d = Set d
type Object d = (Expr d)
type ObjectSet d = Set(Expr d)

-- | Any is the constructor for the distinguished domain object
--   any, the bottom of the domain. Every object in the concrete
--   language belongs to the any set.
data Any f = Any deriving (Eq, Ord, Show)
any = inject Any; isAny (match -> Just Any) = True ; isAny _ = False

-- | A constructor to denote non var things
data NotVar f = NotVar deriving (Eq, Ord, Show, Bounded)
notvar = inject NotVar
isNotVar (match -> Just NotVar) = True ; isNotVar _ = False

-- | Compound is a recursive constructor to analyze the
--   instantiation level of a function symbol
data Compound f = Compound f [f] deriving (Show, Eq, Ord)
compound id = inject . Compound id

-- ----------------------
-- Abstract Compilation
-- ----------------------
data PrologT a = Zero | Succ | Tup | Cons | Nil | String String deriving (Show, Eq, Ord)
data T id a = T {id0::id} deriving (Show, Eq, Ord)
tup = inject Tup
mkT = inject . T
cons = inject Cons; nil = inject Nil
succ x = term1 (inject Succ) [x] ; zero = term1 (inject Zero) []
string = inject . String

getPrologSignature1 = getPrologSignature' (Just . id1)

type Term1 id    = Free (Term1F id)
data Term1F id a = Term1 {id1::id, tt1::[a]} deriving (Eq, Ord, Show)
term1 id = Impure . Term1 id

type Term0 id = Free (T id)
term0         = Impure . T

data AbstractPred id idt = Base id | Denotes idt | NotAny | Domain deriving (Eq, Show, Ord)
instance (Ppr id, Ppr idt) => Ppr (AbstractPred id idt) where
  ppr (Base id) = ppr id; ppr (Denotes id) = text "denotes_" <> ppr id; ppr Domain = text "domain"; ppr NotAny = text "notAny"
isDenotes Denotes{} = True; isDenotes _ = False

data WildCard = WildCard deriving (Eq, Ord)
vars' t = [ v | v@Right{} <- toList t]


datalogCompile :: forall idt idp d pgm.
                        (Ord idt, Ord idp, Ppr idt, Ppr idp,
                         pgm ~ AbstractDatalogProgram idp idt d,
                         d ~ Expr (Any :+: NotVar :+: Compound :+: PrologTerm idt)) =>
                         Program'' idp (Term idt)         -- ^ Original Program
                      -> ([d], pgm, pgm,pgm)         -- ^ (domain, notAny, denotes, program)

datalogCompile pl = (dom, notanyRules , denoteRules, cc') where
  pl' = prepareProgram pl
  PrologSig constructors _ = getPrologSignature1 pl'
  dom = (any :: d) : notvar : [ compound (reinject f) args | (f,i) <- Map.toList constructors
                                                    , i>0
                                                    , args <- replicateM i [notvar, any]
                                                    , not (all isNotVar args) ]
  notanyRules = [Pred NotAny [term0 d] :- [] | d <- tail dom]
  denoteRules = [Pred (Denotes f) (args ++ [term0 res]) :- notany_vars
                | (f, a) <- Map.toList constructors
                , groundness <- [0..2^a - 1]
                , let bits = reverse $ take a (reverse(dec2bin groundness) ++ repeat False)
                , let args = zipWith (\isnotvar v -> if isnotvar then v else term0 any) bits vars
                , let res  = if groundness == 2^a - 1 then notvar
                              else compound (reinject f) ((notvar?:any) <$> bits)
                , let notany_vars = [Pred NotAny [v] | (True,v) <- zip bits vars]
                ]
  vars = (return . Right . Auto) <$> [0..]

  cc' = map ( introduceWildcards
            . runFresh (flattenDupVarsC isLeft)
            . (\c -> fmap2 (mapFree (\t@(Term1 id tt) -> if null tt then T (reinject id)
                                                         else (error ("abstractCompilePre: " ++ show (ppr c)))))
                           c)
            . runFresh (flattenC (\(Impure(Term1 id tt)) v -> Pred (Denotes id) (tt++[return v])))
            . fmap legacyPred
            ) pl'

  legacyPred = mapPredId Base
  mkVar i = (return $ Right $ Auto i)
  allCC   = notanyRules ++ denoteRules ++ cc'
  runFresh m c = m c `evalState` ([Right $ Auto i | i <-  [1..]] \\ foldMap2 vars' c)

flattenC :: (Traversable f, Traversable t, MonadFresh v m) =>
              (Free f v -> v -> t (Free f v)) -> ClauseF (t (Free f v)) -> m(ClauseF (t (Free f v)))
flattenC box clause@(h :- b) = do
    (h' :- b', goals) <- runWriterT (mapM2 flattenTerm clause)
    return (h' :- (b' ++ goals))
  where
  flattenTerm  = evalFree return2 f
  f t = do
    v <- freshVar
    t' <- T.mapM flattenTerm t
    tell [box (Impure t') v]
    return2 v

flattenDupVarsC :: (Traversable t, Monad t, Ord var, MonadFresh var m) => (var -> Bool) -> Clause'' id (t var) -> m(Clause'' id (t var))
flattenDupVarsC isOk c = do
  (h' :- b', goals) <- runWriterT (T.mapM ((`evalStateT` mempty) . flattenDupVarsGoal) c)
  return (h' :- (b' ++ goals))
 where
   flattenDupVarsGoal = T.mapM(liftM join . T.mapM f)
   f v | isOk v = return2 v
   f v = do
    env <- get
    case v `Set.member` env of
      False -> modify (Set.insert v) >> return2 v
      True  -> do
          v' <- lift freshVar
          modify (Set.insert v')
          let res = return v'
          tell [return v :=: res]
          return res

introduceWildcards :: (Ord var, Foldable f, Functor f, t ~ Free f (Either WildCard var)) => Clause'' id t -> Clause'' id t
introduceWildcards c = fmap2 (>>=f) c where
    occurrences = Map.fromListWith (+) (foldMap2 vars c `zip` repeat 1)
    f v@Right{} | Just 1 <- Map.lookup v occurrences = return (Left WildCard)
    f v = return v


prepareProgram :: Program'' idp (Term' idt var) -> Program'' idp (TermC' idt (Either WildCard var))
prepareProgram  = fmap3 (foldFree (return . Right) f) where
    f (Int i)      = iterate succ zero !! fromInteger i
    f (Tuple tt)   = term1 tup tt
    f (Term id tt) = term1 (mkT id) tt
    f (Prolog.String s) = term1 (string s) []
    f Prolog.Wildcard = return (Left WildCard)
    f (Prolog.Cons h t) = term1 cons [h,t]
    f (Prolog.Nil) = term1 nil []

anyOrElseNotVar m = if isAny m then any else notvar

-- -----
-- Stuff
-- -----
deriving instance Ord (f(Expr f)) => Ord (Expr f)

dec2bin :: Int -> [Bool]
dec2bin i | i < 0 = error "no entiendo numeros negativos"
dec2bin i = go [] i where
  go acc 0 = acc
  go acc i = go ((i `mod` 2 /= 0) : acc) (i `div` 2)

(t?:f) b = if b then t else f

return2 = return.return
mapM2 = T.mapM . T.mapM
fmap2 = fmap.fmap
fmap3 = fmap.fmap.fmap
(<$$>)  = fmap2
(<$$$>) = fmap3
foldMap2 = foldMap.foldMap
isLeft Left{} = True; isLeft _ = False

instance Functor Any      where fmap _ Any = Any
instance Functor NotVar   where fmap _ NotVar = NotVar
instance Functor Compound where fmap f (Compound id tt) = Compound (f id) (fmap f tt)
instance Functor (T id)   where fmap f (T id) = T id
instance Functor PrologT where
    fmap _ Zero = Zero; fmap _ Succ = Succ
    fmap _ Tup = Tup  ; fmap _ (String s) = String s
    fmap _ Cons = Cons; fmap _ Nil = Nil

instance Ppr a => Ppr (Set a)            where ppr = braces   . hcat . punctuate comma . map ppr . Set.toList
instance (Ppr k, Ppr a) => Ppr (Map k a) where ppr = brackets . hcat . punctuate comma . map ppr . Map.toList
instance (Ppr a, Ppr b) => Ppr (Either a b) where ppr = either ppr ppr
instance PprF f => Ppr (Expr f) where ppr = foldExpr pprF
instance PprF f =>Show (Expr f) where show = show . ppr
instance Ppr Doc                where ppr = Prelude.id
instance Ppr WildCard           where ppr _ = text "_"

class Functor f => PprF f where pprF :: f Doc -> Doc
instance PprF Any         where pprF _ = text "any"
instance PprF NotVar      where pprF _ = text "notvar"
instance Ppr id => PprF (T id) where pprF (T id) = ppr id
instance Ppr id => Ppr (T id a) where ppr (T id) = ppr id
instance PprF PrologT where
    pprF Tup = Text.PrettyPrint.empty
    pprF Zero = text "0"; pprF Succ = char 's'
    pprF Cons = text "cons"; pprF Nil = text "nil"
    pprF (String s) = quotes (text s)
instance PprF Compound where pprF (Compound id dd) = ppr id <> parens (hcat $ punctuate comma $ map ppr dd)
instance (PprF f, PprF g) => PprF (f :+: g) where
  pprF (Inl l) = pprF l; pprF (Inr r) = pprF r

instance Functor  (Term1F id) where fmap f (Term1 id tt) = Term1 id (map f tt)
instance Foldable (Term1F id) where foldMap f (Term1 id tt) = foldMap f tt
instance Traversable (Term1F id) where traverse f (Term1 id tt) = Term1 id <$> traverse f tt
instance (Ppr id, Ppr a) => Ppr (Term1F id a) where ppr(Term1 id []) = ppr id; ppr (Term1 id tt) = ppr id <> parens (hcat $ punctuate comma $ map ppr tt)
instance Foldable (T id) where foldMap = mempty
instance Traversable (T id) where traverse _ (T id) = pure (T id)


#ifdef GHCI
-- NI CONTIGO NI SIN TI: Si la incluyo, Cabal ve un duplicado. Si no la incluyo, GHCi no ve ninguna.
-- Brought this instance here from the prolog package.
-- For some reason GHC 6.10.2 refuses to export it
instance (Monoid w, MonadFresh var m) => MonadFresh var (WriterT w m) where freshVar = lift freshVar
instance Monad m => MonadFresh v (StateT [v] m)  where freshVar = do { x:xx <- get; put xx; return x}
#endif
