{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE UndecidableInstances, FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards, ViewPatterns #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

{- | Abstract Analyses based on Preinterpretations
     * /Abstract domains based on regular types/ John Gallagher, K Henriksen.
       <http://www.springerlink.com/index/QBXV0L2QCU2UNEG4.pdf>
     * /Practical model-based static analysis for definite logic programs/ J Gallagher, D Boulanger, H Saglam.
       <http://www.cs.bris.ac.uk/Publications/Papers/1000067.pdf>
-}

module Language.Prolog.PreInterpretation where

import Control.Applicative
import Control.Arrow ((***))
import Control.Exception
import Control.Monad (mplus, filterM, replicateM)
import Control.Monad.Free (Free(..),foldFree, evalFree, foldFreeM)
import Control.Monad.Reader (MonadReader(..), runReader)
import Control.Monad.RWS (MonadState, MonadWriter, RWS, evalRWS, tell, get,put)
import Control.Monad.List (ListT(..), runListT)
import Data.AlaCarte
import Data.Foldable (foldMap, toList)
import qualified Data.Foldable as F
import Data.List (find, (\\), nub)
import Data.Maybe
import Data.Monoid (Sum(..), Monoid(..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Traversable as T
import Language.Prolog.Syntax as Prolog
import Language.Prolog.Signature
import Text.PrettyPrint
import Prelude hiding (any)

-- | An interpretation is just a set of atoms
newtype Interpretation idp d = I {interpretation::Set (AtomF idp d)} deriving (Eq,Monoid)
instance (Ppr idp, Ppr term) => Ppr  (Interpretation idp term) where ppr  = vcat . map ppr . Set.toList . interpretation
instance (Ppr idp, Ppr term) => Show (Interpretation idp term) where show = show . ppr
mkI = I . Set.fromList

type ClauseAssignment idt d = forall idp var. Ord var => Clause'' idp (Term' idt var)  -> [Clause'' idp d]

deriving instance (Ord idp, Ord term) => Ord (AtomF idp term)
deriving instance (Ord id,  Ord f)    => Ord (TermF id f)


-- | Convenient function to get the set of success patterns of a program
--   according to an interpretation, giving as a parameter the function which
--   constructs the delta mapping from the signature of the program.
getSuccessPatterns mkDelta pl = fixEq (tp_preinterpretation pl' ta) mempty where
  PrologSig sigma _   = getPrologSignature pl'
  pl'   = fmap3 (foldFree return f) pl where f(Term f tt) = term (Id f) tt
  ta  = mkClauseAssignment (Set.toList modes)
                           (\f tt -> fromJust $ Map.lookup (f,tt) transitions)
  (modes,transitions) = buildPre (mkDelta sigma) sigma pre0

getSuccessPatterns' :: (Any :<: f, PprF f, f :<: T (PointedId id) :+: f, Ord idp, Ord id, Ppr id, Ord (Expr f)) =>
                        (Arity (PointedId id) -> DeltaMany (PointedId id) (Expr f)) -> Program'' idp (Term id) ->
                       (PreInterpretation (PointedId id) f, Program'' (AbstractPred idp) (Term (Object (T (PointedId id) :+: f))))
getSuccessPatterns' mkDelta pl = (pre, tp_abstractcompile pre pl') where
  PrologSig sigma _ = getPrologSignature pl'
  pl'   = fmap3 (foldFree return f) pl where f(Term f tt) = term (Id f) tt
  pre@(dom,_) = buildPre (mkDelta sigma) sigma pre0

-- ------------------
-- Fixpoint operator
-- ------------------

-- | The l.f.p. computation of a program according to a Clause Assignment.
tp_preinterpretation :: (Ord idp, Ord d, Ord var) => Program'' idp (Term' idt var) -> ClauseAssignment idt d -> Interpretation idp d -> Interpretation idp d
tp_preinterpretation p j (I i) = mkI
                             [ a
                              | c <- p
                              , a :- bb <- j c
                              , Set.fromList bb `Set.isSubsetOf` i]

-- | A clause assignments is computed from a preinterpretation.
mkClauseAssignment :: [d]                                -- ^ The domain as a list of objects
                   -> (idf -> [d] -> d)                  -- ^ The preinterpretation as a mapping function
                   -> (forall idp var. Ord var => Clause'' idp (Term' idf var) -> [Clause'' idp d])
mkClauseAssignment domain pre c@(h :- cc) = [runReader (mapM2 (foldFreeM var_mapping pre') c) a | a <- assignments]
  where
   pre' (Term f tt) = return (pre f tt) -- TODO Other Term constructors
   var_mapping v = ask >>= \map -> let Just d = Map.lookup v map in return d
   assignments = (Map.fromList . zip fv) `map` (replicateM (length fv) domain)
   fv          = foldMap2 toList (h:cc)


-- ----------------------
-- Abstract Compilation
-- ----------------------
-- | The framework introduces a distinguished object V in the abstract language
--   to model variables (no term evaluates to V).
data PointedId id = V | Id {fromId::id} deriving (Eq, Ord)

-- | A Preinterpretation is composed of a Domain and a Delta mapping ids to domain objects
type PreInterpretation id f = (Domain f, Delta id (Set (Expr f)))

-- | The domain of a disjoint preinterpretation is composed by sets of objects.
--   Domain objects are modeled with open datatypes.
type Domain f = Set (Object f)
type Object f = Set (Expr f)

-- | A Delta is the mapping from n-ary syntactical function symbols to domain functions
type    Delta     id da = Map (id, [da])  da
newtype DeltaMany id da = DeltaMany {deltaMany::Map (id, [da]) [da]} deriving Show
instance (Ord id, Ord da) => Monoid (DeltaMany id da) where
  mempty = DeltaMany mempty
  DeltaMany m1 `mappend` DeltaMany m2 = DeltaMany $ Map.unionWith (++) m1 m2

data T idt a = T idt deriving (Show, Eq)
instance Ppr id => PprF (T id) where pprF (T id) = ppr id
instance Functor (T id) where fmap f (T id) = T id
mkT :: (T id :<: f) => id -> Expr f
mkT id = inject (T id)

data AbstractPred id = Base id | Denotes | Domain deriving (Eq, Show)
instance Ppr id => Ppr (AbstractPred id) where ppr (Base id) = ppr id; ppr Denotes = text "denotes"; ppr Domain = text "domain"

tp_abstractcompile :: (f :<: T idt :+: f, term ~ Term idt) =>
                      PreInterpretation idt f -> Program'' idp term -> Program'' (AbstractPred idp) (Term (Object (T idt :+: f)))
tp_abstractcompile (domain, transitions) cc = (domainrules ++ deltaRules ++ cc') where
  domainrules         = [Pred Domain [domain2Term d] :- [] | d <- toList domain]
  domain2Term d       = term (Set.mapMonotonic reinject d) []
  id2domain           = Set.singleton . mkT
  deltaRules          = [Pred Denotes [term (id2domain id) (domain2Term <$> args), domain2Term res] :- []
                         | ((id, args), res) <- Map.toList transitions]
  cc'                 = map ( flattenC (\t v -> Pred Denotes [t,v])
                            . fmap2 legacyTerm
                            . varsDomain
                            . fmap  legacyPred
                            ) cc
  varsDomain c@(h:-b) = let fv = Set.toList(Set.fromList(foldMap vars h) `Set.difference` Set.fromList (foldMap2 vars b))
                          in h :- (b ++ map (\v -> Pred Domain [return v]) fv)

  legacyPred (Pred p tt) = Pred (Base p) tt
  legacyPred (Is t1 t2)  = Is t1 t2
  legacyPred (t1 :=: t2) = t1 :=: t2
  legacyPred Cut         = Cut

  legacyTerm          = foldFree return f where
    f (Term id tt) = term (id2domain id) tt
    f (Int i)      = Prolog.int i
    f (Float f)    = Prolog.float f
    f Wildcard     = wildcard
    f (String s)   = string s
    f (Tuple t)    = tuple t

flattenC :: term ~ Term idt => (term -> term -> AtomF id term) -> Clause'' id term -> Clause'' id term
flattenC box clause@(h :- b) = h' :- (b' ++ atoms)
  where (h' :- b', atoms) = evalRWS (T.mapM (flatten box) clause) () newvars
        newvars = [0..] \\ nub [ i | Auto i <- foldMap2 vars clause]

flatten :: (MonadState [Int] m, MonadWriter [AtomF id term] m, term ~ Term idt) => (term -> term -> AtomF id term) -> AtomF id term -> m (AtomF id term)
flatten box = T.mapM (evalFree (return . return) f) where
  f t = do
    (x:xs) <- get
    put xs
    tell [box (Impure t) (var' x)]
    return (var' x)

-- ------------------------------------------------------
-- DFTA algorithm to compute a disjoint preinterpretation
-- ------------------------------------------------------
pre0 = (Set.singleton (Set.singleton any), Map.singleton (V,[])
                                                         (Set.singleton any))

-- | Completes a preinterpretation from a Delta function and a signature
buildPre :: (da ~ Expr f, Any :<: f, PprF f, Ppr id, Ord id, Ord da) =>
            DeltaMany id da -> Arity id -> PreInterpretation id f -> PreInterpretation id f
buildPre (DeltaMany delta) sigma = fixEq f
 where
 f (qd, delta_d)
   | tracePpr (text "buildPre " <> parens (ppr qd <> comma <+> ppr delta_d)) False = undefined
   | otherwise      = (mconcat *** mconcat) (unzip new_elems)
   where
    new_elems = [tracePpr (text "  inserted " <> ppr s <+> text "with f=" <> ppr f <+> text "and cc=" <> ppr cc)
                 (qd `mappend` Set.singleton s, Map.insert (f,cc) s delta_d)
                  | (f,n)  <- Map.toList sigma
                  ,  cc    <- replicateM n (Set.toList qd)
                  , let s = Set.fromList $ concat $ catMaybes
                            [Map.lookup (f, c) delta | c <- Prelude.sequence (map Set.toList cc)]
                  , not (Set.null s)
                ]

mkDeltaMany = DeltaMany . Map.fromListWith (++)
toDeltaMany :: (Ord id, Ord a) => Delta id a -> DeltaMany id a
toDeltaMany = DeltaMany . Map.map (:[])

mkDeltaAny :: (Ord id, Ord (Expr f), Any :<: f) => Map id Int -> Delta id (Expr f)
mkDeltaAny sig = Map.fromList [ ((f, replicate i any), any)| (f,i) <- Map.toList sig]

-- --------------------------------------
-- Preinterpretations suitable for modes
-- --------------------------------------
type Arity id = Map id Int

-- | A constructor Static to denote ground things
data Static f = Static deriving (Eq, Ord, Show, Bounded)

-- | Static0 is the domain of Static or Any
type Static0  = Expr (Static :+: Any)
static = inject Static
isStatic (match -> Just Static) = True ; isStatic _ = False

staticAny0 :: Ord id => Arity id -> DeltaMany id Static0
staticAny0 sig = toDeltaMany (mkDeltaAny sig) `mappend`
                 toDeltaMany  deltaStatic
 where
  deltaStatic= Map.fromList [ ((f, replicate i static), static)| (f,i) <- Map.toList sig]

-- | Compound is a recursive constructor to analyze the
--   instantiation level of a function symbol
data Compound id f = Compound id [f] deriving (Show, Eq, Ord)

-- | Static1 is the domain which
--   looks one level below the constructor and marks
--   the arguments as static or dynamic.
type Static1  id   = Expr (Any :+: Static :+: Compound id)
compound id = inject . Compound id

staticAny1 :: Ord id => Arity id -> DeltaMany id (Static1 id)
staticAny1 sig = toDeltaMany (mkDeltaAny sig) `mappend`
                 toDeltaMany (Map.fromList deltaStatic1)
  where
   deltaStatic1 = [((f, args), typ)
                       | (f,i)  <- Map.toList sig
                       , args <- replicateM i [any, static]
                       , let typ = case () of
                                     _ | i == 0             -> static
                                     _ | all isStatic  args -> static
                                     _ | all isAny args     -> any
                                     _ | otherwise          -> compound f args]

-- -----
-- Stuff
-- -----
deriving instance Ord (f(Expr f)) => Ord (Expr f)

mapM2 = T.mapM . T.mapM
mapM3 = T.mapM . T.mapM . T.mapM
fmap2 = fmap.fmap
fmap3 = fmap.fmap.fmap
foldMap3 = foldMap.foldMap.foldMap
foldMap2 = foldMap.foldMap
foldMapM f = fmap(F.foldr mappend mempty) . T.mapM f
foldMapM2 = foldMapM . foldMapM
fixEq f x | fx <- f x = if fx == x then x else fixEq f fx
snub = Set.toList . Set.fromList

instance Functor Any           where fmap _ Any = Any
instance Functor Static        where fmap _ Static = Static
instance Functor (Compound id) where fmap f (Compound id tt) = Compound id (fmap f tt)
instance Functor List where
  fmap _ List = List
  fmap _ ListList = ListList

instance Ppr a => Ppr (Set a)            where ppr = braces   . hcat . punctuate comma . map ppr . Set.toList
instance (Ppr k, Ppr a) => Ppr (Map k a) where ppr = brackets . hcat . punctuate comma . map ppr . Map.toList
instance Show (PointedId String) where show = show.ppr
instance PprF f => Ppr (Expr f) where ppr = foldExpr pprF
instance PprF f =>Show (Expr f) where show = show . ppr
instance Ppr i => Ppr (PointedId i) where ppr (Id i) = ppr i; ppr V = text "v"
instance Ppr Doc                where ppr = id


-- | Any is the constructor for the distinguished domain object
--   any, the bottom of the domain. Every object in the concrete
--   language belongs to the any set.
data Any f = Any deriving (Eq, Ord, Show)
any = inject Any; isAny (match -> Just Any) = True ; isAny _ = False

class Functor f => PprF f where pprF :: f Doc -> Doc
instance PprF Any         where pprF _ = text "any"
instance PprF Static      where pprF _ = text "static"
instance PprF List        where pprF   = text . show
instance Show id => PprF (Compound id) where
    pprF (Compound id dd) = text (show id) <> parens (hcat $ punctuate comma $ map ppr dd)
instance (PprF f, PprF g) => PprF (f :+: g) where
  pprF (Inl l) = pprF l; pprF (Inr r) = pprF r

-- Testing
-- -------
trace _ = id
tracePpr msg = trace (render msg)

preSD_cons = buildPre (staticAny0 list_sig) list_sig

data List a = List | ListList deriving (Eq,Show,Ord,Bounded)
type ListSum = Expr(List :+: Any)
list = inject List
listlist = inject ListList
pre_ex6  = buildPre tran sig where
  sig  = list_sig `mappend` peano_sig
  tran = toDeltaMany(mkDeltaAny sig) `mappend`
         mkDeltaMany [ ((Id "nil",  [])               , [list])
                     , ((Id "cons", [any :: ListSum, list]), [list])
                     , ((Id "nil",  [])               , [listlist])
                     , ((Id "cons", [list, listlist]) , [listlist])
                     ]
list_sig  = Map.fromList [(Id "cons",2), (Id "nil", 0)]
peano_sig = Map.fromList [(Id "s",1), (Id "0", 0)]
