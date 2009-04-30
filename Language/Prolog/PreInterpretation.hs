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
import Control.Monad.Free (Free(..), mapFree, foldFree, evalFree, foldFreeM)
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
import Unsafe.Coerce
import Prelude hiding (any, succ, pred)

-- Types
-- -----
type TermC f = Term (Expr f)    -- Concrete terms
type TermD f = Term (Object f)  -- Domain (abstract) terms

-- | An interpretation is just a set of atoms
newtype Interpretation idp d = I {interpretation::Set (AtomF idp d)} deriving (Eq,Monoid)
instance (Ppr idp, Ppr term) => Ppr  (Interpretation idp term) where ppr  = vcat . map ppr . Set.toList . interpretation
instance (Ppr idp, Ppr term) => Show (Interpretation idp term) where show = show . ppr
mkI = I . Set.fromList
liftI f (I i) = I (f i)

-- | A Preinterpretation is composed of a Domain and a Delta mapping ids to domain objects
type PreInterpretation id f = (Domain f, Delta id (Set (Expr f)))
type MkPre ft fd = Arity (Expr ft) -> DeltaMany (Expr ft) (Expr fd)

-- | The domain of a disjoint preinterpretation is composed by sets of objects.
--   Domain objects are modeled with open datatypes.
type Domain f = Set (Object f)
type Object f = Set (Expr f)

-- | A Delta is the mapping from n-ary syntactical function symbols to domain functions
type    Delta     id da = Map (id, [da])  da
newtype DeltaMany id da = DeltaMany {deltaMany::Map (id, [da]) [da]} deriving Show

type ClauseAssignment idt d = forall idp var. Ord var => Clause'' idp (Term' idt var)  -> [Clause'' idp d]

deriving instance (Ord idp, Ord term) => Ord (AtomF idp term)
deriving instance (Ord id,  Ord f)    => Ord (TermF id f)

-- ------------------
-- External interface
-- ------------------

-- | Convenient function to get the set of success patterns of a program
--   according to an interpretation, giving as a parameter the function which
--   constructs the delta mapping from the signature of the program.
getSuccessPatterns mkDelta pl = fixEq (tp_preinterpretation pl' ta) mempty where
  PrologSig sigma _   = getPrologSignature pl'
  pl' = prepareProgram pl
  ta  = mkClauseAssignment (Set.toList modes) (\f tt -> fromJust $ Map.lookup (f,tt) transitions)
  (modes,transitions) = buildPre (mkDelta sigma) sigma pre0

getAbstractComp :: (Any :<: f, V :<: ft, Peano :<: ft, Tup :<: ft, T id :<: ft, PprF f, PprF ft, Ord idp, Ord id, Ord(Expr f), Ord (Expr ft), Ord (Expr f'), f :<: f', ft :<: f') =>
                        MkPre ft f -> Program'' idp (Term id) ->
                       (PreInterpretation (Expr ft) f, Program'' (AbstractPred idp) (TermD f'))

getAbstractComp mkDelta pl = (pre, pl'') where
  PrologSig sigma'  _ = getPrologSignature pl'
  pl'   = prepareProgram pl
  pl''  = tp_abstractcompile False pre pl'
  pre@(dom,tran) = buildPre (mkDelta sigma') sigma' pre0

getSuccessPatterns' :: (V :<: f1, T id :<: f1, Peano :<: f1, Tup :<: f1, Any :<: f2, f1 :<: f12, f2 :<: f12, PprF f1, PprF f2, PprF f12, Ord idp, Ord (Expr f1), Ord (Expr f2), Ord(Expr f12)) =>
                        MkPre f1 f2 -> Program'' idp (Term id) ->
                       Interpretation (AbstractPred idp) (TermD f12)

getSuccessPatterns' mkDelta pl = liftI (Set.filter (not.isDenotes.pred)) (fixEq (tp_herbrand pl'') mempty)
 where
  PrologSig sigma'  _ = getPrologSignature pl'
  pl'   = prepareProgram pl
  pl''  = tp_abstractcompile False pre pl'
  pre@(dom,tran) = buildPre (mkDelta sigma') sigma' pre0

data Peano a = Zero | Succ deriving (Eq, Ord)
succ x = term (inject Succ) [x] ; zero = term (inject Zero) []

data Tup a = Tup deriving (Eq,Ord)
tup = term (inject Tup)

prepareProgram  = fmap3 (foldFree return f) where
  f (Int i)    = iterate succ zero !! fromInteger i
  f (Tuple tt) = tup tt
  f t          = Impure (mapTermFid mkT t)

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

-- | The l.f.p. computation of a minimal Herbrand model of a program with a preinterpretation compiled in.
--   This does not compute the minimal Herbrand model of a program in general
tp_herbrand :: (Ord idp, Ord idt, Ord var, d ~ Term' idt var) => Program'' idp (Term' idt var) -> Interpretation idp d -> Interpretation idp d
tp_herbrand p (I i) = mkI
                             [ a
                              | c <- p
                              , a :- bb <- j c
                              , Set.fromList bb `Set.isSubsetOf` i]
  where
    PrologSig functors _ = getPrologSignature p
    j c@(h :- cc) = [fmap2 (>>= var_mapping a) c | a <- assignments] where
      var_mapping ass v | Just d <- Map.lookup v ass = term d []
      assignments   = --assert (all (==0) (Map.elems functors))
                      ((Map.fromList . zip fv) `map` replicateM (length fv) [f|(f,0) <- Map.toList functors]) -- Assuming all terms are arity 0
      fv             = snub $ foldMap2 toList (h:cc)

-- | A clause assignments is computed from a preinterpretation.
mkClauseAssignment :: (Show d, Show idf) =>
                      [d]                                -- ^ The domain as a list of objects
                   -> (idf -> [d] -> d)                  -- ^ The preinterpretation as a mapping function
                   -> (forall idp var. Ord var => Clause'' idp (Term' idf var) -> [Clause'' idp d])
mkClauseAssignment domain pre c@(h :- cc) = [runReader (mapM2 (foldFreeM var_mapping pre') c) a | a <- assignments]
  where
   pre' (Term f tt) = return (pre f tt)
   pre' t = error ("mkClauseAssignment "++ show(t))
   var_mapping v = ask >>= \map -> let Just d = Map.lookup v map in return d
   assignments = (Map.fromList . zip fv) `map` (replicateM (length fv) domain)
   fv          = snub(foldMap2 toList (h:cc))

-- ----------------------
-- Abstract Compilation
-- ----------------------
data T idt a = T idt deriving (Show, Eq, Ord)
mkT :: (T id :<: f) => id -> Expr f
mkT id = inject (T id)

data AbstractPred id = Base id | Denotes | Domain deriving (Eq, Show, Ord)
instance Ppr id => Ppr (AbstractPred id) where ppr (Base id) = ppr id; ppr Denotes = text "denotes"; ppr Domain = text "domain"
isDenotes Denotes = True; isDenotes _ = False

tp_abstractcompile :: (f :<: f', ft :<: f', Functor ft, term ~ TermC ft) =>
                       Bool                           -- ^ Insert domain() atoms
                    -> PreInterpretation (Expr ft) f  -- ^ Preinterpretation to use
                    -> Program'' idp term             -- ^ Original Program
                    -> Program'' (AbstractPred idp) (TermD f')
tp_abstractcompile mkDomain (domain, transitions) cc = domainrules++ denoteRules++cc' where
  domainrules         = if mkDomain then [Pred Domain [domain2Term d] :- [] | d <- toList domain] else []
  domain2Term d       = term (Set.mapMonotonic reinject d) []
  id2domain           = Set.singleton . reinject
  denoteRules          = [Pred Denotes [term (id2domain id) (domain2Term <$> args), domain2Term res] :- []
                         | ((id, args), res) <- Map.toList transitions]
  cc'                 = map ( flattenC (\t v -> Pred Denotes [t,v])
                            . fmap2 legacyTerm
                            . varsDomain
                            . fmap  legacyPred
                            ) cc
  varsDomain c@(h:-b)
    | mkDomain = let fv = Set.toList(Set.fromList(foldMap vars h) `Set.difference` Set.fromList (foldMap2 vars b))
                 in h :- (b ++ map (\v -> Pred Domain [return v]) fv)
    | otherwise = c

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
-- | The framework introduces a distinguished object V in the abstract language
--   to model variables (no term evaluates to V).
data V a = V deriving (Eq,Ord)
mkV = inject V

pre0 = (Set.singleton (Set.singleton any), Map.singleton (mkV,[])
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

staticAny0 :: (Static :<: f, Any :<: f ,Ord (f'(Expr f')), Ord (f(Expr f)), f' :<: f) => Arity (Expr f') -> DeltaMany (Expr f') (Expr f)
staticAny0 sig = toDeltaMany (mkDeltaAny sig) `mappend`
                 toDeltaMany  deltaStatic
 where
  deltaStatic= Map.fromList [ ((reinject f, replicate i static), static)| (f,i) <- Map.toList sig]

-- | Compound is a recursive constructor to analyze the
--   instantiation level of a function symbol
data Compound f = Compound f [f] deriving (Show, Eq, Ord)

-- | Static1 is the domain which
--   looks one level below the constructor and marks
--   the arguments as static or dynamic.
type Static1   = Any :+: Static :+: Compound
compound id = inject . Compound id

staticAny1 :: (Ord (Expr f), Ord (Expr f'), Compound :<: f', Any :<: f', Static :<: f', f :<: f') => Arity (Expr f) -> DeltaMany (Expr f) (Expr f')
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
                                     _ | otherwise          -> compound (reinject f) args]

-- -----
-- Stuff
-- -----
deriving instance Ord (f(Expr f)) => Ord (Expr f)

mapM2 = T.mapM . T.mapM
mapM3 = T.mapM . T.mapM . T.mapM
fmap2 = fmap.fmap
fmap3 = fmap.fmap.fmap
(<$$>)  = fmap2
(<$$$>) = fmap3
foldMap3 = foldMap.foldMap.foldMap
foldMap2 = foldMap.foldMap
foldMapM f = fmap(F.foldr mappend mempty) . T.mapM f
foldMapM2 = foldMapM . foldMapM
fixEq f x | fx <- f x = if fx == x then x else fixEq f fx
snub = Set.toList . Set.fromList

instance (Ord id, Ord da) => Monoid (DeltaMany id da) where
  mempty = DeltaMany mempty
  DeltaMany m1 `mappend` DeltaMany m2 = DeltaMany $ Map.unionWith (++) m1 m2

instance Functor Any      where fmap _ Any = Any
instance Functor Static   where fmap _ Static = Static
instance Functor Compound where fmap f (Compound id tt) = Compound (f id) (fmap f tt)
instance Functor List     where fmap _ List = List; fmap _ ListList = ListList
instance Functor Peano    where fmap _ Zero = Zero; fmap _ Succ = Succ
instance Functor (T id)   where fmap f (T id) = T id
instance Functor V        where fmap _ V = V
instance Functor Tup      where fmap _ Tup = Tup

instance Ppr a => Ppr (Set a)            where ppr = braces   . hcat . punctuate comma . map ppr . Set.toList
instance (Ppr k, Ppr a) => Ppr (Map k a) where ppr = brackets . hcat . punctuate comma . map ppr . Map.toList
instance PprF f => Ppr (Expr f) where ppr = foldExpr pprF
instance PprF f =>Show (Expr f) where show = show . ppr
instance Ppr Doc                where ppr = id


-- | Any is the constructor for the distinguished domain object
--   any, the bottom of the domain. Every object in the concrete
--   language belongs to the any set.
data Any f = Any deriving (Eq, Ord, Show)
any = inject Any; isAny (match -> Just Any) = True ; isAny _ = False

class Functor f => PprF f where pprF :: f Doc -> Doc
instance PprF Any         where pprF _ = text "any"
instance PprF V           where pprF _ = text "V"
instance PprF Static      where pprF _ = text "static"
instance PprF List        where pprF   = text . show
instance PprF Peano       where pprF Zero = text "0"; pprF Succ = char 's'
instance PprF Tup         where pprF Tup = Text.PrettyPrint.empty
instance Ppr id => PprF (T id) where pprF (T id) = ppr id
instance PprF Compound where pprF (Compound id dd) = ppr id <> parens (hcat $ punctuate comma $ map ppr dd)
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
         mkDeltaMany [ ((mkT "nil",  [])               , [list])
                     , ((mkT "cons", [any :: ListSum, list]), [list])
                     , ((mkT "nil",  [])               , [listlist])
                     , ((mkT "cons", [list, listlist]) , [listlist])
                     ]
list_sig  = Map.fromList [(mkT "cons",2), (mkT "nil", 0)]
peano_sig = Map.fromList [(mkT "s",1), (mkT "0", 0)]
