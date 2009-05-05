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
import Control.Monad.Identity(Identity)
import Control.Monad (mplus, filterM, replicateM, liftM, join)
import Control.Monad.Free (Free(..), mapFree, foldFree, evalFree, foldFreeM)
import Control.Monad.State (evalState, evalStateT)
import Control.Monad.Writer (runWriter, runWriterT)
import Control.Monad.Reader (MonadReader(..), runReader)
import Control.Monad.RWS (MonadState(..), modify, MonadWriter(..), RWS, evalRWS, lift, RWST)
import Control.Monad.List (ListT(..), runListT)
import Data.AlaCarte
import Data.Foldable (foldMap, toList, Foldable)
import qualified Data.Foldable as F
import Data.List (find, (\\), nub)
import Data.Maybe
import Data.Monoid (Sum(..), Monoid(..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Traversable as T
import Data.Traversable (Traversable(..))
import Language.Prolog.Semantics (MonadFresh(..))
import Language.Prolog.Syntax hiding (Cons, Nil, cons, nil)
import qualified Language.Prolog.Syntax as Prolog
import Language.Prolog.Signature
import Text.PrettyPrint
import Unsafe.Coerce
import Prelude hiding (any, succ, pred)
import qualified Prelude

-- Types
-- -----
type TermC idt = Term1 (Expr (PrologTerm idt)) VName   -- ^ Concrete terms
type TermD f   = Term0 (Object f) VName                -- ^ Domain (abstract) terms
type TermDset f   = Term0 (ObjectSet f) VName                -- ^ Domain (abstract) terms
type PrologTerm idt = PrologT :+: T idt :+: V

-- | An interpretation is just a set of goals
newtype Interpretation idp d = I {interpretation::Set (GoalF idp d)} deriving (Eq,Monoid)

-- | A Preinterpretation is composed of a Domain and a Delta mapping ids to domain objects
type PreInterpretation'   id d  = (Domain d, Delta id d)
type PreInterpretation    id f  = PreInterpretation' (Expr id) (Expr f)
type PreInterpretationSet id f  = PreInterpretation' (Expr id) (Set(Expr f))
type PreInterpretationSet' id d = PreInterpretation' id (Set d)
type Arity id = Map id Int

type MkPre ft fd = Arity (Expr ft) -> DeltaMany (Expr ft) (Expr fd)

-- | The domain of a disjoint preinterpretation is composed by sets of objects.
--   Domain objects are modeled with open datatypes.
type Domain d = Set d
type Object d = (Expr d)
type ObjectSet d = Set(Expr d)

-- | A Delta is the mapping from n-ary syntactical function symbols to domain functions
type    Delta     id da = Map (id, [da])  da
newtype DeltaMany id da = DeltaMany {deltaMany::Map (id, [da]) [da]} deriving Show

type ClauseAssignment term d = forall idp var. Ord var => Clause'' idp (Free term var)  -> [Clause'' idp d]

deriving instance (Ord idp, Ord term) => Ord (GoalF idp term)
deriving instance (Ord id,  Ord f)    => Ord (TermF id f)
instance (Ppr idp, Ppr term) => Ppr  (Interpretation idp term) where ppr  = vcat . map ppr . Set.toList . interpretation
instance (Ppr idp, Ppr term) => Show (Interpretation idp term) where show = show . ppr
mkI = I . Set.fromList
liftI f (I i) = I (f i)

-- ------------------
-- External interface
-- ------------------

-- | Convenient function to get the set of success patterns of a program
--   according to an interpretation, giving as a parameter the function which
--   constructs the delta mapping from the signature of the program.
getSuccessPatterns :: (Ord idt, Ord idp, Ord var, Ppr idt, PprF f', Ord (Expr f'), Any :<: f', ft ~ PrologTerm idt) =>
                      MkPre ft f' -> Program'' idp (Term' idt var) -> Interpretation idp (ObjectSet f')
getSuccessPatterns mkDelta pl = fixEq (tp_preinterpretation pl' ta) mempty where
  PrologSig sigma _   = getPrologSignature1 pl'
  pl' = prepareProgram pl
  ta  = mkClauseAssignment (Just . id1) (Set.toList modes) (\f tt -> fromJust $ Map.lookup (f,tt) transitions)
  (modes,transitions) = buildPre (mkDelta sigma) sigma pre0

getCookedSuccessPatterns :: (Ord idp, Ord idt, Ord var, Ppr idt) => Program'' idp (Term' idt var) -> Interpretation idp (Expr (Any :+: Compound :+: Static :+: PrologTerm idt))
getCookedSuccessPatterns  pl = fixEq (tp_preinterpretation pl' ta) mempty where
  pl' = prepareProgram pl
  PrologSig sigma _   = getPrologSignature1 pl'
  ta  = mkClauseAssignment (Just . id1) (Set.toList modes)
                 (\f tt -> fromMaybe (error ("getCookedSuccessPatterns: " ++ show (f,tt))) $
                           Map.lookup (f,tt) transitions)
  (modes,transitions) = cookPre sigma

-- | In this version we avoid generating the transitions map, encoding it as a Haskell function instead.
--   Improves time efficiency in at least 50%
getCookedSuccessPatterns' :: (Ord idp, Ord idt, Ord var, Ppr idt) => Program'' idp (Term' idt var) -> Interpretation idp (Expr (Any :+: Compound :+: Static :+: PrologTerm idt))
getCookedSuccessPatterns'  pl = fixEq (tp_preinterpretation pl' ta) mempty where
  pl' = prepareProgram pl
  PrologSig sigma _   = getPrologSignature1 pl'
  ta  = mkClauseAssignment (Just . id1) (Set.toList modes)
                 (\f tt -> case () of
                             _ | [] <- tt -> static
                             _ | all (not.isAny) tt -> static
                             _ | otherwise -> compound (reinject f) (map (\m -> if isAny m then any else static) tt))
  (modes,_) = cookPre sigma


prepareProgram :: Program'' idp (Term' idt var) -> Program'' idp (Term1 (Expr (PrologTerm idt)) var)
prepareProgram  = fmap3 (foldFree return f) where
    f (Int i)      = iterate succ zero !! fromInteger i
    f (Tuple tt)   = term1 tup tt
    f (Term id tt) = term1 (mkT id) tt
    f (Prolog.Cons h t) = term1 cons [h,t]
    f (Prolog.Nil) = term1 nil []

getAbstractComp :: (PprF f, Ord idp, Ord id, Ord(Expr f), Ppr id, Ppr idp, Any :<: f, ft :<: f, ft ~ PrologTerm id) =>
                        MkPre ft f -> Program'' idp (Term id) ->
                       (PreInterpretationSet ft f, Program'' (AbstractPred idp (Expr(PrologTerm id))) (TermDset f))

getAbstractComp mkDelta pl = (pre, dencc `mappend` cc') where
  PrologSig sigma _ = getPrologSignature1 pl'
  pl'            = prepareProgram pl
  (_, dencc, cc')= abstractCompilePre compileSet pre pl'
  pre@(dom,tran) = buildPre (mkDelta sigma) sigma pre0

getCookedAbstractComp :: (Ord idp, Ord id, Ppr id, Ppr idp, ft ~ PrologTerm id, f ~ (Any :+: Compound :+: Static :+: ft)) =>
                        Program'' idp (Term id) ->
                       (PreInterpretation ft f, Program'' (AbstractPred idp (Expr(PrologTerm id))) (TermD f))

getCookedAbstractComp pl = (pre, dencc `mappend` cc') where
  pl'               = prepareProgram pl
  PrologSig sigma _ = getPrologSignature1 pl'
  (_, dencc, cc')   = abstractCompilePre compilePlain pre pl'
  pre@(dom,tran)    = cookPre sigma

getSuccessPatterns' :: (Any :<: f,  ft :<: f, PprF f, Ord idp, Ord idt, Ppr idt, Ppr idp, Ord (Expr f), ft ~ PrologTerm idt) =>
                        MkPre ft f -> Program'' idp (Term idt) ->
                       Interpretation (AbstractPred idp (Expr ft)) (TermDset f)

getSuccessPatterns' mkDelta pl = liftI (Set.filter (not.isDenotes.pred)) (fixEq (tp_herbrand (Just . id0) T (dencc `mappend` cc')) mempty)
 where
  PrologSig sigma'  _ = getPrologSignature1 pl'
  pl'   = prepareProgram pl
  (_, dencc, cc') = abstractCompilePre compileSet pre pl'
  pre@(dom,tran) = buildPre (mkDelta sigma') sigma' pre0

-- ------------------
-- Fixpoint operator
-- ------------------
-- | The l.f.p. computation of a program according to a Clause Assignment.
tp_preinterpretation :: (Ord idp, Ord d, term ~ Free termF var, Functor termF, Ord var) =>
                        Program'' idp term -> ClauseAssignment termF d -> Interpretation idp d -> Interpretation idp d
tp_preinterpretation p j (I i) = mkI
                             [ a
                              | c <- p
                              , a :- bb <- j c
                              , Set.fromList bb `Set.isSubsetOf` i]

-- | The l.f.p. computation of a minimal Herbrand model of a program with a preinterpretation compiled in.
--   This does not compute the minimal Herbrand model of a program in general
tp_herbrand :: (Ord idp, Ord var, Ord id, Ord term, term ~ Free (termF id) var, Functor (termF id), Foldable (termF id), d ~ term) =>
               (forall id a . termF id a -> Maybe id) -- ^ A function to open a term
            -> (forall id a . id -> termF id a)       -- ^ term constructor
            -> Program'' idp term        -- ^ The Program
            -> Interpretation idp d      -- ^ An initial interpretation
            -> Interpretation idp d      -- ^ The next interpretation (one step application)
tp_herbrand openTerm mkTerm p (I i) = mkI
                             [ a
                              | c <- p
                              , a :- bb <- j c
                              , Set.fromList bb `Set.isSubsetOf` i]
  where
    PrologSig functors _ = getPrologSignature' openTerm p
    j c@(h :- cc) = [fmap2 (>>= var_mapping a) c | a <- assignments] where
      var_mapping ass v | Just d <- Map.lookup v ass = Impure $ mkTerm d
      assignments   = --assert (all (==0) (Map.elems functors))
                      ((Map.fromList . zip fv) `map` replicateM (length fv) [f|(f,0) <- Map.toList functors]) -- Assuming all terms are arity 0
      fv             = snub $ foldMap2 toList (h:cc)

-- | A clause assignments is computed from a preinterpretation.
mkClauseAssignment :: (Show d, Show idf, Traversable termF) =>
                      (forall d. termF d -> Maybe idf)   -- ^ A function to open the term
                   -> [d]                                -- ^ The domain as a list of objects
                   -> (idf -> [d] -> d)                  -- ^ The preinterpretation as a mapping function
                   -> (forall idp var. Ord var => Clause'' idp (Free termF var) -> [Clause'' idp d])

mkClauseAssignment getTermId domain pre c@(h :- cc) = [runReader (mapM2 (foldFreeM var_mapping pre') c) a | a <- assignments]
  where
   pre' = return . uncurry pre . fromMaybe (error "mkClauseAssignment") . openTerm
   openTerm t = getTermId t >>= \id -> Just (id, toList t)
   var_mapping v = ask >>= \map -> let Just d = Map.lookup v map in return d
   assignments = (Map.fromList . zip fv) `map` (replicateM (length fv) domain)
   fv          = snub(foldMap2 toList (h:cc))

-- ----------------------
-- Abstract Compilation
-- ----------------------
data PrologT a = Zero | Succ | Tup | Cons | Nil deriving (Show, Eq, Ord)
data T id a = T {id0::id} deriving (Show, Eq, Ord)
tup = inject Tup
mkT = inject . T
cons = inject Cons; nil = inject Nil
succ x = term1 (inject Succ) [x] ; zero = term1 (inject Zero) []
getPrologSignature1 = getPrologSignature' (Just . id1)

type Term1 id    = Free (Term1F id)
data Term1F id a = Term1 {id1::id, tt1::[a]} deriving (Eq, Ord, Show)
term1 id = Impure . Term1 id

type Term0 id = Free (T id)
term0         = Impure . T

data AbstractPred id idt = Base id | Denotes idt | Domain deriving (Eq, Show, Ord)
instance (Ppr id, Ppr idt) => Ppr (AbstractPred id idt) where ppr (Base id) = ppr id; ppr (Denotes id) = text "denotes_" <> ppr id; ppr Domain = text "domain"
isDenotes Denotes{} = True; isDenotes _ = False

data AbstractCompile idt d = AbstractCompile { id2domain   :: Expr (PrologTerm idt) -> d
                                             , domain2Term :: d -> Term0 d VName
                                             , mkDomain    :: Bool
                                             }
abstractCompilePre ::  (term ~ TermC idt, ft ~ PrologTerm idt, Ppr idt, Ppr idp,
                        pgm ~ Program'' (AbstractPred idp (Expr ft)) (Term0 d VName)) =>
                       AbstractCompile idt d
                    -> PreInterpretation' (Expr ft) d -- ^ Preinterpretation to use
                    -> Program'' idp term             -- ^ Original Program
                    -> (pgm,pgm,pgm)                  -- ^ (domain, denotes, program)

abstractCompilePre AbstractCompile{..} (domain, transitions) cc = (domainrules, denoteRules, flattenDupVarsC <$> cc') where
  domainrules   = [Pred Domain [domain2Term d] :- [] | d <- toList domain]
  denoteRules   = [Pred (Denotes id) ((domain2Term <$> args) ++ [domain2Term res]) :- []
                          | ((id, args), res) <- Map.toList transitions]

  cc' = map ((if mkDomain then varsDomain else id)
            . (\c -> fmap2 (mapFree (\t@(Term1 id tt) -> if null tt then T (id2domain id) else (error ("abstractCompilePre: " ++ show (ppr c)))) ) c)
            . flattenC (\(Impure(Term1 id tt)) v -> Pred (Denotes id) (tt++[v]))
            . fmap legacyPred
            ) cc

  varsDomain c@(h:-b)
    = let fv = Set.toList(Set.fromList(foldMap toList h) `Set.difference` Set.fromList (foldMap2 toList b))
      in h :- (b ++ map (\v -> Pred Domain [return v]) fv)

  legacyPred = mapPredId Base

compileSet = AbstractCompile { mkDomain  = False
                             , id2domain = Set.singleton . reinject
                             , domain2Term = term0 . Set.mapMonotonic reinject
                             }
compilePlain = AbstractCompile { mkDomain = False
                               , id2domain = reinject
                               , domain2Term = term0 . reinject
                               }

-- If we try to define SomeTerm f as a local type synonim instead (using type equality coercions),
-- GHC 6.10.2 panics down.
type SomeTerm f = Free f VName
flattenC :: (Traversable f, Traversable t) =>
              (SomeTerm f -> SomeTerm f -> t (SomeTerm f)) -> ClauseF (t (SomeTerm f)) -> ClauseF (t (SomeTerm f))
flattenC box clause@(h :- b) = h' :- (b' ++ goals)
  where
  (h' :- b', goals) = evalRWS (mapM2 flattenTerm clause) () newvars
  newvars = [0..] \\ nub [ i | Auto i <- foldMap2 toList clause]
  flattenTerm  = evalFree (return . return) f
  f t = do
    (x:xs) <- get
    put xs
    t' <- T.mapM flattenTerm t
    tell [box (Impure t') (var' x)]
    return (var' x)

flattenDupVarsC :: (Traversable t, Monad t) => Clause'' id (t VName) -> Clause'' id (t VName)
flattenDupVarsC c = h' :- (b' ++ goals)
 where
   (h' :- b', goals) = evalRWS (T.mapM ((`evalStateT` mempty) . flattenDupVarsGoal) c) () newvars
   newvars = Sum (1 + maximum (0:[ i | Auto i <- foldMap2 toList c]))
   flattenDupVarsGoal = T.mapM(liftM join . T.mapM f)

   f v = do
    env <- get
    case v `Set.member` env of
      False -> modify (Set.insert v) >> return (return v)
      True  -> do
          v' <- lift freshVar
          modify (Set.insert v')
          let res = return v'
          tell [return v :=: res]
          return res

instance Functor  (Term1F id) where fmap f (Term1 id tt) = Term1 id (map f tt)
instance Foldable (Term1F id) where foldMap f (Term1 id tt) = foldMap f tt
instance Traversable (Term1F id) where traverse f (Term1 id tt) = Term1 id <$> traverse f tt
instance (Ppr id, Ppr a) => Ppr (Term1F id a) where ppr(Term1 id []) = ppr id; ppr (Term1 id tt) = ppr id <> parens (hcat $ punctuate comma $ map ppr tt)
instance Foldable (T id) where foldMap = mempty
instance Traversable (T id) where traverse _ (T id) = pure (T id)

-- ------------------------------------------------------
-- DFTA algorithm to compute a disjoint preinterpretation
-- ------------------------------------------------------
-- | The framework introduces a distinguished object V in the abstract language
--   to model variables (no term evaluates to V).
data V a = V deriving (Eq,Ord)
mkV = inject V

pre0 :: (Any :<: f, V :<: id) => PreInterpretationSet id f
pre0 = (Set.singleton (Set.singleton any), Map.singleton (mkV,[])
                                                         (Set.singleton any))

-- | Completes a preinterpretation from a Delta function and a signature
buildPre :: (Ord id, Ord da, Ppr id, Ppr da) =>
            DeltaMany id da -> Arity id -> PreInterpretationSet' id da -> PreInterpretationSet' id da
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

-- --------------------------------------
-- Preinterpretations suitable for modes
-- --------------------------------------
-- | A constructor Static to denote ground things
data Static f = Static deriving (Eq, Ord, Show, Bounded)

-- | Static0 is the domain of Static or Any
type Static0  = Expr (Static :+: Any)
static = inject Static
isStatic (match -> Just Static) = True ; isStatic _ = False

staticAny0 :: (Ord (f'(Expr f')), Ord (f(Expr f)), f' :<: f, Any :<: f, Static :<: f) => MkPre f' f
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

staticAny1 :: (Ord (Expr f), Ord (Expr f'), Compound :<: f', Any :<: f', Static :<: f', f :<: f') => MkPre f f'
staticAny1 sig = toDeltaMany (mkDeltaAny sig) `mappend`
                 toDeltaMany (Map.fromList deltaStatic1)
  where
   deltaStatic1 = [((f, args), typ)
                       | (f,i)  <- Map.toList sig
                       , args <- replicateM i [any, static]
                       , let typ = case () of
                                     _ | i == 0             -> static
                                     _ | all isStatic  args -> static
--                                     _ | all isAny args     -> any
                                     _ | otherwise          -> compound (reinject f) args]


cookPre :: (Compound :<: f, Any :<: f, Static :<: f, Ord (f(Expr f)), Ord (id(Expr id)), id :<: f) =>
                  Arity (Expr id) -> PreInterpretation id f
cookPre sig = (Set.fromList domain, tran) where
  domain = any : static : [ compound (reinject f) args | (f,i) <- Map.toList sig
                                                       , i>0
                                                       , args <- replicateM i [static, any]
                                                       , not (all isStatic args) ]
  tran   = deltaAny `mappend` Map.fromList delta1

  deltaAny = Map.empty -- Map.fromList [ ((f, replicate i any), any)| (f,i) <- Map.toList sig, i > 0]
  delta1 = [((f, args), typ)
            | (f,i)  <- Map.toList sig
            , args <- replicateM i domain
            , let typ = case () of
                           _ | i == 0               -> static
                           _ | all (not.isAny) args -> static
                           _ | otherwise            -> compound (reinject f)
                                                                (map (\m -> if isAny m then any else static) args)
           ]

mkDeltaMany = DeltaMany . Map.fromListWith (++)
toDeltaMany :: (Ord id, Ord a) => Delta id a -> DeltaMany id a
toDeltaMany = DeltaMany . Map.map (:[])

mkDeltaAny :: (Ord id, Ord (Expr f), Any :<: f) => Map id Int -> Delta id (Expr f)
mkDeltaAny sig = Map.fromList [ ((f, replicate i any), any)| (f,i) <- Map.toList sig]

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
instance Functor V        where fmap _ V      = V
instance Functor (T id)   where fmap f (T id) = T id
instance Functor PrologT where
    fmap _ Zero = Zero; fmap _ Succ = Succ
    fmap _ Tup = Tup
    fmap _ Cons = Cons; fmap _ Nil = Nil

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
instance Ppr id => PprF (T id) where pprF (T id) = ppr id
instance Ppr id => Ppr (T id a) where ppr (T id) = ppr id
instance PprF PrologT where
    pprF Tup = Text.PrettyPrint.empty
    pprF Zero = text "0"; pprF Succ = char 's'
    pprF Cons = text "cons"; pprF Nil = text "nil"
instance PprF Compound where pprF (Compound id dd) = ppr id <> parens (hcat $ punctuate comma $ map ppr dd)
instance (PprF f, PprF g) => PprF (f :+: g) where
  pprF (Inl l) = pprF l; pprF (Inr r) = pprF r

-- -------------------
-- Output for bddbddb
-- -------------------
newtype BddBddb a = BddBddb a

instance (Compound :<: f, Static :<: f, T String :<: f, Any :<: f, PprF f) => Ppr (BddBddb (TermD f)) where
    ppr (BddBddb t) = ppr $ mapFree (\(T id) -> T (BddBddb id)) t

instance (Compound :<: f, Static :<: f, Any :<: f, PprF f) => Ppr (BddBddb (Expr f)) where
    ppr (BddBddb e) = foldExpr f e where
        f (prj -> Just Static) = text "s"
        f (prj -> Just Any)    = text "d"
        f (prj -> Just(Compound id args)) = id <> text "_" <> hcat args
        f x = pprF x

pprBddbddb :: (Functor f, Compound :<: f, Static :<: f, T String :<: f, Any :<: f, Ppr idp, PprF f) => Program'' idp (TermD f) -> Doc
pprBddbddb = ppr . fmap3 BddBddb

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
