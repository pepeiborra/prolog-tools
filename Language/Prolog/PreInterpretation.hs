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
-}

module Language.Prolog.PreInterpretation where

import Control.Applicative
import Control.Arrow ((***))
import Control.Exception
import Control.Monad.Identity(Identity)
import Control.Monad (mplus, filterM, replicateM, liftM, join)
import Control.Monad.Free (Free(..), mapFree, foldFree, evalFree, foldFreeM, isPure)
import Control.Monad.State (StateT, evalState, evalStateT)
import Control.Monad.Writer (WriterT, runWriter, runWriterT)
import Control.Monad.Reader (MonadReader(..), runReader)
import Control.Monad.RWS (MonadState(..), modify, MonadWriter(..), RWS, evalRWS, evalRWST, lift, RWST)
import Control.Monad.List (ListT(..), runListT)
import Data.AlaCarte
import Data.Foldable (foldMap, toList, Foldable)
import qualified Data.Foldable as F
import Data.List (find, (\\), nub, nubBy, sort, sortBy, groupBy, elemIndex, foldl')
import Data.Maybe
import Data.Monoid (Sum(..), Monoid(..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Traversable as T
import Data.Traversable (Traversable(..))
import Language.Prolog.Semantics (MonadFresh(..), matches, equiv)
import Language.Prolog.Syntax hiding (Cons, Nil, Wildcard, String, cons, nil, wildcard, string)
import qualified Language.Prolog.Syntax as Prolog
import Language.Prolog.Signature
import Text.PrettyPrint as Ppr
import Unsafe.Coerce
import Prelude hiding (any, succ, pred)
import qualified Prelude

-- Types
-- -----
type TermC  idt     = TermC' idt VName
type TermC' idt var = Term1 (Expr (PrologTerm idt)) (Either WildCard var)

type PrologTerm idt = PrologT :+: T idt :+: V

type DatalogTerm  d  = Term0 d (Either WildCard VName)
type DatalogTerm' f  = DatalogTerm (ObjectSet f)
type DatalogProgram idp idt = [ClauseF (GoalF idp (DatalogTerm idt)) ]
type AbstractDatalogProgram  idp d = Program'' (Expr idp) (DatalogTerm d)
type AbstractDatalogProgram' idp d = Program'' (Expr idp) (DatalogTerm' d)

-- | An interpretation is just a set of goals
newtype Interpretation idp d = I {interpretation::Set (GoalF idp d)} deriving (Eq,Monoid)

-- | A Preinterpretation is composed of a Domain and a Delta mapping ids to domain objects
type PreInterpretation'   id d  = (Set d, Delta id d)
type PreInterpretation    id f  = PreInterpretation' (Expr id) (Expr f)
type PreInterpretationSet id f  = PreInterpretation' (Expr id) (Set(Expr f))
type PreInterpretationSet' id d = PreInterpretation' id (Set d)
type Arity id = Map id Int

type MkPre ft fd = Arity (Expr ft) -> DeltaMany (Expr ft) (Expr fd)

-- | The domain of a disjoint preinterpretation is composed by sets of objects.
--   Domain objects are modeled with open datatypes.
type Object d = (Expr d)
type ObjectSet d = Set(Expr d)

-- | A Delta is the mapping from n-ary syntactical function symbols to domain functions
type    Delta     id da = Map (id, [da])  da
newtype DeltaMany id da = DeltaMany {deltaMany::Map (id, [da]) [da]} deriving Show



type ClauseAssignment term d = forall idp var. Ord var => Clause'' idp (Free term var)  -> [Clause'' idp d]

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

getCookedSuccessPatterns :: (Ord idp, Ord idt, Ord var, Ppr idt) =>
                            Program'' idp (Term' idt var) -> Interpretation idp (Expr (Any :+: Compound :+: NotVar :+: PrologTerm idt))
getCookedSuccessPatterns  pl = fixEq (tp_preinterpretation pl' ta) mempty where
  pl' = prepareProgram pl
  PrologSig sigma _   = getPrologSignature1 pl'
  ta  = mkClauseAssignment (Just . id1) (Set.toList modes)
                 (\f tt -> fromMaybe (error ("getCookedSuccessPatterns: " ++ show (f,tt))) $
                           Map.lookup (f,tt) transitions)
  (modes,transitions) = cookPre sigma

-- | In this version we avoid generating the transitions map, encoding it as a Haskell function instead.
--   Improves time efficiency in at least 50%
getCookedSuccessPatterns' :: (Ord idp, Ord idt, Ord var, Ppr idt) =>
                             Program'' idp (Term' idt var) -> Interpretation idp (Expr (Any :+: Compound :+: NotVar :+: PrologTerm idt))
getCookedSuccessPatterns'  pl = fixEq (tp_preinterpretation pl' ta) mempty where
  pl' = prepareProgram pl
  PrologSig sigma _   = getPrologSignature1 pl'
  ta  = mkClauseAssignment (Just . id1) (Set.toList modes)
                 (\f tt -> case () of
                             _ | [] <- tt -> notvar
                             _ | all (not.isAny) tt -> notvar
                             _ | otherwise -> compound (reinject f) (map (\m -> if isAny m then any else notvar) tt))
  (modes,_) = cookPre sigma

getAbstractComp :: ( PprF f, Ord idp, Ord id, Ord(Expr f), Ppr id, Ppr idp, Any :<: f, ft :<: f, ft ~ PrologTerm id
                   , fp ~ (T idp :+: DenotesT id :+: Domain)) =>
                    MkPre ft f -> Program'' idp (Term id) ->
                    (PreInterpretationSet ft f, AbstractDatalogProgram' fp f)

getAbstractComp mkDelta pl = (pre, fmap2 (mapPredId reinject) dencc `mappend` cc') where
  PrologSig sigma _ = getPrologSignature1 pl'
  pl'            = prepareProgram pl
  (_, dencc, cc')= abstractCompilePre compileSet pre pl'
  pre@(dom,tran) = buildPre (mkDelta sigma) sigma pre0

getCookedAbstractComp :: (Ord idp, Ord id, Ppr id, Ppr idp, ft ~ PrologTerm id,
                          f ~ (Any :+: Compound :+: NotVar :+: ft), fp ~ (T idp :+: DenotesT id :+: Domain)) =>
                        Program'' idp (Term id) ->
                       (PreInterpretation ft f, AbstractDatalogProgram fp (Object f))

getCookedAbstractComp pl = (pre, fmap2 (mapPredId reinject)dencc `mappend` cc') where
  pl'               = prepareProgram pl
  PrologSig sigma _ = getPrologSignature1 pl'
  (_, dencc, cc')   = abstractCompilePre compilePlain pre pl'
  pre@(dom,tran)    = cookPre sigma

getSuccessPatterns' :: forall f fp ft idt idp.
                       (Any :<: f, ft :<: f, ft ~ PrologTerm idt, PprF f, Ord (Expr f),
                        Ord idp, Ord idt, Ppr idt, Ppr idp,
                        fp ~ (T idp :+: DenotesT idt :+: Domain)) =>
                        MkPre ft f -> Program'' idp (Term idt) -> Interpretation (Expr fp) (DatalogTerm' f)

getSuccessPatterns' mkDelta pl =
--  liftI (Set.filter (not.isDenotes.pred))
        (fixEq (tp_herbrand (Just . id0) T (fmap2 (mapPredId reinject) dencc `mappend` cc')) mempty)
 where
  pl'                 = prepareProgram pl -- :: Program'' (Expr idp) (TermC' idt VName)
  PrologSig sigma'  _ = getPrologSignature1 pl'
  pre@(dom,tran)      = buildPre (mkDelta sigma') sigma' pre0
  (_, dencc, cc')     = abstractCompilePre compileSet pre pl'

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

mkClauseAssignment getTermId domain pre c@(h :- cc) =
    [runReader (mapM2 (foldFreeM var_mapping pre') c) a | a <- assignments]
  where
   pre' = return . uncurry pre . fromMaybe (error "mkClauseAssignment") . openTerm
   openTerm t = getTermId t >>= \id -> Just (id, toList t)
   var_mapping v = ask >>= \map -> let Just d = Map.lookup v map in return d
   assignments = (Map.fromList . zip fv) `map` (replicateM (length fv) domain)
   fv          = snub(foldMap2 toList (h:cc))

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

type Term1 id    = Free (Term1F id)
data Term1F id a = Term1 {id1::id, tt1::[a]} deriving (Eq, Ord, Show)
term1 id = Impure . Term1 id
mapTerm1Id f = mapFree (mapTerm1IdF f)
mapTerm1IdF f (Term1 id args) = Term1 (f id) args


getPrologSignature1 = getPrologSignature' (Just . id1)
getPrologSignature0 = getPrologSignature' (Just . id0)

type Term0 id = Free (T id)
term0         = Impure . T

type AbstractCompile idt = DenotesT idt :+: Domain :+: NotAny
data Denotes idt a  = Denotes idt deriving (Eq, Show, Ord)
type DenotesT idt = Denotes (Expr (PrologTerm idt))
data NotAny a = NotAny deriving (Eq, Show, Ord)
data Domain a = Domain deriving (Eq, Show, Ord)
denotes = inject . Denotes; domain = inject Domain; notAny = inject NotAny

data WildCard = WildCard deriving (Eq, Ord)
wildCard = return (Left WildCard)

vars' t = [ v | v@Right{} <- toList t]


data AbstractCompileOpts id d termd = AbstractCompile { id2domain   :: id -> d
                                                      , domain2Term :: d -> termd
                                                      , mkDomain    :: Bool
                                                      }

abstractCompilePre ::  (term ~ TermC idt, ft ~ PrologTerm idt, Ppr idt, Ppr idp,
                        pgm  ~ AbstractDatalogProgram (T idp :+: DenotesT idt) d,
                        pgmd ~ AbstractDatalogProgram (T idp :+: DenotesT idt :+: Domain) d,
                        termd ~ DatalogTerm d) =>
                       AbstractCompileOpts(Expr ft) d termd
                    -> PreInterpretation' (Expr ft) d -- ^ Preinterpretation to use
                    -> Program'' idp term  -- ^ Original Program
                    -> (pgmd,pgm,pgmd)                -- ^ (domain, denotes, program)

abstractCompilePre AbstractCompile{..} (dom, transitions) cc = (domainrules, denoteRules, cc') where
  domainrules   = [Pred domain [domain2Term d] :- [] | d <- toList dom]
  denoteRules   = [Pred (denotes id) ((domain2Term <$> args) ++ [domain2Term res]) :- []
                          | ((id, args), res) <- Map.toList transitions]
  cc' = map ( introduceWildcards
            . runFresh (flattenDupVarsC isLeft)
            . (if mkDomain then varsDomain else id)
            . (\c -> fmap2 (mapFree (\t@(Term1 id tt) ->
                           if null tt then T (id2domain id)
                                      else (error ("abstractCompilePre: " ++ show (ppr c)))))
                           c)
            . runFresh (flattenC (\(Impure(Term1 id tt)) v -> Pred (denotes id) (tt++[return v])))
            . fmap (mapPredId mkT)
            ) cc

  varsDomain (h:-b)
    = let fv = Set.toList(Set.fromList(foldMap vars' h) `Set.difference` Set.fromList (foldMap2 vars' b))
      in h :- (b ++ map (\v -> Pred domain [return v]) fv)

type Abstract idt = Any :+: NotVar :+: Static :+: Compound :+: PrologTerm idt

abstractCompilePre' :: (Ord idt, Ppr idt, Ord (Expr idp), PprF idp, idp :<: (DenotesT idt :+: idp),
                         var    ~ Either WildCard VName,
                         pgmany ~ AbstractDatalogProgram  NotAny d,
                         pgmden ~ AbstractDatalogProgram (NotAny :+: DenotesT idt) d,
                         pgm    ~ AbstractDatalogProgram (DenotesT idt :+: idp) d,
                         d ~ Expr (Abstract idt)) =>
                         Program'' (Expr idp) (TermC idt)  -- ^ Original Program
                      -> ([d], pgmany, pgmden,pgm)         -- ^ (domain, notAny, denotes, program)

abstractCompilePre' pl = (dom, notanyRules, denoteRules, cc') where
  PrologSig constructors _ = getPrologSignature1 pl
  dom = any : static :
        [ compound (reinject f) args | (f,i) <- Map.toList constructors
                                     , i>0
                                     , args <- replicateM i [notvar, any]
                                     ]
  notanyRules = [Pred notAny [term0 d] :- [] | d <- tail dom]
  denoteRules = [Pred (denotes f) (args ++ [term0 res]) :- notany_vars
                | (f, a) <- Map.toList constructors, a > 0
                , groundness <- [0..2^a - 1]
                , let bits = reverse $ take a (reverse(dec2bin groundness) ++ repeat False)
                , let args = zipWith (\isnotvar v -> if isnotvar then v else term0 any) bits vars
                , let res  = compound (reinject f) ((notvar?:any) <$> bits)
                , let notany_vars = [Pred notAny [v] | (True,v) <- zip bits vars]
                ] ++
                [ Pred (denotes f) (replicate (a+1) (term0 static)) :- []
                | (f,a) <- Map.toList constructors
                ] ++
                [ Pred (denotes f) (replicate (a+1) (term0 any)) :- []
                | (f,a) <- Map.toList constructors, a >0
                ]


  vars = (return . Right . Auto) <$> [0..]

  cc' = map ( introduceWildcards
            . runFresh (flattenDupVarsC isLeft)
            . (\c -> fmap2 (mapFree (\t@(Term1 id tt) -> if null tt then T (reinject id)
                                                         else (error ("abstractCompilePre: " ++ show (ppr c)))))
                           c)
            . runFresh (flattenC (\(Impure(Term1 id tt)) v -> Pred (denotes id) (tt++[return v])))
            . fmap (mapPredId reinject)
            ) pl

  mkVar i = (return $ Right $ Auto i)

  runFresh m c = m c `evalState` ([Right $ Auto i | i <-  [1..]] \\ foldMap2 vars' c)

compileSet = AbstractCompile { mkDomain  = False
                             , id2domain = Set.singleton . reinject
                             , domain2Term = term0 . Set.mapMonotonic reinject
                             }
compilePlain = AbstractCompile { mkDomain = False
                               , id2domain = reinject
                               , domain2Term = term0 . reinject
                               }

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

introduceWildcards :: (Ord var, Foldable f, Functor f, t ~ Free f (Either WildCard var)) =>
                      Clause'' id t -> Clause'' id t
introduceWildcards c = fmap2 (>>=f) c where
    occurrences = Map.fromListWith (+) (foldMap2 vars c `zip` repeat 1)
    f v@Right{} | Just 1 <- Map.lookup v occurrences = wildCard
    f v = return v


prepareProgram :: Program'' idp (Term' idt var) -> Program'' idp (TermC' idt var)
prepareProgram  = fmap3 prepareTerm
prepareTerm = foldFree (return . Right) f where
    f (Int i)      = iterate succ zero !! fromInteger i
    f (Tuple tt)   = term1 tup tt
    f (Term id tt) = term1 (mkT id) tt
    f (Prolog.String s) = term1 (string s) []
    f Prolog.Wildcard = wildCard
    f (Prolog.Cons h t) = term1 cons [h,t]
    f (Prolog.Nil) = term1 nil []

data QueryAnswer idp a = QueryAll idp | Query idp Int Int | Answer idp deriving (Eq,Ord,Show)
answer = inject . Answer; queryAll = inject . QueryAll ; query id i j = inject (Query id i j)
instance Functor (QueryAnswer id) where
    fmap _ (Answer id)    = Answer id
    fmap _ (QueryAll id)  = QueryAll id
    fmap _ (Query id i j) = Query id i j
instance Ppr id => PprF (QueryAnswer id) where
    pprF (Answer   id)  = text "answer_" <> ppr id
    pprF (QueryAll id)  = text "query_" <> ppr id
    pprF (Query id i j) = text "query_" <> Ppr.int i <> text "_" <> Ppr.int j <> text "_" <> ppr id

queryAnswer :: (Monad mt, QueryAnswer idp :<: idp', term ~ mt (Either b VName)) =>
                   Program'' idp term -> Program'' (Expr idp') term
queryAnswer pgm = concatMap (uncurry queryF) (zip [1..] pgm) ++ map answerF pgm
 where
  answerF (Pred h h_args :- cc) =
      Pred (answer h) h_args :- ( Pred (queryAll h) h_args :
                                [ Pred (answer c) c_args | Pred c c_args <- cc ])
  queryF _ (_ :- []) = []
  queryF i (Pred h h_args :- cc@(Pred b0 b0_args :_)) =
      Pred (query b0 i 1) b0_args :- [Pred (queryAll h) h_args] :
      queryAllquery b0 (length b0_args) i 1 :
     concat
     [[Pred (query bj i j) bj_args :- ([Pred (answer c) c_args | Pred c c_args <- bleft] ++
                                       [Pred (queryAll h) h_args])
      ,queryAllquery bj (length bj_args) i j]
     | (j,(bleft, Pred bj bj_args :_)) <- zip [2..] (map (`splitAt` drop i cc)  [1..length cc - 1])]

queryAllquery h ar i j = let vars = take ar allvars in Pred (queryAll h) vars :- [Pred (query h i j) vars]
  where allvars = map (return . Right . Auto) [1..]

queryAnswerGoal :: (Monad mt, QueryAnswer idp :<: idp', term ~ mt (Either b VName)) =>
                   GoalF idp term -> Program'' (Expr idp') term

queryAnswerGoal  (Pred g g_args)  = [Pred (query g 0 1) g_args :- [], queryAllquery g (length g_args) 0 1]


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
-- | A constructor NotVar to denote nonvar things
data NotVar f = NotVar deriving (Eq, Ord, Show, Bounded)
-- | A constructor Static to denote static things
data Static f = Static deriving (Eq, Ord, Show, Bounded)
-- | NotVar0 is the domain of NotVar or Any
type NotVar0  = Expr (NotVar :+: Any)
notvar = inject NotVar
isNotVar (match -> Just NotVar{}) = True ; isNotVar _ = False
static = inject Static
isStatic (match -> Just Static{}) = True ; isStatic _ = False


notvarAny0 :: (Ord (f'(Expr f')), Ord (f(Expr f)), f' :<: f, Any :<: f, NotVar :<: f) => MkPre f' f
notvarAny0 sig = toDeltaMany (mkDeltaAny sig) `mappend`
                 toDeltaMany  deltaNotVar
 where
  deltaNotVar= Map.fromList [ ((reinject f, replicate i notvar), notvar)| (f,i) <- Map.toList sig]

-- | Compound is a recursive constructor to analyze the
--   instantiation level of a function symbol
data Compound f = Compound f [f] deriving (Show, Eq, Ord)

-- | NotVar1 is the domain which
--   looks one level below the constructor and marks
--   the arguments as notvar or dynamic.
type NotVarAny1 = Any :+: NotVar :+: Compound
compound id = inject . Compound id


notvarAny1 :: (Ord (Expr f), Ord (Expr f'), Compound :<: f',  Static :<: f', Any :<: f', NotVar :<: f', f :<: f') => MkPre f f'
notvarAny1 sig = -- toDeltaMany (mkDeltaAny sig) `mappend`
                 toDeltaMany (Map.fromList delta)
  where
   domain = any : static : [ compound (reinject f) args
                            | (f,i) <- Map.toList sig, args <- replicateM i [any,notvar], Prelude.any isAny args]
   delta  =     [((f,args),  res)
                | (f, a) <- Map.toList sig, a > 0
                , groundness <- [0..2^a - 1]
                , let bits = reverse $ take a (reverse(dec2bin groundness) ++ repeat False)
                , args <- Prelude.mapM (\isnotvar -> if isnotvar then drop 1 domain else [any]) bits
                , let res  = compound (reinject f) ((notvar?:any) <$> bits)
                ] ++
                [ ((f, replicate a static), static)
                | (f,a) <- Map.toList sig
                ]

cookPre :: (Compound :<: f, Any :<: f, NotVar :<: f, Ord (f(Expr f)), Ord (id(Expr id)), id :<: f) =>
                  Arity (Expr id) -> PreInterpretation id f
cookPre sig = (Set.fromList domain, tran) where
  domain = any : notvar : [ compound (reinject f) args | (f,i) <- Map.toList sig
                                                       , i>0
                                                       , args <- replicateM i [notvar, any]
                                                       , not (all isNotVar args) ]
  tran   = deltaAny `mappend` Map.fromList delta1

  deltaAny = Map.empty -- Map.fromList [ ((f, replicate i any), any)| (f,i) <- Map.toList sig, i > 0]
  delta1 = [((f, args), typ)
            | (f,i)  <- Map.toList sig
            , args <- replicateM i domain
            , let typ = case () of
                           _ | i == 0               -> notvar
                           _ | all (not.isAny) args -> notvar
                           _ | otherwise            -> compound (reinject f)
                                                                (map anyOrElseNotVar args)
           ]

mkDeltaMany = DeltaMany . Map.fromListWith (++)
toDeltaMany :: (Ord id, Ord a) => Delta id a -> DeltaMany id a
toDeltaMany = DeltaMany . Map.map (:[])

mkDeltaAny :: (Ord id, Ord (Expr f), Any :<: f) => Map id Int -> Delta id (Expr f)
mkDeltaAny sig = Map.fromList [ ((f, replicate i any), any)| (f,i) <- Map.toList sig]

anyOrElseNotVar m = if isAny m then any else notvar


-- | Abstract a set of clauses over a finite domain
{-
  The algorithm is a fixpoint over the following function.
  First we identify a set of candidate arguments to abstract,
  then generate the set of possible patterns that abstract these arguments,
  and filter out the ones which are not entirely covered by the input clauses.
  Finally we keep the resulting patterns and throw away the covered clauses.
-}
abstract dom = fixEq abstractF where
  ldom  = length dom
  abstractF cc@(Pred f tt : _) = compress (snub (concatMap go (tail $ combinations estimations)))  cc
   where
    ccset = Set.fromList cc
    zipTT = map snub $ zipAll (map args cc)
    estimations = [ i | (i,xx) <- zip [0..] zipTT, length xx >= ldom ]
    arity = length tt
    go ii = [ p | p <- patterns, all (`Set.member` ccset) (explodeAt ii p) ] where
     patterns =
        Pred f <$> ( filter ((>0) . length . filter isVar) . nubBy equiv . Prelude.sequence)
                    [ maybe (zipTT !! i) (const [var' 0, var' 1]) (elemIndex i ii)
                    | i <- [0..arity-1]
                    ]
  explodeAt ii pat@(Pred f tt)
   | vv <- [v | Pure v <- select ii tt]
   = snub (Pred f <$> [ map (>>= apply vals) tt
                        | vals <- (Map.fromList . zip vv) <$> replicateM (length vv) (term0 <$> dom)])
  apply subst v = case Map.lookup v subst of
                    Just t  -> t
                    Nothing -> return v

  compress patterns = let p' = zipIt patterns in (p' ++) . filter (\c -> not (Prelude.any (`matches` c) p'))
  zipIt = foldl' f [] . groupBy ((==) `on` (length . getVars)) . sortBy (compare `on` (length . getVars))
   where
     f acc xx = acc ++ filter (not.consequence) (snub xx) where
         consequence c = Prelude.any (`matches` c) acc

-- -----
-- Stuff
-- -----
deriving instance Ord (f(Expr f)) => Ord (Expr f)
deriving instance (Ppr id, Ppr [da]) => Ppr (DeltaMany id da)

dec2bin :: Int -> [Bool]
dec2bin i | i < 0 = error "no entiendo numeros negativos"
dec2bin i = go [] i where
  go acc 0 = acc
  go acc i = go ((i `mod` 2 /= 0) : acc) (i `div` 2)

(t?:f) b = if b then t else f

return2 = return.return
mapM2 = T.mapM . T.mapM
mapM3 = T.mapM . T.mapM . T.mapM
fmap2 = fmap.fmap
fmap3 = fmap.fmap.fmap
(<$$>)  = fmap2
(<$$$>) = fmap3
(<$$$$>) = fmap.fmap.fmap.fmap
foldMap3 = foldMap.foldMap.foldMap
foldMap2 = foldMap.foldMap
foldMapM f = fmap(F.foldr mappend mempty) . T.mapM f
foldMapM2 = foldMapM . foldMapM
fixEq f x | fx <- f x = if fx == x then x else fixEq f fx
snub = Set.toList . Set.fromList
isLeft Left{} = True; isLeft _ = False
runFresh m c = m c `evalState` ([Right $ Auto i | i <-  [1..]] \\ foldMap2 vars' c)


on cmp f x y = cmp (f x) (f y)
(f .&. g) x  = f x && g x

zipAll = getZipList . sequenceA . map ZipList

combinations :: [a] -> [[a]]
combinations [] = [[]]
combinations (x:xs)
    = combinations xs ++ [ x:xs' | xs' <- combinations xs ]


select :: (Ord t, Num t, Foldable f) => [t] -> f a ->[a]
select ii xx = go 0 (toList xx) (sort ii)
    where go _ [] _ = []
          go _ _ [] = []
          go n (x:xx) (i:ii) | n == i = x : go (n+1) xx ii
                             | otherwise = go (n+1) xx (i:ii)

instance (Ord id, Ord da) => Monoid (DeltaMany id da) where
  mempty = DeltaMany mempty
  DeltaMany m1 `mappend` DeltaMany m2 = DeltaMany $ Map.unionWith (++) m1 m2

instance Functor Any      where fmap _ Any = Any
instance Functor NotVar   where fmap _ NotVar = NotVar
instance Functor Static   where fmap _  _     = Static
instance Functor Compound where fmap f (Compound id tt) = Compound (f id) (fmap f tt)
instance Functor List     where fmap _ List = List; fmap _ ListList = ListList
instance Functor V        where fmap _ V      = V
instance Functor (T id)   where fmap f (T id) = T id
instance Functor PrologT where
    fmap _ Zero = Zero; fmap _ Succ = Succ
    fmap _ Tup = Tup  ; fmap _ (String s) = String s
    fmap _ Cons = Cons; fmap _ Nil = Nil

instance Ppr a => Ppr (Set a)            where ppr = braces   . hcat . punctuate comma . map ppr . Set.toList
instance (Ppr k, Ppr a) => Ppr (Map k a) where ppr = vcat . map ppr . Map.toList
instance (Ppr a, Ppr b) => Ppr (Either a b) where ppr = either ppr ppr
instance PprF f => Ppr (Expr f) where ppr = foldExpr pprF
instance PprF f =>Show (Expr f) where show = show . ppr
instance Ppr Doc                where ppr = id
instance Ppr WildCard           where ppr _ = text "_"

-- | Any is the constructor for the distinguished domain object
--   any, the bottom of the domain. Every object in the concrete
--   language belongs to the any set.
data Any f = Any deriving (Eq, Ord, Show)
any = inject Any; isAny (match -> Just Any) = True ; isAny _ = False

class Functor f => PprF f where pprF :: f Doc -> Doc
instance PprF Any         where pprF _ = text "any"
instance PprF V           where pprF _ = text "V"
instance PprF NotVar      where pprF _ = text "notvar"
instance PprF Static      where pprF _ = text "static"
instance PprF List        where pprF   = text . show
instance Ppr id => PprF (T id) where pprF (T id) = ppr id
instance Ppr id => Ppr (T id a) where ppr (T id) = ppr id
instance PprF PrologT where
    pprF Tup = Ppr.empty
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

instance (Ppr idt) => PprF (Denotes idt) where pprF (Denotes id) = text "denotes_" <> ppr id
instance PprF Domain where pprF Domain = text "domain"
instance PprF NotAny where pprF NotAny = text "notAny"
instance Functor (Denotes idt) where fmap _ (Denotes id) = Denotes id
instance Functor NotAny        where fmap _ NotAny = NotAny
instance Functor Domain        where fmap _ Domain = Domain

#ifdef GHCI
-- NI CONTIGO NI SIN TI: Si la incluyo, Cabal ve un duplicado. Si no la incluyo, GHCi no ve ninguna.
-- Brought this instance here from the prolog package.
-- For some reason GHC 6.10.2 refuses to export it
instance (Monoid w, Monad m) => MonadFresh VName (RWST r w (Sum Int) m) where freshVar = modify Prelude.succ >> liftM (Auto . getSum . Prelude.pred) get
--instance (Monoid w, MonadFresh var m) => MonadFresh var (WriterT w m) where freshVar = lift freshVar
--instance Monad m => MonadFresh v (StateT [v] m)  where freshVar = do { x:xx <- get; put xx; return x}
#endif

-- Testing
-- -------
--trace _ = id
tracePpr msg = id -- trace (render msg)

preSD_cons = buildPre (notvarAny0 list_sig) list_sig

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
