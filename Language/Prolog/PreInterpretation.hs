{-# LANGUAGE CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances, FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards #-}
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
import Control.Monad (mplus, filterM, replicateM, liftM, join, when, forM)
import Control.Monad.Free (Free(..), mapFree, foldFree, evalFree, foldFreeM, isPure)
import Control.Monad.State (StateT, evalState, evalStateT)
import Control.Monad.Writer (WriterT, runWriter, runWriterT)
import Control.Monad.Reader (MonadReader(..), runReader)
import Control.Monad.RWS (MonadState(..), modify, MonadWriter(..), RWS, evalRWS, evalRWST, lift, RWST)
import Control.Monad.List (ListT(..), runListT)
import Data.AlaCarte.Ppr
import Data.Array
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
import Text.PrettyPrint as Ppr

import Data.Term (MonadFresh(..))
import Data.Term.Rules
import Data.Term.Var
import Language.Prolog.Syntax hiding (Cons, Nil, Wildcard, String, cons, nil, wildcard, string)
import Language.Prolog.Transformations
import Language.Prolog.Utils
import qualified Language.Prolog.Syntax as Prolog
import Language.Prolog.Signature

import System.Exit
import System.FilePath
import System.IO
import System.Directory
import System.Process

import Prelude hiding (any, succ, pred)
import qualified Prelude

-- Types
-- -----
type TermC  idt     = TermC' idt Var
type TermC' idt var = Term1 (Expr (PrologTerm idt)) (Either WildCard var)

type PrologTerm idt = PrologT :+: T idt :+: V

type DatalogTerm  d  = Term0 d (Either WildCard Var)
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

type MkPre ft fd = Arity (Expr ft) -> (DeltaMany (Expr ft) (Expr fd), Arity (Expr ft))

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
  (modes,transitions) = buildPre (mkDelta sigma)  pre0

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
getCookedSuccessPatterns' :: ( Ord idp, Ord idt, Ord var, Ppr idt
                             , dom ~ (Any :+: Static :+: Compound :+: NotVar :+: PrologTerm idt)) =>
                             Program'' idp (Term' idt var) -> Interpretation idp (Expr dom)
getCookedSuccessPatterns'  pl = fixEq (tp_preinterpretation pl' ta) mempty where
  pl' = prepareProgram pl
  PrologSig sigma _   = getPrologSignature1 pl'
  ta  = mkClauseAssignment (Just . id1) (Set.toList modes)
                 (\f tt -> case () of
                             _ | [] <- tt -> notvar
                             _ | all (not.isAny) tt -> static
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
  pre@(dom,tran) = buildPre (mkDelta sigma) pre0

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
  pl'                 = prepareProgram pl -- :: Program'' (Expr idp) (TermC' idt Var)
  PrologSig sigma'  _ = getPrologSignature1 pl'
  pre@(dom,tran)      = buildPre (mkDelta sigma') pre0
  (_, dencc, cc')     = abstractCompilePre compileSet pre pl'

-- ------------
-- Driver
-- ------------
computeSuccessPatterns :: forall idp t t' as.
                          (idp ~ (T String :+: QueryAnswer String), as ~ Abstract String, t ~ DatalogTerm (Expr as), t' ~ (Free (T (Expr as)) Var)) =>
                          Int -> Int -> Maybe (GoalF String t) -> Program'' String (Term' String Var) -> FilePath -> [FilePath] -> IO ([Expr as], [[GoalF (Expr idp) t']])
computeSuccessPatterns depth verbosity mb_goal_ pl fp bdd_paths = do
         bddbddb_jar <- findBddJarFile bdd_paths
         let mb_goal = (fmap (introduceWildcards . runFresh (flattenDupVarsC isLeft)) . queryAnswerGoal)
                         <$> mb_goal_ :: Maybe (AbstractDatalogProgram idp (Expr as))
             pl' :: Program'' (Expr idp) (TermC String)
             pl' = if isJust mb_goal then queryAnswer (prepareProgram pl)
                                     else mapPredId mkT <$$> prepareProgram pl
             PrologSig constructors predicates0 = getPrologSignature1 pl'
             (dom, _, denotes, clauses) = abstractCompilePre' depth pl'
             predicates = nub $
                           (case getPrologSignature0 <$> mb_goal of Just (PrologSig _ pred) -> (Map.toList pred ++); _ -> id )
                           (Map.toList predicates0)

         withTempFile "." (fp++".bddbddb") $ \fpbddbddb hbddbddb -> do

         -- Domain
         echo ("The domain is: " ++ show (ppr dom))
         withTempFile "." (fp++".map") $ \fpmap hmap -> do
         let dump_bddbddb txt = hPutStrLn hbddbddb txt >> echo txt

         echo ("writing domain map file to " ++ fpmap)
         dump_bddbddb "### Domains"
         let domsize = length dom
         dump_bddbddb ("D " ++ show domsize ++ " " ++ takeFileName fpmap)
         hPutStrLn hmap (show (vcat $ map (ppr) dom))
         hClose hmap

         -- Relations
         dump_bddbddb "\n### Relations\n"
         dump_bddbddb $ unlines $ map show
             [ text "denotes_" <> ppr c <> parens (hsep $ punctuate comma $ replicate (a+1) (text "arg : D"))
                    | (c,a) <- Map.toList constructors]
         dump_bddbddb $ unlines $ map show
             [ ppr c <> parens (hsep $ punctuate comma $ replicate a (text "arg : D"))
                        <+>  text "outputtuples"
                    | (c,a) <- predicates]
         dump_bddbddb "notAny (arg : D) inputtuples"
         let domainDict = Map.fromList (dom `zip` [(0::Int)..])

         withTempFile' (takeDirectory fp) "notAny.tuples" $ \notanyfp notanyh -> do
         echo ("writing facts for notAny in file " ++ notanyfp )
         hPutStrLn notanyh $ unlines (("# D0: " ++ show domsize) : [ show i | i <- [1..domsize - 1]])
         hClose notanyh

         -- Rules
         dump_bddbddb "\n### Rules\n"
         let cc        = foldFree return toId <$$$> clauses
             den_cc    = foldFree return toId <$$$> denotes
             mb_goal_c = foldFree return toId <$$$$> mb_goal
             toId (T f) | Just i <- Map.lookup f domainDict = term0 i
                        | otherwise = error ("Symbol not in domain: " ++ show (ppr f))
         dump_bddbddb (show $ ppr den_cc)
         dump_bddbddb (show $ ppr cc)
         maybe (return ()) (dump_bddbddb . show . ppr) mb_goal_c

         -- Running bddbddb
         hClose hbddbddb
         hClose hmap
         let cmdline = if verbosity>1 then  ("java -jar " ++ bddbddb_jar ++ " " ++ fpbddbddb)
                                      else ("java -jar " ++ bddbddb_jar ++ " " ++ fpbddbddb ++ "> /dev/null 2> /dev/null")
         echo ("Calling bddbddb with command line: " ++ cmdline ++ "\n")
         exitcode <- system cmdline

         case exitcode of
           ExitFailure{} -> error ("bddbddb failed with an error")
           ExitSuccess   -> do
            let domArray = listArray (0, domsize) dom
            results <- forM predicates $ \(p,i) -> do
                         echo ("Processing file " ++ show p ++ ".tuples")
                         let fp_result = (takeDirectory fp </> show p <.> "tuples")
                         output <- readFile fp_result
                         evaluate (length output)
                         removeFile fp_result
                         return [ Pred p (map (either var' (term0 . (domArray!))) ii)
                                  | ii <- map (map (uncurry wildOrInt) . zip [1..] . words) (drop 1 $ lines output)
                                  , all (< domsize) [i | Right i <- ii]]
            return (dom, results)

    where wildOrInt v "*" = Left v
          wildOrInt _ i   = Right (read i)
          echo x | verbosity>0   = hPutStrLn stderr x
                 | otherwise = return ()

          findBddJarFile [] = error "Cannot find bddbddb.jar"
          findBddJarFile (fp:fps) = do
            x <- doesFileExist fp
            if x then return fp else findBddJarFile fps

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
                         var    ~ Either WildCard Var,
                         pgmany ~ AbstractDatalogProgram  NotAny d,
                         pgmden ~ AbstractDatalogProgram (NotAny :+: DenotesT idt) d,
                         pgm    ~ AbstractDatalogProgram (DenotesT idt :+: idp) d,
                         d ~ Expr (Abstract idt)) =>
                         Int                                -- ^ Depth of the Preinterpretation used
                      ->  Program'' (Expr idp) (TermC idt)  -- ^ Original Program
                      -> ([d], pgmany, pgmden,pgm)          -- ^ (domain, notAny, denotes, program)

abstractCompilePre' 0 pl = (dom, [], denoteRules, cc') where
  PrologSig constructors _ = getPrologSignature1 pl
  dom = [any, static, notvar]
  denoteRules = [Pred (denotes f) (args ++ [term0 notvar]) :- []
                | (f, a) <- Map.toList constructors, a > 0
                , args <- replicateM a [term0 any, term0 notvar]
                ] ++
                [ Pred (denotes f) (replicate (a+1) (term0 static)) :- []
                | (f,a) <- Map.toList constructors
                ]
  cc' = map ( introduceWildcards
            . runFresh (flattenDupVarsC isLeft)
            . (\c -> fmap2 (mapFree (\t@(Term1 id tt) -> if null tt then T (reinject id)
                                                         else (error ("abstractCompilePre: " ++ show (ppr c)))))
                           c)
            . runFresh (flattenC (\(Impure(Term1 id tt)) v -> Pred (denotes id) (tt++[return v])))
            . fmap (mapPredId reinject)
            ) pl

abstractCompilePre' 1 pl = (dom, notanyRules, denoteRules, cc') where
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
                ] {- ++
                [ Pred (denotes f) (replicate a (term0 freeArg) ++ [term0 any]) :- []
                | (f,a) <- Map.toList constructors, a > 0
                ] -}

  vars = (return . Right . VAuto) <$> [0..]

  cc' = map ( introduceWildcards
            . runFresh (flattenDupVarsC isLeft)
            . (\c -> fmap2 (mapFree (\t@(Term1 id tt) -> if null tt then T (reinject id)
                                                         else (error ("abstractCompilePre: " ++ show (ppr c)))))
                           c)
            . runFresh (flattenC (\(Impure(Term1 id tt)) v -> Pred (denotes id) (tt++[return v])))
            . fmap (mapPredId reinject)
            ) pl

  mkVar i = (return $ Right $ VAuto i)

compileSet = AbstractCompile { mkDomain  = False
                             , id2domain = Set.singleton . reinject
                             , domain2Term = term0 . Set.mapMonotonic reinject
                             }
compilePlain = AbstractCompile { mkDomain = False
                               , id2domain = reinject
                               , domain2Term = term0 . reinject
                               }


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

-- ------------
-- Abstraction
-- ------------
--abstractAnys

abstractAnys theany cc = compress (Set.toList newcc) cc
  where
    cc'   = Set.fromList (runFresh (mapM2 (foldFreeM return2 replaceAnys)) cc)
    newcc = cc' `Set.difference` Set.fromList cc
    replaceAnys (T id) = if id == theany then return <$> freshVar else return (term0 id)

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

-- ------------------------------------------------------
-- DFTA algorithm to compute a disjoint preinterpretation
-- ------------------------------------------------------
-- | The framework introduces a distinguished object V in the abstract language
--   to model variables (no term evaluates to V).
data V a = V deriving (Eq,Ord)
mkV = inject V; isV (match -> Just V) = True; isV _ = False

pre0 :: (Any :<: f, V :<: id) => PreInterpretationSet id f
pre0 = (Set.singleton (Set.singleton any), Map.singleton (mkV,[])
                                                         (Set.singleton any))

pre0var :: (V :<: f, V :<: id) => PreInterpretationSet id f
pre0var = (Set.singleton (Set.singleton mkV), Map.singleton (mkV,[])
                                                         (Set.singleton mkV))

-- | Completes a preinterpretation from a Delta function and a signature
buildPre :: (Ord id, Ord da, Ppr id, Ppr da) =>
            (DeltaMany id da, Arity id) -> PreInterpretationSet' id da -> PreInterpretationSet' id da
buildPre (DeltaMany delta, sigma) = fixEq f
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


--notvarAny0 :: (Ord (f'(Expr f')), Ord (f(Expr f)), f' :<: f, Any :<: f, NotVar :<: f) => MkPre f' f
notvarAny0 sig = (toDeltaMany (mkDeltaAny sig) `mappend` toDeltaMany  deltaNotVar, sig) -- TODO Fix like in notVarAny1
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


data FreeArg a = FreeArg deriving (Eq,Ord,Show)
instance PprF FreeArg where pprF _ = text "free"
instance Functor FreeArg where fmap f _ = FreeArg
freeArg = inject FreeArg; isFree (match -> Just FreeArg) = True; isFree _ = False

notvarAny1 :: (Ord (Expr f), V :<: f, Ord (Expr f'), Compound :<: f',  Static :<: f', FreeArg :<: f', Any :<: f', NotVar :<: f', f :<: f') => MkPre f f'
notvarAny1 sig = (
                  toDeltaMany (mkDeltaAny sig') `mappend` 
                  toDeltaMany (Map.fromList delta), sig')
  where
   sig'   = sig `mappend` Map.singleton mkV 0
   domain = static : [ compound (reinject f) args
                            | (f,i) <- Map.toList sig, args <- replicateM i [freeArg,notvar], Prelude.any isFree args]
   delta  =     ((mkV,[]), freeArg) :
                [((f,args),  res)
                | (f, a) <- Map.toList sig, a > 0
                , groundness <- [0..2^a - 1]
                , let bits = reverse $ take a (reverse(dec2bin groundness) ++ repeat False)
                , args <- Prelude.mapM (\isnotvar -> if isnotvar then domain else [freeArg]) bits
                , let res  = compound (reinject f) ((notvar?:freeArg) <$> bits)
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

-- -----
-- Stuff
-- -----
deriving instance Ord (f(Expr f)) => Ord (Expr f)
deriving instance (Ppr id, Ppr [da]) => Ppr (DeltaMany id da)

runFresh m c  = m c `evalState` ([toEnum 1..] \\ getVars c)


withTempFile dir name m = bracket (openTempFile dir' name') (removeFile . fst) (uncurry m)
  where (dirname, name') = splitFileName name
        dir'  = dir </> dirname

withTempFile' dir name m = do
    doesFileExist fp >>= \true -> when true (error ("Please delete file " ++ fp ++ " and start again"))
    bracket (openFile fp ReadWriteMode) (\_->removeFile fp) (m fp)
  where fp = dir' </> name'
        (dirname, name') = splitFileName name
        dir'  = dir </> dirname

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

-- | Any is the constructor for the distinguished domain object
--   any, the bottom of the domain. Every object in the concrete
--   language belongs to the any set.
data Any f = Any deriving (Eq, Ord, Show)
any = inject Any; isAny (match -> Just Any) = True ; isAny _ = False

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

-- Testing
-- -------
--trace _ = id
tracePpr msg = id -- trace (render msg)


preSD_cons = buildPre (notvarAny0 list_sig)

data List a = List | ListList deriving (Eq,Show,Ord,Bounded)
type ListSum = Expr(List :+: Any)
list = inject List
listlist = inject ListList
pre_ex6  = buildPre (tran, sig) where
  sig  = list_sig `mappend` peano_sig
  tran = toDeltaMany(mkDeltaAny sig) `mappend`
         mkDeltaMany [ ((mkT "nil",  [])               , [list])
                     , ((mkT "cons", [any :: ListSum, list]), [list])
                     , ((mkT "nil",  [])               , [listlist])
                     , ((mkT "cons", [list, listlist]) , [listlist])
                     ]
list_sig  = Map.fromList [(mkT "cons",2), (mkT "nil", 0)]
peano_sig = Map.fromList [(mkT "s",1), (mkT "0", 0)]
