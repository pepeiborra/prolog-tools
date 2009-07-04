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
import Control.Monad.Identity(Identity(..))
import Control.Monad (mplus, filterM, replicateM, liftM, join, when, forM, forM_)
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

import Data.Term (HasId(..), MapId(..), MonadFresh(..), directSubterms, mapTermSymbols, foldTermM)
import Data.Term.Rules
import Data.Term.Var
import Language.Prolog.Representation
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

-- | Datalog terms cannot be compound terms.
--   For that reason we define it with Term0, which takes no subterms.
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
type Arity id = Map id (Set Int)

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

-- ------------
-- Driver
-- ------------
data ComputeSuccessPatternsOpts idp as = ComputeSuccessPatternsOpts
    { mb_goal   :: Maybe (Clause'' (Expr idp) (DatalogTerm (Expr as)))
    , pl        :: Program String
    , depth     :: Int
    , verbosity :: Int
    , debug     :: Bool
    , fp        :: FilePath
    , bddbddb_path ::[FilePath]
    }

computeSuccessPatternsOpts = ComputeSuccessPatternsOpts { mb_goal = Nothing
                                                        , pl      = []
                                                        , depth   = 1
                                                        , verbosity = 0
                                                        , debug   = False
                                                        , fp      = "tempbddbddb"
                                                        , bddbddb_path = []
                                                        }

computeSuccessPatterns :: forall idp idp' t t' as.
                          (t' ~ Term0 (Expr as) Var, idp' ~ (QueryAnswer :+: idp),
                           PprF idp, PprF as, Ord (Expr idp'), Ord (Expr as),
                           PrologTerm String :<: as, NotVar :<: as, Any :<: as, Compound :<: as,
                           T String :<: idp, NotAny :<: idp
                           ) =>
                          ComputeSuccessPatternsOpts idp as -> IO (Set(Expr as), [[GoalF (Expr idp') t']])
computeSuccessPatterns ComputeSuccessPatternsOpts{..} = do
         bddbddb_jar <- findBddJarFile bddbddb_path
         let mb_goal' = (fmap (introduceWildcards . runFresh (flattenDupVarsC isLeft)) . queryAnswerGoal)
                         <$> mb_goal
             pl' :: Program'' (Expr idp') (TermR String)
             pl' = case mb_goal' of
                       Just _              -> queryAnswer (prepareProgram pl)
                       Nothing             -> mapPredId (foldExpr (In . Inr)) <$$> prepareProgram pl
             PrologSig constructors predicates0 = getPrologSignature pl'
             (dom, _, denotes, clauses) = abstractCompileProgram depth pl'
             predicates = snub $
                           case getPrologSignature <$> mb_goal' of
                              Just (PrologSig _ pred) -> filter (not.isNotAny.fst) (Map.toList pred) ++ Map.toList predicates0
                              _                     -> Map.toList predicates0

         withTempFile (not debug) "." (fp++".bddbddb") $ \fpbddbddb hbddbddb -> do

         -- Domain
         echo ("The domain is: " ++ show (ppr dom))
         withTempFile (not debug) "." (fp++".map") $ \fpmap hmap -> do
         let dump_bddbddb txt = hPutStrLn hbddbddb txt >> echo txt

         echo ("writing domain map file to " ++ fpmap)
         dump_bddbddb "### Domains"
         let domsize = Set.size dom
         dump_bddbddb ("D " ++ show domsize ++ " " ++ takeFileName fpmap)
         hPutStrLn hmap (show (vcat $ map (ppr) $ Set.toList dom))
         hClose hmap
         -- Relations
         dump_bddbddb "\n### Relations\n"

         dump_bddbddb "notAny1 (arg : D) inputtuples"
         withTempFile' (not debug) (takeDirectory fp) "notAny1.tuples" $ \notanyfp notanyh -> do
         echo ("writing facts for notAny1 in file " ++ notanyfp )
         hPutStrLn notanyh $ unlines (("# D0: " ++ show domsize) : [ show i | i <- [1..domsize - 1]])
         hClose notanyh
         let domainDict = Map.fromList (Set.toList dom `zip` [(0::Int)..])
             toDomain f | Just i <- Map.lookup f domainDict = i
                        | otherwise = error ("Symbol not in domain: " ++ show (ppr f))

         toBeDeleted <- forM denotes $ \cc@(Pred cons@(match -> Just Denotes{}) (length -> ar) :- [] : _) -> do
                            let name = ppr cons <> ppr ar
                            dump_bddbddb $ show (name <> parens (hsep $ punctuate comma $ replicate ar (text "arg : D"))
                                                    <+> text "inputtuples")
                            withTempFile' False (takeDirectory fp) (show name ++ ".tuples") $ \fp h -> do
                            echo ("writing facts for " ++ show name ++ " in file " ++ fp )
                            debugMsg $ show (vcat $ map ppr cc)
                            let header = "# " ++ unwords ["D" ++ show i ++ ": " ++ show domsize | i <- [0 .. ar - 1]]
                                tuples = [ unwords $ map (show.ppr) tt
                                           | Pred _ tt :- [] <- mapTermSymbols toDomain <$$$> cc]
                            hPutStrLn h $ unlines (header : tuples)
                            hClose h
                            return fp
         (flip finally (when (not debug) $ mapM_ removeFile toBeDeleted)) $ do
           dump_bddbddb $ unlines $ map show
             [ ppr c <> ppr a <> parens (hsep $ punctuate comma $ replicate a (text "arg : D"))
                        <+>  text "outputtuples"
                    | (c,aa) <- predicates, a <- toList aa]

         -- Rules
           dump_bddbddb "\n### Rules\n"
           let cc        = mapTermSymbols toDomain <$$$> clauses
               den_cc    = mapTermSymbols toDomain <$$$> concat denotes
               mb_goal_c = mapTermSymbols toDomain <$$$$> mb_goal'
           dump_bddbddb (show $ pprBddbddb cc)
           maybe (return ()) (dump_bddbddb . show . pprBddbddb) mb_goal_c

         -- Running bddbddb
           hClose hbddbddb
           hClose hmap
           let cmdline = if verbosity>1 then ("java -jar " ++ bddbddb_jar ++ " " ++ fpbddbddb)
                                        else ("java -jar " ++ bddbddb_jar ++ " " ++ fpbddbddb ++ "> /dev/null 2> /dev/null")
           echo ("\nCalling bddbddb with command line: " ++ cmdline ++ "\n")
           exitcode <- system cmdline

           case exitcode of
             ExitFailure{} -> error ("bddbddb failed with an error")
             ExitSuccess   -> do
              let domArray = listArray (0, domsize) (Set.toList dom)
                  outpredicates = if debug then predicates else filter (isAnswer . fst) predicates
              results <- forM outpredicates $ \(p,ii) -> liftM concat $ forM (toList ii) $ \i -> do
                           echo ("Processing file " ++ show p ++ show i ++ ".tuples")
                           let fp_result = (takeDirectory fp </> show p ++ show i <.> "tuples")
                           output <- readFile fp_result
                           evaluate (length output)
                           when (not debug) $ removeFile fp_result
                           let tuples = map (map (uncurry wildOrInt) . zip [1..] . words) (drop 1 $ lines output)
                           return [ Pred p (map (either var' (term0 . (domArray!))) ii)
                                    | ii <- tuples
                                    , all (< domsize) [i | Right i <- ii]]
              return (dom, filter (not.null) results)

    where wildOrInt v "*" = Left v
          wildOrInt _ i   = Right (read i)
          echo x  | verbosity>0 = hPutStrLn stderr x
                  | otherwise   = return ()
          debugMsg x | debug       = hPutStrLn stderr x
                     | otherwise   = return ()
          findBddJarFile = go . (++ ["bddbdd.jar"]) where
              go [] = error "Cannot find bddbddb.jar"
              go (fp:fps) = do
                x <- doesFileExist fp
                if x then return fp else go fps

class PprBddBddb a where pprBddbddb :: a -> Doc
instance Ppr (Free f v) => PprBddBddb (Free f v)     where pprBddbddb = ppr
instance PprBddBddb a => PprBddBddb (ClauseF  a) where
    pprBddbddb (a :- []) = pprBddbddb a <> text "."
    pprBddbddb (a :- aa) = pprBddbddb a <+> text ":-" <+> hcat (punctuate comma $ map pprBddbddb aa) <> text "."
instance (Ppr id, Ppr a) => PprBddBddb (GoalF id a) where
    pprBddbddb (Pred p args) = ppr (Pred (ppr p <> Ppr.int (length args)) args)
    pprBddbddb p = ppr p
instance PprBddBddb (ClauseF a) => PprBddBddb [ClauseF a] where pprBddbddb = vcat . map pprBddbddb

-- ----------------------
-- Abstract Compilation
-- ----------------------
type Abstract = NotVar :+: Any :+: Compound

abstractCompileGoal :: (NotAny :<: pf, T String :<: pf, Monad m, Enum v) => String -> [Bool] -> Clause'' (Expr pf) (m v)
abstractCompileGoal f ii = Pred (mkT f) (take (length ii) vars) :- [ Pred notAny [v]| (False,v) <- zip ii vars]
  where vars = return <$> [toEnum 0 .. ]

abstractCompileProgram :: forall idt idp var fd d pgmany pgmden pgm.
                         (Ord idt, Ppr idt, Ord (Expr idp), PprF idp, Ord d,
                         var    ~ Either WildCard Var,
                         pgmany ~ AbstractDatalogProgram  NotAny d,
                         pgmden ~ AbstractDatalogProgram (NotAny :+: AbstractCompile :+: PrologTerm idt) d,
                         pgm    ~ AbstractDatalogProgram (AbstractCompile :+: PrologTerm idt :+: idp) d,
                         d      ~ (Expr fd),
                         PrologTerm idt :<: fd, Any :<: fd, NotVar :<: fd, Compound :<: fd) =>
                         Int                                -- ^ Depth of the Preinterpretation used
                      ->  Program'' (Expr idp) (TermR idt)  -- ^ Original Program
                      -> (Set d, pgmany, [pgmden], pgm)          -- ^ (domain, notAny, denotes, program)
{-
abstractCompileProgram  0 pl = (dom, [], denoteRules, cc') where
  PrologSig constructors _ = getPrologSignature pl
  dom         = [any, notvar]
  denoteRules = [Pred (denotes f) (map term0 args ++ [term0 res]) :- []
                | (f, aa) <- Map.toList constructors
                , a       <- toList aa
                , args    <- replicateM a [any, notvar]
                , let res = notvar --if all isStatic args then static else notvar
                ]
  cc' = map ( introduceWildcards
            . runFresh (flattenDupVarsC isLeft)
            . denoteAndDomainize reinject
            . fmap (mapPredId reinject)
            ) pl


abstractCompileProgram 1 pl = (Set.fromList dom, notanyRules, denoteRules, cc') where
  PrologSig constructors _ = getPrologSignature pl
  dom = any : [ compound (reinject f) args | (f,ii) <- Map.toList constructors
                                     , i <- toList ii
                                     , args <- replicateM i [notvar, any]
                                     ]
  notanyRules = [Pred notAny [term0 d] :- [] | d <- tail dom]

  denoteRules = [ [Pred (denotes (reinject f)) (args ++ [term0 res]) :- notany_vars
                  | groundness <- [0..2^a - 1]
                  , let bits = reverse $ take a (reverse(dec2bin groundness) ++ repeat False)
                  , let args = zipWith (\isnotvar v -> if isnotvar then v else term0 any) bits vars
                  , let res  = compound (reinject f) ((notvar?:any) <$> bits)
                  , let notany_vars = [Pred notAny [v] | (True,v) <- zip bits vars]
                  ]
                | (f, aa) <- Map.toList constructors, a <- toList aa
                ]

  vars = (return . Right . VAuto) <$> [0..]

  cc' = map ( introduceWildcards
            . runFresh (flattenDupVarsC isLeft)
            . fmap2 (mapTermSymbols reinject)
            . denoteAndDomainize
            ) pl
-}

abstractCompileProgram depth pl  = (dom, notAnyRules, denoteRules, cc') where
  PrologSig constructors _ = getPrologSignature pl
  dom = mkDom depth

  notAnyRules = [Pred notAny [term0 d] :- [] | d <- Set.toList $ Set.delete any dom]

  denoteRules = [      [Pred (denotes (reinject f)) (term0 <$> (args ++ [res])) :- []
                        | args    <- replicateM a (Set.toList dom)
                        , let res  = cutId depth $ compound (reinject f) args
                       ]
                | (f, aa) <- Map.toList constructors, a <- toList aa
                ]

  cc' = map ( introduceWildcards
            . runFresh (flattenDupVarsC isLeft)
            . fmap2 (mapTermSymbols reinject)
            . denoteAndDomainize
            ) pl

  mkDom :: Int -> Set(Expr fd)
  mkDom 0 = Set.fromList [notvar, any]
  mkDom i = Set.fromList (mkLevel (Set.toList $ mkDom (i-1)))

  mkLevel dom = any : [ compound (reinject f) args | (f,ii) <- Map.toList constructors
                                     , i <- toList ii
                                     , args <- replicateM i dom]

  cutId 0 t = if isAny t then t else notvar
  cutId i (match -> Just (Compound c tt)) = compound c (cutId (i-1) <$> tt)
  cutId i t = t


denoteAndDomainize :: (idp' ~ (AbstractCompile :+: idc :+: idp),
                       Functor idc, Functor idp, HasId t (Expr idc), Traversable t, Ord v, Enum v) =>
                      Clause'' (Expr idp) (Free t v) -> Clause'' (Expr idp') (Term0 (Expr idc) v)
-- Manual resolution of injections, to avoid introducing more constraints
denoteAndDomainize = fmap2 ids2domain
                   . runFresh (flattenC f)
                   . fmap (mapPredId (foldExpr (In . Inr . Inr)))
   where
    f t@(getId -> Just id) v = Pred (denotes (foldExpr (In . Inr . Inl) id)) (directSubterms t ++ [return v])
    ids2domain = mapFree (\t -> case getId t of
                                    Just id | null (toList t) -> T id
                                    _                         -> error "denoteAndDomainize" )

-- ------------
-- Abstraction
-- ------------
--abstractAnys

abstractAnys theany cc = compress (Set.toList newcc) cc
  where
    cc'   = Set.fromList (runFresh (mapM2 (foldFreeM return2 replaceAnys)) cc)
    newcc = cc' `Set.difference` Set.fromList cc
    replaceAnys (T id) = if id == theany then return <$> freshVar else return (term0 id)

-- ------------------------------------------------------
-- DFTA algorithm to compute a disjoint preinterpretation
-- ------------------------------------------------------
-- We don't actually use this anymore

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
                  | (f,nn)  <- Map.toList sigma
                  , n <- toList nn
                  , cc    <- replicateM n (Set.toList qd)
                  , let s = Set.fromList $ concat $ catMaybes
                            [Map.lookup (f, c) delta | c <- Prelude.sequence (map Set.toList cc)]
                  , not (Set.null s)
                ]

-- -----
-- Stuff
-- -----
prepareProgram :: (T idp :<: pf, PrologP :<: pf, var ~ Var) => Program'' idp (Term' idt var) -> Program'' (Expr pf) (TermR' idt var)
prepareProgram = runIdentity . mapM3 (foldTermM (return2 . Right)
                                                (representTerm term1 (return wildCard)))
                             . fmap2 representPred
                             . addBuiltInPredicates

deriving instance (Ppr id, Ppr [da]) => Ppr (DeltaMany id da)

runFresh m c  = m c `evalState` ([toEnum 1..] \\ Set.toList (getVars c))


withTempFile delete dir name m = bracket (openTempFile dir' name') close (uncurry m)
  where (dirname, name') = splitFileName name
        dir'  = dir </> dirname
        close = if delete then  (removeFile . fst) else (\_ -> return ())

withTempFile' delete dir name m = do
    -- doesFileExist fp >>= \true -> when true (error ("Please delete file " ++ fp ++ " and start again"))
    bracket (openFile fp ReadWriteMode) close (m fp)
  where fp = dir' </> name'
        (dirname, name') = splitFileName name
        dir'  = dir </> dirname
        close _ = if delete then removeFile fp else return ()

instance (Ord id, Ord da) => Monoid (DeltaMany id da) where
  mempty = DeltaMany mempty
  DeltaMany m1 `mappend` DeltaMany m2 = DeltaMany $ Map.unionWith (++) m1 m2


instance PprF f => Ppr (Expr f) where ppr = foldExpr pprF
instance PprF f =>Show (Expr f) where show = show . ppr

tracePpr msg = id -- trace (render msg)
