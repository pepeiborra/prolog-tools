{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}

#ifdef GHCI
module PrologSuccessPatterns where
#endif

--import Control.Monad.Exception
import Control.Applicative
import Control.Exception
import Control.Monad
import Control.Monad.Free
import Control.Monad.Error
import Data.Array
import Data.Foldable (Foldable, toList)
import Data.List (elemIndex, nub, nubBy, sort, sortBy, groupBy, foldl', (\\))
import Data.Maybe
import Data.AlaCarte
import Data.Monoid hiding (Any)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Traversable as T hiding (forM)
import Language.Prolog.Parser as Prolog (program, goal)
import qualified Language.Prolog.Parser as Prolog
import Language.Prolog.PreInterpretation
import Language.Prolog.Semantics (eval,debug, equiv, unifies, matches, MonadFresh(..))
import Language.Prolog.Signature
import Language.Prolog.Syntax
import System.Directory
import System.Environment
import System.Exit
import System.IO
import System.Cmd
import System.FilePath
import Text.ParserCombinators.Parsec (ParseError, parseFromFile, parse)
import qualified Text.ParserCombinators.Parsec as Parsec
import Text.PrettyPrint

import qualified Prelude
import Prelude hiding (pred, any, or)

import Debug.Trace

type Concrete = PrologTerm String

instance Error ParseError

echo = hPutStrLn stderr

bddbddb_jar_paths = ["bddbddb-full.jar", "bddbddb.jar"]

main = do
  (fp:rest) <- getArgs
  Right pl <- parseFromFile program fp
  let mkPre :: MkPre Concrete (Abstract String) = notvarAny1
  case rest of

    []                              -> run_bddbddb Nothing pl fp bddbddb_jar_paths
    ["bddbddb"]                     -> run_bddbddb Nothing pl fp bddbddb_jar_paths
    ("bddbddb" : bddbddb_jar_paths) -> run_bddbddb Nothing pl fp bddbddb_jar_paths

    ["dfta"] -> do
         let ((dom,_), pl0) = getAbstractComp mkPre pl
         echo "We compute the following compiled abstraction:"
         print (ppr pl0)
--         echo "the Preinterpretation domain is: "
--         print (ppr dom)
    ["cooked"] -> do
         let pl' = prepareProgram pl
         echo "We compute the following (cooked) compiled abstraction:"
         let (pre@(dom',_), pl') = getCookedAbstractComp pl
         print (ppr pl')
--         echo "the Preinterpretation domain is: "
--         print (ppr dom')
    ["success"] -> do
         echo "We obtain the success patterns:"
         print (getSuccessPatterns mkPre pl) -- :: Interpretation (Expr (T String)) (ObjectSet Abstract))
    ["success","cooked"] -> do
         echo "We obtain the (cooked) success patterns:"
         print (getCookedSuccessPatterns' pl)
    ["success","cookedslowly"] -> do
         echo "We obtain the (slowly cooked) success patterns:"
         print (getCookedSuccessPatterns pl)
    [goal] -> run_bddbddb (Just goal) pl fp bddbddb_jar_paths

--parseGoal :: String -> 
parseGoal = either (error.show) id . parse p  ""
   where p = Pred <$> Prolog.ident <*> Prolog.parens (Prolog.commaSep1 term)
         term = msum
                [Parsec.string "any" >> return (term0 any)
                ,Parsec.string "static" >> return (term0 static)
                , (>>= return .Right) <$> Prolog.var
--                ,Parsec.string "no" >> (Parsec.string "nvar" <|> Parsec.string "tvar") >> return (term0 notvar)
                ]

run_bddbddb mb_goal_ pl fp bdd_paths = do
         bddbddb_jar <- findBddJarFile bdd_paths
         let mb_goal = (fmap (introduceWildcards . runFresh (flattenDupVarsC isLeft)) . queryAnswerGoal . parseGoal)
                         <$> mb_goal_ :: Maybe (AbstractDatalogProgram (T String :+: QueryAnswer String) (Expr (Abstract String)))
             pl' :: Program'' (Expr(T String :+: QueryAnswer String)) (TermC String)
             pl' = if isJust mb_goal then queryAnswer (prepareProgram pl)
                                     else mapPredId mkT <$$> prepareProgram pl
             PrologSig constructors predicates0 = getPrologSignature1 pl'
             (dom, _, denotes, clauses) = abstractCompilePre' pl'
             predicates = nub $
                           (case getPrologSignature0 <$> mb_goal of Just (PrologSig _ pred) -> (Map.toList pred ++); _ -> id )
                           (Map.toList predicates0)

         withTempFile "." (fp++".bddbddb") $ \fpbddbddb hbddbddb -> do

         -- Domain
         withTempFile "." (fp++".map") $ \fpmap hmap -> do
         let dump_bddbddb txt = hPutStrLn hbddbddb txt >> putStrLn txt

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
         let cmdline = ("java -jar " ++ bddbddb_jar ++ " " ++ fpbddbddb)
         echo ("Calling bddbddb with command line: " ++ cmdline ++ "\n")
         exitcode <- system cmdline

         case exitcode of
           ExitFailure{} -> error ("bddbddb failed with an error")
           ExitSuccess -> do
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
            echo "bddbddb produced the following success patterns:\n"
            print (vcat $ map ppr $ concat results)
            echo " \nWe can simplify the patterns as follows:\n"
            let zipped_results = abstract dom <$> results
            print (vcat $ map ppr $ concat zipped_results)

    where wildOrInt v "*" = Left v
          wildOrInt _ i   = Right (read i)


findBddJarFile [] = error "Cannot find bddbddb.jar in the working directory"
findBddJarFile (fp:fps) = do
  x <- doesFileExist fp
  if x then return fp else findBddJarFile fps


withTempFile dir name m = bracket (openTempFile dir' name') (removeFile . fst) (uncurry m)
  where (dirname, name') = splitFileName name
        dir'  = dir </> dirname

withTempFile' dir name m = do
    doesFileExist fp >>= \true -> when true (error ("Please delete file " ++ fp ++ " and start again"))
    bracket (openFile fp ReadWriteMode) (\_->removeFile fp) (m fp)
  where fp = dir' </> name'
        (dirname, name') = splitFileName name
        dir'  = dir </> dirname

-- ---------------
