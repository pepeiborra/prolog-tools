{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}
{-# LANGUAGE NamedFieldPuns, RecordWildCards #-}
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
import Data.Term (MonadFresh(..))
import Data.Term.Var
import qualified Data.Map as Map
import qualified Data.Set as Set
--import Data.Traversable as T hiding (forM)
import Language.Prolog.Parser as Prolog (program)
import qualified Language.Prolog.Parser as PrologP
import Language.Prolog.PreInterpretation
import Language.Prolog.Semantics (eval,debug)
import Language.Prolog.Signature
import Language.Prolog.Syntax as Prolog
import Language.Prolog.Transformations
import Language.Prolog.Utils
import System.Console.GetOpt
import System.Directory
import System.Environment
import System.Exit
import System.IO
import System.Cmd
import System.FilePath
import Text.ParserCombinators.Parsec (ParseError, getState, setState, runParser, parseFromFile, parse, oneOf)
import qualified Text.ParserCombinators.Parsec as Parsec
import Text.PrettyPrint hiding (Mode(..),mode)

import qualified Prelude
import Prelude hiding (pred, any, or)

import Debug.Trace

type Concrete = PrologTerm String

instance Error ParseError

echo = hPutStrLn stderr

bddbddb_jar_paths = ["bddbddb-full.jar", "bddbddb.jar"]

main = do
  (opts@Opts{..}, nonOpts) <- getOptions
  let mkPre :: MkPre Concrete (FreeArg :+: Abstract String) = notvarAny1
  case mode of
    Bddbddb -> run_bddbddb opts
    Fixpoint -> do
         echo "We obtain the success patterns:"
         print (getSuccessPatterns mkPre pl) -- :: Interpretation (Expr (T String)) (ObjectSet Abstract))

{-
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
    ["success","cooked"] -> do
         echo "We obtain the (cooked) success patterns:"
         print (getCookedSuccessPatterns' pl)
    ["success","cookedslowly"] -> do
         echo "We obtain the (slowly cooked) success patterns:"
         print (getCookedSuccessPatterns pl)
-}

run_bddbddb Opts{..} = do
  (dom, results) <- computeSuccessPatterns depth verbosity goal pl problemFile bddbddb_path
  echo "bddbddb produced the following success patterns:\n"
  print (vcat $ map ppr $ concat results)
  echo " \nWe can simplify the patterns as follows:\n"
  let zipped_results = abstract (term0 <$> dom) <$> results
  print (vcat $ map ppr $ concat zipped_results)

-- ---------------

-- --------------------------
-- Parsing Prolog problems
-- --------------------------
data PrologSection = QueryProgram [Goal String] | Clause (Prolog.Clause String) | QueryString String

problemParser = do
  txt <- Parsec.getInput
  let !queryComments = map QueryString $ catMaybes $ map f (lines txt)
  res <- PrologP.whiteSpace >> many (Clause <$> PrologP.clause <|> QueryProgram <$> PrologP.query)
  return (res ++ queryComments)
  where f ('%'    :'q':'u':'e':'r':'y':':':goal) = Just goal
        f ('%':' ':'q':'u':'e':'r':'y':':':goal) = Just goal
        f _ = Nothing

goalParser = PrologP.whiteSpace >> Pred <$> PrologP.ident <*> PrologP.parens (PrologP.commaSep1 term)
 where term = msum
                [((Parsec.string "any"    >> return()) <|> (oneOf "fvo" >> return ())) >> nextVar
                ,((Parsec.string "static" >> return()) <|> (oneOf "gbi" >> return ())) >> return (term0 static)
                , (>>= return . Right) <$> PrologP.var
                ]
       nextVar = getState >>= \st -> setState (st+1) >> return2 (Right (VAuto st))

parsePrologProblem fp input = either (error . show) id $ do
     things <- runParser problemParser 0 fp input
     let cc      = [c | Clause      c <- things]
         gg_txt  = [q | QueryString  q <- things]
     goals <- mapM (runParser goalParser 0 "goal") gg_txt
     return (goals, cc)

-- -------------------
-- Command Line Opts
-- -------------------

usage = "PrologSuccessPatterns - Computation of abstract success patterns using a preinterpretation\n" ++
        "USAGE: PrologSuccessPatterns [options] file.pl <goal>"

data Opts = Opts  { classpath :: [String]
                  , bddbddb_path :: [String]
                  , goal      :: Maybe (GoalF String (DatalogTerm (Expr (Abstract String))))
                  , nogoals   :: Bool
                  , mode      :: Mode
                  , problemFile :: String
                  , pl        :: Program String
                  , verbosity :: Int
                  }

defOpts = Opts { classpath = []
               , bddbddb_path = bddbddb_jar_paths
               , goal=Nothing
               , mode = Bddbddb
               , nogoals = False
               , verbosity=1

data Mode = Bddbddb | Fixpoint

getOptions = do
  args <- getArgs
  let (actions, nonOptions, errors) = getOpt Permute opts args
  case errors of
    (:){} -> putStrLn ("Error: " ++ unwords errors) >> putStrLn (usageInfo usage opts) >> exitWith (ExitFailure (-1))
    [] -> do
      opts@Opts{nogoals} <- foldl (>>=) (return defOpts) actions
      input <- maybe getContents readFile (listToMaybe nonOptions)
      let problemFile = fromMaybe "INPUT" (listToMaybe nonOptions)
          (goals, pl) = parsePrologProblem problemFile input
          goal        = if nogoals
                          then Nothing
                          else  fmap (either (error.show) id . runParser goalParser 0 "goal")
                                     (listToMaybe (drop 1 nonOptions))
                                `mplus` listToMaybe goals
      return (opts{problemFile,pl,goal}, nonOptions)


opts = [ Option "" ["bddbddb"]         (ReqArg setBddbddb "PATH") "Path to the bddbddb jar file"
       , Option "" ["cp","classpath"] (ReqArg setCP "PATHS")     "Additional classpath for the Java VM"
       , Option "b" [] (NoArg (\opts -> return opts{mode=Bddbddb}))  "Use bddbddb to compute the approximation (DEFAULT)"
       , Option "f" [] (NoArg (\opts -> return opts{mode=Fixpoint})) "Solve the fixpoint equation to compute the approximation (slower)"
       , Option "" ["nogoals","bottomup"] (NoArg setNogoals)     "Ignore any goals and force a bottom-up analysis"
       , Option "v" ["verbose"] (OptArg setVB "0-2") "Set verbosity level (default: 1)"
       , Option "h?" ["help"] (NoArg $ \_ -> putStrLn (usageInfo usage opts) >> exitSuccess) "Displays this help screen"
       ]

setCP arg opts = return opts{classpath = splitBy (== ':') arg}
setBddbddb arg opts = return opts{bddbddb_path = [arg]}
setNogoals opts = return opts{nogoals = True}
setVB arg opts = return opts{verbosity = maybe 1 read arg}

splitBy :: (a->Bool) -> [a] -> [[a]]
splitBy _ [] = []
splitBy f list =  first : splitBy f (dropWhile f rest)
  where
    (first, rest) = break f list