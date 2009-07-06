{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}
{-# LANGUAGE NamedFieldPuns, RecordWildCards, DisambiguateRecordFields #-}
{-# LANGUAGE CPP #-}

#ifdef GHCI
#define THIS PrologSuccessPatterns
#else
#define THIS Main
#endif

module THIS where

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
import Data.Term.Rules
import Data.Term.Var
import qualified Data.Map as Map
import qualified Data.Set as Set
--import Data.Traversable as T hiding (forM)
import Language.Prolog.Parser as Prolog (program)
import qualified Language.Prolog.Parser as PrologP
import Language.Prolog.PreInterpretation
import Language.Prolog.Representation
import Language.Prolog.Semantics (eval)
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
import Text.ParserCombinators.Parsec (Parser, ParseError, getState, setState, runParser, parseFromFile, parse, oneOf)
import qualified Text.ParserCombinators.Parsec as Parsec
import Text.PrettyPrint hiding (Mode(..),mode)

import qualified Prelude
import Prelude hiding (pred, any, or)

import Debug.Trace

type Concrete = PrologTerm String
type Abstract idt = Any :+: NotVar :+: Compound :+: PrologTerm idt


instance Error ParseError

echo = hPutStrLn stderr

bddbddb_jar_paths = ["bddbddb-full.jar", "bddbddb.jar"]

main = do
  (opts@Opts{..}, nonOpts) <- getOptions
  case mode of
    Bddbddb -> run_bddbddb opts
{-
    Fixpoint -> do
         echo "We obtain the success patterns:"
         let mkPre :: MkPre Concrete (FreeArg :+: Abstract String) = notvarAny1
             sig_pl = getSignature pl'
             pl'    = queryAnswer $ prepareProgram pl
             mkPre  = notvarAny1 sig_pl
         getSuccessPatterns' pl'
-}
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

type P = NotAny :+: T String :+: PrologP
type A = NotVar :+: Compound :+: Any :+: PrologTerm String

run_bddbddb Opts{..} = do
  let mb_goal' = uncurry abstractCompileGoal <$> mb_goal
  let opts :: ComputeSuccessPatternsOpts P A
      opts =  ComputeSuccessPatternsOpts{depth, verbosity, debug, fp = problemFile
                                         ,bddbddb_path, mb_goal = mb_goal', pl, smart}
  (dom, results) <- computeSuccessPatterns opts
  echo "bddbddb produced the following success patterns:\n"
  print (vcat $ map ppr $ concat results)
  when simplify $ do
    echo " \nWe can simplify the patterns as follows:\n"
--  let zipped_results = abstract (term0 <$> dom) <$> results
    let zipped_results = abstractAnys any <$> results
    print (vcat $ map ppr $ concat zipped_results)

-- ---------------

-- --------------------------
-- Parsing Prolog problems
-- --------------------------
data PrologSection = QueryProgram [Goal String] | Clause (Prolog.Clause String) | QueryString String

problemParser = do
  txt <- Parsec.getInput
  let !queryComments = map QueryString $ catMaybes $ map f (lines txt)
  res <- PrologP.whiteSpace >> concat <$> many (Clause <$$> PrologP.clause <|> QueryProgram <$$> PrologP.query)
  return (res ++ queryComments)
  where f ('%'    :'q':'u':'e':'r':'y':':':goal) = Just goal
        f ('%':' ':'q':'u':'e':'r':'y':':':goal) = Just goal
        f _ = Nothing

goalParser :: Parser (String,[Bool])
goalParser = PrologP.whiteSpace >> (,) <$> PrologP.ident <*> PrologP.parens (PrologP.commaSep1 term)
 where term = msum
                [((Parsec.string "any"    >> return()) <|> (oneOf "fvo" >> return ())) >> return False
                ,((Parsec.string "static" >> return()) <|> (oneOf "gbi" >> return ())) >> return True
                , (PrologP.var :: Parser (Prolog.Term String)) >> return False
                ]

parsePrologProblem fp input = either (error . show) id $ do
     things <- parse problemParser fp input
     let cc      = [c | Clause      c <- things]
         gg_txt  = [q | QueryString  q <- things]
     goals <- mapM (parse goalParser "goal") gg_txt
     return (goals, cc)

-- -------------------
-- Command Line Opts
-- -------------------

usage = "PrologSuccessPatterns - Computation of abstract success patterns using a preinterpretation\n" ++
        "USAGE: PrologSuccessPatterns [options] file.pl <goal>"

data Opts = Opts  { classpath :: [String]
                  , bddbddb_path :: [String]
                  , mb_goal   :: Maybe (String,[Bool])
                  , depth     :: Int
                  , nogoals   :: Bool
                  , mode      :: Mode
                  , problemFile :: String
                  , pl        :: Program String
                  , verbosity :: Int
                  , debug     :: Bool
                  , simplify  :: Bool
                  , smart     :: Bool
                  }

defOpts = Opts { classpath    = []
               , bddbddb_path = bddbddb_jar_paths
               , mb_goal      = Nothing
               , mode         = Bddbddb
               , nogoals      = False
               , verbosity    = 1
               , debug        = False
               , simplify     = False
               , smart        = False
               , depth        = 1
               }

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
          (goals, the_pl) = parsePrologProblem problemFile input
          the_goal = if nogoals
                          then Nothing
                          else  fmap (either (error.show) id . parse goalParser "goal")
                                     (listToMaybe (drop 1 nonOptions))
                                `mplus` listToMaybe goals
      return (opts{problemFile,THIS.pl=the_pl,THIS.mb_goal=the_goal}, nonOptions)


opts = [ Option "" ["bddbddb"]         (ReqArg setBddbddb "PATH") "Path to the bddbddb jar file"
       , Option "d" ["depth"]          (ReqArg setDepth "NUM") "Depth of the approximation (default: 1)"
       , Option "" ["cp","classpath"]  (ReqArg setCP "PATHS")     "Additional classpath for the Java VM"
       , Option "b" [] (NoArg (\opts -> return opts{mode=Bddbddb}))  "Use bddbddb to compute the approximation (DEFAULT)"
       , Option "f" [] (NoArg (\opts -> return opts{mode=Fixpoint})) "Solve the fixpoint equation to compute the approximation (slower)"
       , Option ""  ["nogoals","bottomup"] (NoArg setNogoals)     "Ignore any goals and force a bottom-up analysis"
       , Option "v" ["verbose"] (OptArg setVB "0-2") "Set verbosity level (default: 1)"
       , Option ""  ["debug"] (NoArg (\opts -> return opts{THIS.debug=True})) "Do not delete intermediate files"
       , Option "s" ["simplify"] (NoArg (\opts -> return opts{THIS.simplify=True})) "Simplify the patterns returned"
       , Option ""  ["smart"] (NoArg (\opts -> return opts{THIS.smart=True})) "Be smart by creating a custom abstract domain"
       , Option "h?" ["help"] (NoArg $ \_ -> putStrLn (usageInfo usage opts) >> exitSuccess) "Displays this help screen"
       ]

setCP arg opts = return opts{classpath = splitBy (== ':') arg}
setBddbddb arg opts = return opts{THIS.bddbddb_path = [arg]}
setNogoals opts = return opts{nogoals = True}
setVB arg opts = return opts{THIS.verbosity = maybe 1 read arg}
setDepth arg opts = return opts{THIS.depth = read arg}

splitBy :: (a->Bool) -> [a] -> [[a]]
splitBy _ [] = []
splitBy f list =  first : splitBy f (dropWhile f rest)
  where
    (first, rest) = break f list