{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}

--import Control.Monad.Exception
import Control.Exception
import Control.Monad
import Control.Monad.Free
import Data.Array
import Data.List (sort, groupBy)
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Language.Prolog.Parser (program)
import Language.Prolog.PreInterpretation
import Language.Prolog.Semantics (eval,debug)
import Language.Prolog.Signature
import Language.Prolog.Syntax
import System.Directory
import System.Environment
import System.Exit
import System.IO
import System.Cmd
import System.FilePath
import Text.ParserCombinators.Parsec (parseFromFile)
import Text.PrettyPrint
import Data.AlaCarte
import Data.Monoid hiding (Any)
import qualified Data.Set as Set

import Prelude hiding (pred)

type Concrete = PrologTerm String
type Abstract = NotVar :+: Any :+: Compound :+: PrologT :+: T String :+: V

deriving instance Ord f => Ord (ClauseF f)

echo = hPutStrLn stderr

bddbddb_jar_paths = ["bddbddb-full.jar", "bddbddb.jar"]

main = do
  (fp:rest) <- getArgs
  Right pl <- parseFromFile program fp
  let mkPre :: MkPre Concrete Abstract = notvarAny1
  case rest of
    []                              -> run_bddbddb pl fp bddbddb_jar_paths
    ["bddbddb"]                     -> run_bddbddb pl fp bddbddb_jar_paths
    ("bddbddb" : bddbddb_jar_paths) -> run_bddbddb pl fp bddbddb_jar_paths
    ["dfta"] -> do
         let ((dom,_), pl0 :: AbstractDatalogProgram' String String Abstract) = getAbstractComp mkPre pl
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
         print (getSuccessPatterns mkPre pl :: Interpretation String (ObjectSet Abstract))
    ["success","cooked"] -> do
         echo "We obtain the (cooked) success patterns:"
         print (getCookedSuccessPatterns' pl)
    ["success","cookedslowly"] -> do
         echo "We obtain the (slowly cooked) success patterns:"
         print (getCookedSuccessPatterns pl)

run_bddbddb pl fp bdd_paths = do
         bddbddb_jar <- findBddJarFile bdd_paths
         let pl' = prepareProgram pl
             PrologSig constructors predicates = getPrologSignature1 pl'
             (dom, _, denotes, clauses) = abstractCompilePre' pl

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
             [ text c <> parens (hsep $ punctuate comma $ replicate a (text "arg : D"))
                        <+>  text "outputtuples"
                    | (c,a) <- Map.toList predicates]
         dump_bddbddb "notAny (arg : D) inputtuples"
         let domainDict = Map.fromList (dom `zip` [(0::Int)..])

         withTempFile' (takeDirectory fp) "notAny.tuples" $ \notanyfp notanyh -> do
         echo ("writing facts for notAny in file " ++ notanyfp )
         hPutStrLn notanyh $ unlines (("# D0: " ++ show domsize) : [ show i | i <- [1..domsize - 1]])
         hClose notanyh

         -- Rules
         dump_bddbddb "\n### Rules\n"
         let dom_cc = foldFree return toId <$$$> (clauses ++ denotes)
             toId (T f) | Just i <- Map.lookup f domainDict = term0 i
         dump_bddbddb (show $ ppr dom_cc)

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
            results <- forM (Map.toList predicates) $ \(p,i) -> do
                         echo ("Processing file " ++ p ++ ".tuples")
                         let fp_result = (takeDirectory fp </> p <.> "tuples")
                         output <- readFile fp_result
                         evaluate (length output)
                         removeFile fp_result
                         return [ Pred p (map (domArray!) ii)
                                  | ii <- map (map read . words) (tail $ lines output)
                                  , all  (< domsize) ii]
            echo "bddbddb produced the following success patterns:"
            print (vcat $ map ppr $ concat results)

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