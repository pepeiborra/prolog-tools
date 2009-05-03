{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}

import Control.Monad
import Language.Prolog.Parser (program)
import Language.Prolog.PreInterpretation
import Language.Prolog.Semantics (eval,debug)
import Language.Prolog.Signature
import Language.Prolog.Syntax
import System.Environment
import Text.ParserCombinators.Parsec (parseFromFile)
import Text.PrettyPrint
import Data.AlaCarte
import Data.Monoid hiding (Any)
import qualified Data.Set as Set

import Prelude hiding (pred)

type Concrete = PrologTerm String
type Abstract = Static :+: Any :+: Compound :+: PrologT :+: T String :+: V

main = do
  (fp:rest) <- getArgs
  Right pl <- parseFromFile program fp
  let mkPre :: MkPre Concrete Abstract = staticAny1
  case rest of
    [] -> do
         let ((dom,_), pl0 :: Program'' (AbstractPred String (Expr (PrologTerm String))) (TermDset Abstract) ) = getAbstractComp mkPre pl
         putStrLn "We compute the following compiled abstraction:"
         print (ppr pl0)
         putStrLn "the Preinterpretation domain is: "
         print (ppr dom)
    ["cooked"] -> do
         let pl' = prepareProgram pl
         putStrLn "We compute the following (cooked) compiled abstraction:"
         let (pre@(dom',_), pl') = getCookedAbstractComp pl
         print (ppr pl')
         putStrLn "the Preinterpretation domain is: "
         print (ppr dom')
    ["success"] -> do
         putStrLn "We obtain the success patterns:"
         print (getSuccessPatterns mkPre pl :: Interpretation String (ObjectSet Abstract))
    ["success","cooked"] -> do
         putStrLn "We obtain the (cooked) success patterns:"
         print (getCookedSuccessPatterns pl)

