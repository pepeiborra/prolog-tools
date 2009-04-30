{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE TypeOperators, ScopedTypeVariables #-}

import Language.Prolog.PreInterpretation
import Text.ParserCombinators.Parsec (parseFromFile)
import Language.Prolog.Parser (program)
import Language.Prolog.Semantics (eval,debug)
import Language.Prolog.Syntax
import System.Environment
import Text.PrettyPrint
import Data.AlaCarte

type Concrete = V :+: Peano :+: Tup :+: T String
type Abstract = Any :+: Static :+: Compound :+: V :+: Peano :+: T String :+: Tup

main = do
  [mode,fp] <- getArgs
  Right pl <- parseFromFile program fp
  let mkPre :: MkPre Concrete Abstract = staticAny1
  let ((dom,_), pl0 :: Program'' (AbstractPred String) (TermD Abstract)) = getAbstractComp mkPre pl
  putStrLn "We compute the following compiled abstraction:"
  print (ppr pl0)
  putStrLn "the Preinterpretation domain is: "
  print (ppr dom)
  putStrLn "We obtain the success patterns:"
  let successPats
       | mode == "0" = show (getSuccessPatterns  mkPre pl :: Interpretation String (Object Abstract))
       | otherwise   = show (getSuccessPatterns' mkPre pl :: Interpretation (AbstractPred String) (TermD Abstract))
  putStrLn successPats

