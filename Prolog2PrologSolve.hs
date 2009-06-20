{-# LANGUAGE ViewPatterns #-}

import Control.Applicative hiding ((<|>), many)
import Control.Monad.Error
import Data.List
import Data.Maybe
import qualified Data.Set as Set
import Language.Prolog.Parser as Prolog (program, query, clause, whiteSpace)
import Language.Prolog.Syntax as Prolog
import Language.Prolog.Signature
import System.Environment
import Text.ParserCombinators.Parsec
import Text.PrettyPrint (text)

import Data.Term.Rules

instance Error ParseError

main = do
   [fp]     <- getArgs
   contents <- readFile fp
   case translate fp contents of
     Left err -> error err
     Right (pgm, goal) -> putStrLn (show(ppr pgm) ++
                                    "\n%query: " ++ show (ppr goal) ++ "\n")

translate :: FilePath -> String -> Either String (Program String, TermF String Mode)
translate fp txt = do
  things <- mapLeft show $ parse problemP fp txt
  let pgm      = [c | Clause c <- things]
      qq_txt   = [q | QueryString q <- things]
  queries1 <- mapLeft show $ mapM goalToGoal (concat [q | Query q <- things])
  queries2 <- mapLeft show $ mapM parseGoal qq_txt
  case queries1 ++ queries2 of
        [Term goal_f tt] -> do
            let sig = getSignature pgm
                findFreeSymbol :: String -> String
                findFreeSymbol pre = fromJust $ find (`Set.notMember` allSymbols sig) (pre : [pre ++ show i | i <- [0..]])
                [solveF, clauseF, goalF, trueF, equalsF] = map findFreeSymbol ["solve", "clause", "goal", "true", "equal"]
                solveP arg    = Pred solveF [arg]
                clauseP a1 a2 = Pred clauseF [a1,a2]
                trueT         = term trueF []
                tupleT x y    = term "" [x,y]
                (x,y)         = (var "X", var "Y")
                transformClause (h :- (filter (not.isCut) -> [])) = clauseP (transformPred h) trueT :- []
                transformClause (h :- (filter (not.isCut) -> cc)) = clauseP (transformPred h) (transformPreds cc) :- []
                transformPred   (Pred f tt) = term f tt
                transformPred   (Is f g)    = term equalsF [f, g]
                transformPred   (f :=: g)   = term equalsF [f, g]
                transformPreds              = foldl1 tupleT . map transformPred . filter (not.isCut)
                solveClauses = [ solveP trueT :- []
                               , solveP (tupleT x y) :- [solveP x, solveP y]
                               , solveP x :- [clauseP x y , solveP y]]
                goalClause   = let myvars = take (length tt) vars
                                   vars   = map (var.(:[])) ['A'..'Z']
                               in [Pred goalF myvars :- [solveP (term goal_f myvars)]]
                goal'        = Term goalF tt
                pgm'         = map transformClause pgm ++ solveClauses ++ goalClause
            return (pgm', goal')
        _ -> fail "Expected one and only one query"
  where
        goalToGoal (Prolog.Pred f tt) = Term f <$> (parse modesP "" $ unwords $ map (show . ppr) $ tt)

isCut Cut = True; isCut _ = False

data Mode = G|V
instance Show Mode where show G = "b"; show V = "f"
instance Ppr Mode where ppr = text . show

--parseGoal :: String -> Either ParseError Goal
parseGoal = parse p "" where
    ident = many1 (alphaNum <|> oneOf "!+_-./<>=?\\/^")
    mode  = (oneOf "gbi" >> return G) <|> (oneOf "vof" >> return V)
    parens= between (char '(') (char ')')
    p = do
      spaces
      id <- ident
      modes <- parens (mode `sepBy` char ',')
      return (Term id modes)

modesP = modeP `sepBy` char ','
modeP = (oneOf "gbi" >> return G) <|> (oneOf "vof" >> return V)

data PrologSection = Query [Goal String] | Clause (Clause String) | QueryString String

problemP = do
  txt <- getInput
  let !queryComments = map QueryString $ catMaybes $ map findQuery (lines txt)
  res <- Prolog.whiteSpace >> many (Clause <$$> Prolog.clause <|> Query <$$> Prolog.query)
  return (concat res ++ queryComments)
  where findQuery ('%'    :'q':'u':'e':'r':'y':':':' ':goal) = Just $ goal
        findQuery ('%':' ':'q':'u':'e':'r':'y':':':' ':goal) = Just $ goal
        findQuery ('%'    :'q':'u':'e':'r':'y':':':goal) = Just $ goal
        findQuery ('%':' ':'q':'u':'e':'r':'y':':':goal) = Just $ goal
        findQuery _ = Nothing
        (<$$>) = fmap . fmap

mapLeft :: (l -> l') -> Either l r -> Either l' r
mapLeft f (Left x)  = Left(f x)
mapLeft f (Right r) = Right r