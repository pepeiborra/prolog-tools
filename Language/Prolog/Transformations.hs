{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances, TypeSynonymInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Language.Prolog.Transformations where

import Control.Applicative
import Control.Monad.Free
import Control.Monad.State
import Control.Monad.Writer
import Data.AlaCarte.Ppr
import Data.Foldable (Foldable, foldMap, toList)
import Data.List (nubBy, foldl', groupBy, sort, sortBy, elemIndex)
import Data.Monoid
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Traversable as T
import Data.Traversable (Traversable, sequenceA)
import Language.Prolog.Syntax
import Data.Term
import Data.Term.Rules
import Data.Term.Var
import Language.Prolog.Utils
import Text.PrettyPrint as Ppr

-- | Linealize duplicate vars using equality atoms
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

-- | The standard flattening transformation
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

data WildCard = WildCard deriving (Eq, Ord)
wildCard = return (Left WildCard)
instance Ppr WildCard           where ppr _ = text "_"

-- | Replace unused vars by wildcards
introduceWildcards :: (Ord var, Foldable f, Functor f, t ~ Free f (Either WildCard var)) =>
                      Clause'' id t -> Clause'' id t
introduceWildcards c = fmap2 (>>=f) c where
    occurrences = Map.fromListWith (+) (foldMap2 vars c `zip` repeat 1)
    f v@Right{} | Just 1 <- Map.lookup v occurrences = wildCard
    f v = return v

-- -----------------------------------------------------
-- * John Gallagher's query answer transformation
-- -----------------------------------------------------
-- Described in the paper "A bottom-up analysis toolkit"

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

queryAnswer :: (Monad mt, QueryAnswer idp :<: idp', term ~ mt (Either b Var)) =>
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
  where allvars = map (return . Right . VAuto) [1..]

queryAnswerGoal :: (Monad mt, QueryAnswer idp :<: idp', term ~ mt (Either b Var)) =>
                   GoalF idp term -> Program'' (Expr idp') term

queryAnswerGoal  (Pred g g_args)  = [Pred (query g 0 1) g_args :- [], queryAllquery g (length g_args) 0 1]


-- --------------------
-- * Abstraction
-- --------------------
-- | Abstract a set of clauses over a finite domain by using variables
{-
  The algorithm is a fixpoint computation.
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
        Pred f <$> ( filter ((>0) . length . filter isVar) . nubBy equiv' . Prelude.sequence)
                    [ maybe (zipTT !! i) (const [var' 0, var' 1]) (elemIndex i ii)
                    | i <- [0..arity-1]
                    ]
  explodeAt ii pat@(Pred f tt)
   | vv <- [v | Pure v <- select ii tt]
   = snub (Pred f <$> [ map (>>= apply vals) tt
                        | vals <- (Map.fromList . zip vv) <$> replicateM (length vv) dom])
  apply subst v = case Map.lookup v subst of
                    Just t  -> t
                    Nothing -> return v

  compress patterns = let p' = zipIt patterns in (p' ++) . filter (\c -> not (Prelude.any (`matches'` c) p'))
  zipIt = foldl' f [] . groupBy ((==) `on` (length . getVars)) . sortBy (compare `on` (length . getVars))
   where
     f acc xx = acc ++ filter (not.consequence) (snub xx) where
         consequence c = Prelude.any (`matches'` c) acc
