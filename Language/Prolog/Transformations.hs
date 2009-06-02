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

data WildCard = WildCard deriving (Enum, Eq, Ord, Bounded)
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

queryAnswer :: (Enum var, Monad mt, QueryAnswer idp :<: idp', term ~ mt var) =>
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
     | (j,(bleft, Pred bj bj_args :_)) <- zip [2..] (map (`splitAt` cc)  [1..length cc - 1])]

queryAllquery h ar i j = let vars = take ar allvars in Pred (queryAll h) vars :- [Pred (query h i j) vars]
  where allvars = map (return . toEnum)  [1..]

queryAnswerGoal :: (Enum var, Monad mt, QueryAnswer idp :<: idp', term ~ mt var) =>
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
 where
  zipIt = foldl' f [] . groupBy ((==) `on` numVars) . sortBy (compare `on` numVars)
   where
     numVars = length . getVars
     f acc xx = acc ++ filter (not.consequence) (nubBy equiv' xx) where
         consequence c = Prelude.any (`matches'` c) acc

-- -------------------------
-- Additional instances
-- -------------------------
-- Enum instance for Either
instance (Enum a, Bounded a, Enum b, Bounded b) => Enum (Either a b) where
  toEnum i
      | i > minB * 2 = if minB == ma then Right (toEnum (i - minB))
                                     else Left  (toEnum (i - minB))
      | even i    = Right (toEnum (i `div` 2))
      | otherwise = Left  (toEnum (i `div` 2))
   where minB = min ma mb
         ma   = fromEnum (maxBound :: a)
         mb   = fromEnum (maxBound :: b)
  fromEnum (Right x)
      | fx < ma =  fx * 2
      | otherwise = ma + fx
   where fx = fromEnum x
         ma = fromEnum (maxBound :: a)
  fromEnum (Left x)
      | fx < mb =  fx * 2 + 1
      | otherwise = mb + fx
   where fx = fromEnum x
         mb = fromEnum (maxBound :: b)

-- Bounded instance for Var
instance Bounded Var where minBound = VAuto minBound; maxBound = VAuto maxBound