{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving, GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

module Language.Prolog.Transformations where

import Control.Applicative
import Control.Monad.Free
import Control.Monad.State
import Control.Monad.Writer (runWriterT, tell)
import Data.AlaCarte as Al
import Data.AlaCarte.Ppr
import Data.Foldable (Foldable(..), toList)
import Data.List (nubBy, foldl', groupBy, sort, sortBy, elemIndex, (\\))
import Data.Monoid (Monoid(..))
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Traversable as T
import Data.Traversable (Traversable, sequenceA)
import Text.PrettyPrint.HughesPJClass as Ppr
import Prelude hiding (foldr)

#ifdef DERIVE
import Data.DeriveTH
import Data.Derive.Functor
import Data.Derive.Foldable
import Data.Derive.Traversable
#endif

import Language.Prolog.Syntax
import Language.Prolog.Representation
import Language.Prolog.Utils
import Data.Term hiding (Var)
import qualified Data.Term as Family
import Data.Term.Rules
import Data.Term.Var

-- | Linealize duplicate vars using equality atoms
flattenDupVarsC :: (Traversable t, Monad t, Ord var, Family.Var m ~ var, MonadVariant m) => (var -> Bool) -> Clause'' id (t var) -> m(Clause'' id (t var))
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
          v' <- lift $ renaming v
          modify (Set.insert v')
          let res = return v'
          tell [return v :=: res]
          return res

-- | The standard flattening transformation (see e.g. Bosco & Giovanetti 'Narrowing vs SLD Resolution')
--   Receives a clause and a scheme to flatten compound terms, and outputs the flattened clause
--flattenC :: (Traversable f, Traversable t, MonadVariant v m) =>
  --            (Free f v -> v -> t (Free f v)) -> ClauseF (t (Free f v)) -> m(ClauseF (t (Free f v)))
flattenC box clause@(h :- b) = do
    (h' :- b', goals) <- runWriterT (mapM2 flattenTerm clause)
    return (h' :- (goals ++ b'))
  where
  flattenTerm  = evalFree return2 f
  f t = do
    v <- freshVar
    t' <- T.mapM flattenTerm t
    tell [box (Impure t') v]
    return2 v

-- | Replace unused vars by wildcards
introduceWildcards :: (Ord var, Foldable f, Functor f, t ~ Free f (Either WildCard var)) =>
                      Clause'' id t -> Clause'' id t
introduceWildcards c = fmap2 (>>=f) c where
    occurrences = Map.fromListWith (+) (foldMap2 vars c `zip` repeat (1::Int))
    f v@Right{} | Just 1 <- Map.lookup v occurrences = wildCard
    f v = return v

-- -----------------------------------------------------
-- * John Gallagher's query answer transformation
-- -----------------------------------------------------
-- Described in the paper "A bottom-up analysis toolkit"

data QueryAnswer a = QueryAll a | Query a Int Int | Answer a deriving (Eq,Ord,Show)

answer, queryAll :: (QueryAnswer :<: f) => Expr f -> Expr f
query :: (QueryAnswer :<: f) => Expr f -> Int -> Int -> Expr f

answer       = inject . Answer
queryAll     = inject . QueryAll
query id i j = inject (Query id i j)

isAnswer (Al.match -> Just Answer{}) = True; isAnswer _ = False

{-  Example.
 Original program:
 p([x|y]) :- q(x), r(y).
 q(a).
 q(b).
 r(a).

 Result:
 answer_r(a) <- call_r(a).
 answer_q(a) <- call_q(a).
 answer_q(b) <- call_q(b).
 answer_p(x) <- call_p(x), answer_q(x), answer_r(x).
 call_1_1_q(x) <- call_p([x|_]).
 call_q(x)     <- call_1_1_q(x).
 call_1_2_r(y) <- call_p([_|y]), answer_q(x).
 call_r(y)     <- call_1_2_r(y).
-}

queryAnswer :: (term ~ m var, Enum var, Functor idp, Monad m) =>
                   Program'' (Expr idp) term -> Program'' (Expr (QueryAnswer :+: idp)) term
queryAnswer pgm = concatMap (uncurry queryF) (zip [1..] pgm_qa) ++ map answerF pgm_qa
 where
  pgm_qa = mapPredId (foldExpr (In . Inr)) <$$> pgm
  answerF (Pred h h_args :- cc) =
      Pred (answer h) h_args :- ( Pred (queryAll h) h_args :
                                [ Pred (answer c) c_args | Pred c c_args <- cc ])
  queryF _ (_ :- []) = []
  queryF i (Pred h h_args :- cc@(Pred b0 b0_args :_)) =

      -- call_i_1_q(x) :- call_p([x|_]).
      Pred (query b0 i 1) b0_args :- [querySome h h_args] :

      -- call_q(x) :- call_i_1_q(x).
      queryAllquery b0 (length b0_args) 0 i 1           :

     concat
     [[-- call_i_j_r(y) :- call_p([x|_]), answer...
        Pred (query bj i j)  bj_args :- ([Pred (answer c) c_args | Pred c c_args <- bleft] ++
                                       [querySome h h_args])
       -- call_r(y) :- call_i_j_r(y).
      , queryAllquery bj (length bj_args) 0 i j]
         | (j,(bleft, Pred bj bj_args :_)) <- zip [2..] (map (`splitAt` cc)  [1..length cc - 1])]

querySome p args = Pred (queryAll p) args
queryAllquery h ar1 ar2 i j = Pred (queryAll h) vars2 :- [Pred (query h i j) vars1]
  where allvars = map (return . toEnum)  [1..]
        vars1   = take (ar1 + ar2) allvars
        vars2   = take ar1 $ drop ar2 allvars

queryAnswerGoal :: (term ~ mt var, Enum var, Monad mt, Functor idp) =>
                   Clause'' (Expr idp) term -> Program'' (Expr (QueryAnswer :+: idp)) term

queryAnswerGoal  (Pred g g_args :- cc) = [ Pred (query g' 0 1) g_args :- cc'
                                          , queryAllquery g' (length g_args) 0 0 1]
 where g'  = foldExpr (In . Inr) g
       cc' = mapPredId (foldExpr (In . Inr)) <$> cc

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

compress patterns cc = zipIt [] (patterns ++ cc)
 where
  zipIt acc [] = acc
  zipIt acc (x:xx)
    | consequence x (xx ++ acc)  = zipIt acc xx
    | otherwise                  = zipIt (x:acc) xx
   where
     consequence c cc = Prelude.any (`matches'` c) cc
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

#ifdef DERIVE
$(derive makeFunctor     ''QueryAnswer)
$(derive makeFoldable    ''QueryAnswer)
$(derive makeTraversable ''QueryAnswer)
#else
deriving instance Functor QueryAnswer
deriving instance Foldable QueryAnswer
deriving instance Traversable QueryAnswer
#endif

instance PprF QueryAnswer where
    pprF (Answer   id)  = text "answer_" <> id
    pprF (QueryAll id)  = text "query_"  <> id
    pprF (Query id i j) = text "query_"  <> Ppr.int i <> text "_" <> Ppr.int j <> text "_" <> id
