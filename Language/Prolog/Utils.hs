{-# LANGUAGE NoMonomorphismRestriction #-}
module Language.Prolog.Utils where

import Control.Applicative
import qualified Data.Set as Set
import Data.List (sort)
import Data.Foldable as F (Foldable, foldMap, foldr, toList)
import Data.Traversable as T
import Data.Monoid


dec2bin :: Int -> [Bool]
dec2bin i | i < 0 = error "no entiendo numeros negativos"
dec2bin i = go [] i where
  go acc 0 = acc
  go acc i = go ((i `mod` 2 /= 0) : acc) (i `div` 2)

(t?:f) b = if b then t else f

return2       = return.return
mapM2         = T.mapM . T.mapM
mapM3         = T.mapM . T.mapM . T.mapM
fmap2         = fmap.fmap
fmap3         = fmap.fmap.fmap
(<$$>)        = fmap2
(<$$$>)       = fmap3
(<$$$$>)      = fmap.fmap.fmap.fmap
foldMap2      = foldMap.foldMap
foldMap3      = foldMap.foldMap.foldMap
foldMapM f    = fmap(F.foldr mappend mempty) . T.mapM f
foldMapM2     = foldMapM . foldMapM

isLeft Left{} = True; isLeft _ = False
fixEq f x | fx <- f x = if fx == x then x else fixEq f fx
snub = Set.toList . Set.fromList
on cmp f x y = cmp (f x) (f y)
zipAll = getZipList . sequenceA . map ZipList

(f .&. g) x  = f x && g x

combinations :: [a] -> [[a]]
combinations [] = [[]]
combinations (x:xs)
    = combinations xs ++ [ x:xs' | xs' <- combinations xs ]


select :: (Ord t, Num t, Foldable f) => [t] -> f a ->[a]
select ii xx = go 0 (toList xx) (sort ii)
    where go _ [] _ = []
          go _ _ [] = []
          go n (x:xx) (i:ii) | n == i = x : go (n+1) xx ii
                             | otherwise = go (n+1) xx (i:ii)
