{-# LANGUAGE FlexibleInstances, UndecidableInstances, OverlappingInstances #-}

module TypeChecker.DeBruijn where

import Control.Applicative
import Data.Traversable

import Syntax.Internal
import TypeChecker.Monad
import TypeChecker.Monad.Heap
import Utils

class DeBruijn a where
    transform :: (Integer -> DeBruijnIndex -> TC Term') -> Integer -> a -> TC a

instance (Pointer ptr a, DeBruijn a) => DeBruijn ptr where
    transform f n = liftPtrM (transform f n)

instance DeBruijn Type' where
    transform f n t = case t of
	Pi a b	-> uncurry Pi  <$> trf (a,b)
        RPi tel a -> uncurry RPi <$> transform f n' (tel, a)
          where n' = n + fromIntegral (length tel)
	Fun a b -> uncurry Fun <$> trf (a,b)
	El t	-> El <$> trf t
	Set	-> return Set
	where
	    trf x = transform f n x

instance DeBruijn a => DeBruijn (RBind a) where
    transform f n (RBind x a) =
      RBind x <$> transform f n a

instance DeBruijn Term' where
    transform f n t = case t of
	Def f		  -> return $ Def f
	Var m		  -> f n m
	App s t		  -> uncurry App <$> trf (s,t)
	Lam t		  -> Lam <$> trf t
	where
	    trf x = transform f n x

instance (DeBruijn a, DeBruijn b) => DeBruijn (a,b) where
    transform f n (x,y) = (,) <$> transform f n x <*> transform f n y

instance DeBruijn a => DeBruijn (Abs a) where
    transform f n (Abs x b) = Abs x <$> transform f (n + 1) b

instance DeBruijn a => DeBruijn [a] where
    transform f n = traverse (transform f n)

raiseByFrom :: DeBruijn a => Integer -> Integer  -> a -> TC a
raiseByFrom k = transform f
    where
	f n m | m < n	  = return $ Var m
	      | otherwise = return $ Var (m + k)

raiseBy :: DeBruijn a => Integer -> a -> TC a
raiseBy k = raiseByFrom k 0

raise :: DeBruijn a => a -> TC a
raise = raiseBy 1

substUnder  :: DeBruijn a => Integer -> Term -> a -> TC a
substUnder n0 t = transform f n0
    where
	f n m | m < n	  = return $ Var m
	      | m == n	  = forceClosure =<< raiseByFrom (n - n0) n0 t
	      | otherwise = return $ Var (m - 1)

subst :: DeBruijn a => Term -> Abs a -> TC a
subst t = substUnder 0 t . absBody

substs :: DeBruijn a => [Term] -> a -> TC a
substs []     a = return a
substs (t:ts) a = substUnder 0 t =<< flip substs a =<< raise ts

