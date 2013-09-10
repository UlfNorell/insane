{-# LANGUAGE FlexibleInstances, UndecidableInstances, OverlappingInstances #-}

module TypeChecker.Force where

import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Error
import Data.Traversable
import qualified Data.Map as Map

import Syntax.Internal
import TypeChecker.Monad
import TypeChecker.Monad.Heap
import TypeChecker.Monad.Signature
import Utils

traverse_ f x = () <$ traverse f x

-- | Force the checking of everything in the signature
forceSig :: TC ()
forceSig = do
    sig <- getSig
    force $ Map.elems sig
    cs  <- getConstraints
    force cs

class Force a where
    force :: a -> TC ()

instance Force Definition where
    force (Axiom _ t)   = force t
    force (Defn _ t cs) = force (t,cs)
    force (Data _ t _)	= force t
    force (Cons _ t)	= force t

instance (Pointer ptr a, Force a) => Force ptr where
    force p = do
      f <- howForceful
      let gloves = case f of
            Hard -> id
            Soft -> flip catchError $ \_ -> return ()
      gloves $ force =<< forceClosure p

instance Force () where
  force () = return ()

instance Force Clause' where
    force c =
	case c of
	    Clause ps t -> force t

instance Force Type' where
    force a =
	case a of
	    Pi a b    -> force (a,b)
            RPi tel a -> force (tel, a)
	    Fun a b   -> force (a,b)
	    Set       -> return ()
	    El t      -> force t

instance Force a => Force (RBind a) where
  force (RBind _ a) = force a

instance Force Term' where
    force t =
	case t of
	    Var n   -> return ()
	    Def c   -> return ()
	    App s t -> force (s,t)
	    Lam t   -> force t

instance (Force a, Force b) => Force (a,b) where
    force (x,y) = force x >> force y

instance Force a => Force (Abs a) where
    force = traverse_ force

instance Force a => Force [a] where
    force = traverse_ force

