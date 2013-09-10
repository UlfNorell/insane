{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies,
             DeriveDataTypeable, DeriveFunctor, DeriveFoldable,
             DeriveTraversable #-}
module Syntax.Internal where

import Control.Applicative
import Data.Traversable
import Data.Typeable
import Data.Foldable

import qualified Syntax.Abs as Abs
import Utils

-- Pointers ---------------------------------------------------------------

newtype Ptr = Ptr Integer
    deriving (Eq, Ord)

instance Show Ptr where
    show (Ptr n) = "*" ++ show n

newtype Type	 = TypePtr   Ptr deriving (Eq, Typeable)
newtype Term	 = TermPtr   Ptr deriving (Eq, Typeable)
newtype Clause	 = ClausePtr Ptr deriving (Eq, Typeable)
newtype Pair a b = PairPtr   Ptr deriving (Eq, Typeable)
newtype Unit     = UnitPtr   Ptr deriving (Eq, Typeable)

class (Show ptr, Eq ptr, Show a, Typeable a) => Pointer ptr a | ptr -> a, a -> ptr where
    toRawPtr   :: ptr -> Ptr
    fromRawPtr :: Ptr -> ptr

instance Pointer Unit ()          where toRawPtr (UnitPtr p)   = p; fromRawPtr = UnitPtr
instance Pointer Type Type'	  where toRawPtr (TypePtr p)   = p; fromRawPtr = TypePtr
instance Pointer Term Term'	  where toRawPtr (TermPtr p)   = p; fromRawPtr = TermPtr
instance Pointer Clause Clause'   where toRawPtr (ClausePtr p) = p; fromRawPtr = ClausePtr
instance (Show a, Show b, Typeable a, Typeable b) =>
	 Pointer (Pair a b) (a,b) where
    toRawPtr (PairPtr p)   = p
    fromRawPtr = PairPtr

instance Show Type	 where show = show . toRawPtr
instance Show Term	 where show = show . toRawPtr
instance Show Clause	 where show = show . toRawPtr
instance Show (Pair a b) where show (PairPtr p) = show p
instance Show Unit       where show = show . toRawPtr

-- Syntax -----------------------------------------------------------------

type Arity = Int

data Definition
	= Axiom Name Type
	| Defn  Name Type [Clause]
	| Data  Name Type [Constructor]
	| Cons  Name Type
    deriving (Show, Typeable)

data Clause' = Clause [Pattern] Term
    deriving (Show, Typeable)

data Constructor = Constr Name Arity
    deriving (Show, Typeable)

data Pattern = VarP Name
	     | ConP Name [Pattern]
    deriving (Show, Typeable)

type Name	   = String
type DeBruijnIndex = Integer

type Telescope = [RBind Type]
data RBind a = RBind String a
  deriving (Show)

data Type' = Pi Type (Abs Type)
           | RPi Telescope Type
	   | Fun Type Type
	   | El Term
	   | Set
    deriving (Show, Typeable)

data Term' = Lam (Abs Term)
	   | App Term Term
	   | Var DeBruijnIndex
	   | Def Name
    deriving (Show, Typeable)

data Abs a = Abs { absName :: Name, absBody :: a }
    deriving (Typeable, Functor, Foldable, Traversable)

instance Show a => Show (Abs a) where
    show (Abs _ b) = show b

