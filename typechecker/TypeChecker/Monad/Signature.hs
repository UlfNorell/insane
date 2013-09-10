
module TypeChecker.Monad.Signature where

import Control.Monad.State
import qualified Data.Map as Map

import Syntax.Internal
import TypeChecker.Monad
import TypeChecker.Monad.Heap

setSig :: Signature -> TC ()
setSig sig = modify $ \s -> s { stSig = sig }

getSig :: TC Signature
getSig = gets stSig

getDefinition :: Name -> TC Definition
getDefinition x = do
    sig <- getSig
    case Map.lookup x sig of
	Just d	-> return d
	Nothing	-> fail $ "not a defined name " ++ x

withDefinition :: Name -> (Definition-> TC a) -> TC a
withDefinition x f = f =<< getDefinition x

addConstraint :: TC () -> TC ()
addConstraint c = do
  p <- suspend c
  modify $ \s -> s { stConstraints = p : stConstraints s }

defType :: Name -> TC Type
defType x = withDefinition x $ \d ->
    case d of
	Axiom _ t   -> return t
	Defn _ t _  -> return t
	Data _ t _  -> return t
	Cons _ t    -> return t

isConstructor :: Name -> TC ()
isConstructor x = withDefinition x $ \d ->
    case d of
	Cons _ _ -> return ()
	_	 -> fail $ x ++ " should be a constructor"

isData :: Name -> TC ()
isData x = withDefinition x $ \d ->
    case d of
	Data _ _ _ -> return ()
	_	   -> fail $ x ++ " should be a datatype"

functionArity :: Name -> TC (Maybe Arity)
functionArity x = withDefinition x $ \d ->
    case d of
	Defn _ _ (c:_) -> do
	    Clause ps _ <- forceClosure c
	    return $ Just $ length ps
	_ -> return Nothing

