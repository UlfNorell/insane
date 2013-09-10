
module TypeChecker.Monad.Heap where

import Control.Applicative
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Error
import qualified Data.Map as Map
import Data.Typeable

import TypeChecker.Monad
import Syntax.Internal
import Utils.Monad

---------------------------------------------------------------------------
-- * Helpers
---------------------------------------------------------------------------

typeOfCl :: Typeable a => Closure a -> TypeRep
typeOfCl = typeOf . unCl
    where
	unCl :: Closure a -> a
	unCl = undefined

---------------------------------------------------------------------------
-- * Heap manipulation
---------------------------------------------------------------------------

heapLookup :: Pointer ptr a => ptr -> Heap -> Closure a
heapLookup = aux undefined
    where
	aux :: Pointer ptr a => a -> ptr -> Heap -> Closure a
	aux x ptr heap = either error id $ do
	    HpObj cl <- Map.lookup p heap `err` ("bad pointer: " ++ show p)
	    gcast cl `err` unlines
			[ "bad type in closure:"
			, "expected " ++ show (typeOf x)
			, "found    " ++ show (typeOfCl cl)
			]
	    where
		p = toRawPtr ptr

		err Nothing s  = fail s
		err (Just x) _ = return x

heapUpdate :: Pointer ptr a => ptr -> Closure a -> Heap -> Heap
heapUpdate ptr cl = Map.insert p (HpObj cl)
    where
	p = toRawPtr ptr

---------------------------------------------------------------------------
-- * Monadic functions
---------------------------------------------------------------------------

getHeap :: TC Heap
getHeap = gets stHeap

setHeap :: Heap -> TC ()
setHeap = modHeap . const

modHeap :: (Heap -> Heap) -> TC ()
modHeap f = modify $ \s -> s { stHeap = f $ stHeap s}

getClosure :: Pointer ptr a => ptr -> TC (Closure a)
getClosure p = heapLookup p <$> getHeap

setClosure :: Pointer ptr a => ptr -> Closure a -> TC ()
setClosure p cl = modHeap $ heapUpdate p cl

-- | Returns the new closure
modClosure :: Pointer ptr a => (Closure a -> TC (Closure a)) -> ptr -> TC (Closure a)
modClosure f p = do
    cl  <- getClosure p
    case getActive cl of
      Active -> fail "<<Loop>>"
      _ -> do
        setClosure p $ setActive Active cl
        cl' <- f cl
        setClosure p $ setActive Inactive cl'
        return cl'

forceClosure :: Pointer ptr a => ptr -> TC a
forceClosure p = do
    Evaluated x <- modClosure eval p
    return x
    where
	eval cl@(Evaluated _) = return cl
	eval (Unevaluated m)  = do
	    x <- runTCClosure m
	    return (Evaluated x)

freshPtr :: Pointer ptr a => TC ptr
freshPtr = do
    Ptr n <- gets stNextFree
    modify $ \s -> s { stNextFree = Ptr (n + 1) }
    return $ fromRawPtr $ Ptr n

alloc :: Pointer ptr a => Closure a -> TC ptr
alloc cl = do
    p <- freshPtr
    setClosure p cl
    return p

buildClosure :: TC a -> TC (Closure a)
buildClosure m = do
    env <- ask
    return $ Unevaluated $ TCCl env Inactive m

suspend :: Pointer ptr a => TC a -> TC ptr
suspend m = alloc =<< buildClosure m

evaluated :: Pointer ptr a => a -> TC ptr
evaluated = alloc . Evaluated

poke :: Pointer ptr a => ptr -> TC a -> TC ()
poke p m = do
    cl <- buildClosure m
    setClosure p cl

recursive :: Pointer ptr a => (ptr -> TC ptr) -> TC ptr
recursive f = do
    p <- suspend (fail "<uninitialised pointer>")
    poke p (forceClosure =<< f p)
    return p

recursives :: Pointer ptr a => [b] -> ([ptr] -> b -> TC a) -> TC [ptr]
recursives xs f = do
  ps <- replicateM (length xs) $ suspend (fail "<uninitialised pointer>")
  sequence_ [ poke p (f ps x) | (p, x) <- zip ps xs ]
  return ps

updatePtr :: Pointer ptr a => (a -> a) -> ptr -> TC ()
updatePtr f = updatePtrM (return . f)

updatePtrM :: Pointer ptr a => (a -> TC a) -> ptr -> TC ()
updatePtrM f p = do
    modClosure (apply f) p
    return ()
    where
	apply f (Evaluated x)	= do
	    cl <- buildClosure (f x)
	    return cl
	apply f (Unevaluated m) =
	    return $ Unevaluated m{ clAction = action }
	    where
		action = f =<< clAction m

---------------------------------------------------------------------------
-- * Lifting functions to pointers
---------------------------------------------------------------------------

liftPtr :: (Pointer ptr a, Pointer ptr' b) =>
	   (a -> b) -> ptr -> TC ptr'
liftPtr f = liftPtrM (return . f)

liftPtrM :: (Pointer ptr a, Pointer ptr' b) =>
	    (a -> TC b) -> ptr -> TC ptr'
liftPtrM f p = suspend $ f =<< forceClosure p

