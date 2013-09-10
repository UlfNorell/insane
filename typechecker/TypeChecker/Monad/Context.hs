
module TypeChecker.Monad.Context where

import Control.Applicative
import Control.Monad.Reader
import Data.List

import Syntax.Internal
import TypeChecker.Monad
import TypeChecker.Monad.Heap
import TypeChecker.DeBruijn
import Utils

getContext :: TC Context
getContext = asks envContext

withContext :: (Context -> Context) -> TC a -> TC a
withContext f = local $ \e -> e { envContext = f (envContext e) }

extendContext :: Name -> Type -> TC a -> TC a
extendContext x t = withContext (VBind x t :)

extendContext_ :: Name -> TC a -> TC a
extendContext_ x m = do
  set <- evaluated Set
  extendContext x set m

extendContextTel :: Telescope -> TC a -> TC a
extendContextTel tel = withContext (TBind (reverse tel) :)

(!) :: Context -> Name -> Maybe (DeBruijnIndex, DeBruijnIndex, Type)
ctx ! x = look 0 ctx
    where
	look n (VBind y t : ctx)
	    | x == y    = return (n, n + 1, t)
	    | otherwise = look (n + 1) ctx
        look n (TBind tel : ctx) =
          lookTel n n tel `mplus` look n' ctx
          where n' = n + genericLength tel
	look _ [] = fail ""

        lookTel n m (RBind y t : tel)
          | x == y    = return (n, m, t)
          | otherwise = lookTel (n + 1) m tel
        lookTel _ _ [] = fail ""

lookupContext :: Name -> TC (DeBruijnIndex, Type)
lookupContext x = do
    ctx <- getContext
    case ctx ! x of
	Just (n, m, t) -> (,) n <$> raiseBy m t
	Nothing	       -> fail $ "Unbound variable: " ++ x

flattenContext :: Context -> [(Name, Type)]
flattenContext = concatMap f
  where
    f (VBind x t) = [(x, t)]
    f (TBind tel) = [ (x, t) | RBind x t <- tel ]

getVarName :: DeBruijnIndex -> TC String
getVarName n = do
    ctx <- getContext
    fst <$> (ctx ! n)
    where
	cxt ! n
	    | len <= n  = fail $ "deBruijn index out of range " ++ show n ++ " in " ++ show xs
	    | otherwise = return $ xs !! fromIntegral n
	    where
		len = fromIntegral $ length xs
                xs  = flattenContext cxt

