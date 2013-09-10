
module TypeChecker.Reduce where

import Control.Applicative
import Control.Monad.Trans
import Control.Monad
import Data.Monoid
import Data.Foldable hiding (foldr1)
import Data.Traversable hiding (mapM)

import Syntax.Internal
import TypeChecker.Monad
import TypeChecker.Monad.Heap
import TypeChecker.Monad.Signature
import TypeChecker.Monad.Context
import TypeChecker.DeBruijn
import TypeChecker.Print
import TypeChecker.Force
import Utils

data RedexView
	= Iota Name	  [Term] -- | The number of arguments should be the same as the arity.
	| Beta (Abs Term)  Term
	| NonRedex Term'
  deriving (Show)

-- | @spine (f a b c) = [(f, f), (a, f a), (b, f a b), (c, f a b c)]@
spine :: Term -> TC [(Term, Term)]
spine p = do
    t <- forceClosure p
    case t of
	App s t	-> do
	    sp <- spine s
	    return $ sp ++ [(t, p)]
	_	-> return [(p,p)]

redexView :: Term -> TC RedexView
redexView t = do
    sp <- spine t
    case sp of
	(h,_) : args -> do
	    t <- forceClosure h
	    case t of
		Var x	-> other sp
		Def c	-> do
		    ar <- functionArity c
		    case ar of
			Just n | n == length args
			  -> return $ Iota c $ map fst args
			_ -> other sp
		Lam s	-> case args of
		    [(t,_)] -> return $ Beta s t
		    _	    -> other sp
		App s t	-> fail "redexView: impossible App"
	_ -> fail "redexView: impossibly empty spine"
    where
	top	 = snd . last
	other sp = NonRedex <$> forceClosure (top sp)

data ConView = ConApp Name [Term]
	     | NonCon Term

conView :: Term -> TC ConView
conView t = do
    sp <- spine t
    case sp of
	(c,_):args  -> do
	    s <- forceClosure c
	    case s of
		Def c	-> return $ ConApp c $ map fst args
		_	-> return $ NonCon t
	_   -> fail "conView: impossibly empty spine"

data Progress = NoProgress | YesProgress

instance Monoid Progress where
    mempty			    = NoProgress
    mappend NoProgress p	    = p
    mappend p NoProgress	    = p
    mappend YesProgress YesProgress = YesProgress

whenProgress :: Monad m => Progress -> m a -> m ()
whenProgress YesProgress m = m >> return ()
whenProgress NoProgress  m = return ()

class WHNF a where
    whnf :: a -> TC Progress

instance (WHNF a, WHNF b) => WHNF (a,b) where
    whnf (x,y) = mappend <$> whnf x <*> whnf y

instance WHNF Type where
    whnf p = do
	a <- forceClosure p
	case a of
            RPi _ _ -> return NoProgress
	    Pi _ _  -> return NoProgress
	    Fun _ _ -> return NoProgress
	    Set	    -> return NoProgress
	    El t    -> whnf t

instance WHNF Term where
    whnf p = do
	v <- redexView p
	case v of
	    NonRedex t -> case t of
		App s t	-> do
		    pr <- whnf s
		    whenProgress pr $ whnf p
		    return pr
		Lam _	-> return NoProgress
		Var _	-> return NoProgress
		Def _	-> return NoProgress
	    Beta s t	-> do
		poke p (forceClosure =<< subst t s)
		whnf p
	    Iota f ts	-> do
		Defn _ _ cs <- getDefinition f
		m	    <- match cs ts
		case m of
		    YesMatch t -> do
			poke p (forceClosure t)
			whnf p
		    MaybeMatch -> return NoProgress
		    NoMatch    -> fail "Incomplete pattern matching"

data Match a = YesMatch a | MaybeMatch | NoMatch

instance Monoid a => Monoid (Match a) where
    mempty		 = YesMatch mempty
    mappend NoMatch _	 = NoMatch
    mappend _ NoMatch	 = NoMatch
    mappend MaybeMatch _ = MaybeMatch
    mappend _ MaybeMatch = MaybeMatch
    mappend (YesMatch ts) (YesMatch ss) = YesMatch $ ts `mappend` ss

instance Functor Match where
    fmap f (YesMatch x) = YesMatch $ f x
    fmap f NoMatch	= NoMatch
    fmap f MaybeMatch	= MaybeMatch

instance Foldable Match where
    foldMap f (YesMatch x) = f x
    foldMap f NoMatch      = mempty
    foldMap f MaybeMatch   = mempty

instance Traversable Match where
    traverse f (YesMatch x) = YesMatch <$> f x
    traverse f NoMatch      = pure NoMatch
    traverse f MaybeMatch   = pure MaybeMatch

choice :: Match a -> Match a -> Match a
choice NoMatch m = m
choice m       _ = m

-- | Invariant: there are the same number of terms as there are patterns in the clauses
match :: [Clause] -> [Term] -> TC (Match Term)
match cs ts = foldr1 choice <$> mapM (flip matchClause ts) cs

matchClause :: Clause -> [Term] -> TC (Match Term)
matchClause c ts = do
    Clause ps t <- forceClosure c
    m <- matchPatterns ps ts
    traverse (\ss -> substs ss t) m

matchPatterns :: [Pattern] -> [Term] -> TC (Match [Term])
matchPatterns ps ts = mconcat <$> zipWithM matchPattern ps ts

matchPattern :: Pattern -> Term -> TC (Match [Term])
matchPattern (VarP _) t = return $ YesMatch [t]
matchPattern (ConP c ps) t = do
    whnf t
    v <- conView t
    case v of
	ConApp c' ts
	    | c == c'	-> matchPatterns ps (dropPars ts)
	    | otherwise	-> return NoMatch
	_		-> return MaybeMatch
  where
    dropPars ts = drop (length ts - length ps) ts

