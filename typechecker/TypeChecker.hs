{-# LANGUAGE UndecidableInstances, FlexibleInstances, OverlappingInstances #-}

module TypeChecker where

import Control.Applicative
import Control.Monad.Error

import qualified Data.Map as Map
import Data.List

import qualified Syntax.Abs as Abs
import Syntax.Print
import Syntax.Internal

import TypeChecker.Monad
import TypeChecker.Monad.Heap
import TypeChecker.Monad.Context
import TypeChecker.Monad.Signature
import TypeChecker.Force
import TypeChecker.DeBruijn
import TypeChecker.Print
import TypeChecker.Reduce

import Utils

identToName :: Abs.Ident -> Name
identToName (Abs.Ident x) = x

debug :: TC ()
debug = do
    sig  <- getSig
    heap <- getHeap
--     liftIO $ putStrLn "Heap:"
--     mapM_ (pr show) $ Map.assocs heap
    mapM_ pr $ Map.elems sig
    return ()
    where
        pr e = do
            d <- pretty e
            liftIO $ print d

dbg :: Show a => TC a -> TC ()
dbg d = return () -- (liftIO . putStrLn) . show =<< d

checkProgram :: Abs.Program -> TC ()
checkProgram (Abs.Prog ds) = do
    setSig =<< buildSignature ds
    forceSig
    debug
    `catchError`  \e -> do
        debug
        throwError e

buildSignature :: [Abs.Decl] -> TC Signature
buildSignature ds =
    Map.unions
    <$> mapM buildDef
     (  groupBy ((==)    `on` name)
     $  sortBy  (compare `on` name)
     $  ds
     )
    where
        name (Abs.TypeSig i _)    = identToName i
        name (Abs.FunDef i _ _)   = identToName i
        name (Abs.DataDecl i _ _) = identToName i

        telePi :: [Abs.TelBinding] -> Abs.Expr -> Abs.Expr
        telePi tel e = foldr bind e tel -- (\ (Abs.Bind x t) s -> Abs.Pi x t s) e tel
          where
            bind (Abs.PiBind (Abs.Bind x t)) s = Abs.Pi x t s
            bind (Abs.TelBind tel) s = Abs.RPi tel s

        constrWithArity :: Abs.Constr -> Constructor
        constrWithArity (Abs.Constr c t) = Constr (identToName c) $ arity t
            where
                arity (Abs.Pi _ _ b)            = 1 + arity b
                arity (Abs.Fun _ b)             = 1 + arity b
                arity (Abs.RPi (Abs.Tel tel) b) = length tel + arity b
                arity _                         = 0

        buildConstr :: [Abs.TelBinding] -> Abs.Constr -> TC Signature
        buildConstr tel (Abs.Constr x e) = do
            let e' = telePi tel e
                c  = identToName x
            t <- isType e'
            return $ Map.singleton c $ Cons c t

        buildDef :: [Abs.Decl] -> TC Signature
        buildDef [Abs.DataDecl x tel cs] = do
            t   <- isType (telePi tel Abs.Set)
            tcs <- mapM (buildConstr tel) cs
            let d    = identToName x
                decl = Map.singleton d $ Data d t $ map constrWithArity cs
            return $ Map.unions $ decl : tcs

        buildDef ds = do
            t  <- getType
            cs <- getClauses t
            let d = case cs of
                    []  -> Axiom x t
                    _   -> Defn  x t cs
            return $ Map.singleton x d
            where
                x = name $ head ds

                getType = case [ t | Abs.TypeSig _ t <- ds ] of
                            [t] -> isType t
                            []  -> fail $ "No type signature for " ++ x
                            ts  -> fail $ "Multiple type signatures for " ++ x

                getClauses t = mapM (getClause t) [ d | d@(Abs.FunDef _ _ _) <- ds ]
                getClause t (Abs.FunDef _ ps e) =
                    checkClause ps e t
                getClause _ _ = error "getClause: __IMPOSSIBLE__"

checkClause :: [Abs.Pattern] -> Abs.Expr -> Type -> TC Clause
checkClause ps e t = suspend (checkClause' ps e t)

checkClause' :: [Abs.Pattern] -> Abs.Expr -> Type -> TC Clause'
checkClause' ps e a = do
    ps <- mapM buildPattern ps
    checkPatterns ps a $ \_ _ b -> do
        t <- checkType e b
        return $ Clause ps t

buildPattern :: Abs.Pattern -> TC Pattern
buildPattern p = case appView p of
        Abs.VarP i : ps -> do
                isConstructor x
                ConP x <$> mapM buildPattern ps
            `catchError` \_ ->
                case ps of
                    []  -> return $ VarP x
                    _   -> fail $ "Undefined constructor " ++ x
            where
                x = identToName i
        _   -> fail "__IMPOSSIBLE__"
    where
        appView (Abs.AppP p q) = appView p ++ [q]
        appView p              = [p]

isDatatype :: Type -> TC (Name, [Term])
isDatatype p = do
    whnf p
    a <- forceClosure p
    case a of
        El t    -> do
            (d,_):args <- spine t
            d <- forceClosure d
            case d of
                Def d   -> return (d, map fst args)
                _       -> badData
        _       -> badData
    where
        badData = fail . show =<< pretty p <+> text "is not a datatype"

piApply :: Type -> [Term] -> TC Type
piApply a []     = return a
piApply a ts0@(t:ts) = suspend $ do
    whnf a
    a <- forceClosure a
    forceClosure =<<
        case a of
            Pi  _ b   -> flip piApply ts =<< subst t b
            Fun _ b   -> piApply b ts
            RPi tel b
              | length ts0 < length tel -> fail $ "piApply: too few arguments to " ++ show a ++ ": " ++ show ts0
              | otherwise -> do
                let (ts1, ts2) = splitAt (length tel) ts0
                b <- substs ts1 b
                piApply b ts2
            _         -> fail . show =<< text "piApply: not a function type" <+> pretty a

data ArgType = SimpleArg Type
             | TelArg Telescope

-- | The argument should be a function type.
argumentType :: Type -> TC ArgType
argumentType p = do
    a <- forceClosure p
    case a of
        Pi a _    -> return (SimpleArg a)
        Fun a _   -> return (SimpleArg a)
        RPi tel _ -> return (TelArg tel)
        _         -> fail . show =<< text "expected function type, found" <+> pretty p

checkPatterns :: [Pattern] -> Type -> (Integer -> [Term] -> Type -> TC a) -> TC a
checkPatterns []         a ret = ret 0 [] a
checkPatterns ps0@(p:ps) a ret = do
    arg <- argumentType a
    case arg of
      SimpleArg arg ->
        checkPattern p arg $ \n t -> do
            a <- raiseBy n a
            b <- piApply a [t]
            checkPatterns ps b $ \m ts b -> do
                t <- raiseBy m t
                ret (n + m) (t:ts) b
      TelArg tel -> do
        unless (length ps0 >= length tel) $ fail $ "Not enough arguments to constructor of type " ++ show a
        let (ps1, ps2) = splitAt (length tel) ps0
            allVars = mapM isVar
            isVar (VarP x) = Just x
            isVar _        = Nothing
        case allVars ps1 of
          Nothing -> fail $ "Recursive telescope patterns must be variables: " ++ show ps1
          Just xs -> do
            let n  = genericLength xs
            a <- raiseBy n a
            vs <- mapM evaluated [ Var i | i <- reverse [0..n - 1] ]
            b <- piApply a vs
            extendContextTel [ RBind x a | (x, RBind _ a) <- zip xs tel ] $
              checkPatterns ps2 b $ \m us b -> do
                vs <- raiseBy m vs
                ret (n + m) (vs ++ us) b

checkPattern :: Pattern -> Type -> (Integer -> Term -> TC a) -> TC a
checkPattern p a ret =
    case p of
        VarP x    -> extendContext x a $ ret 1 =<< evaluated (Var 0)
        ConP x ps -> do
            b       <- defType x
            (d, us) <- isDatatype a
            b'      <- piApply b us
            checkPatterns ps b' $ \n ts a' -> do
                a  <- raiseBy n a
                us <- raiseBy n us
                a === a' `catchError` \ (Fail s) -> do
                    s' <- show <$> vcat [ text "when checking the type of", nest 2 $ text (show p)
                                        , nest 2 $ text "expected:" <+> pretty a
                                        , nest 2 $ text "inferred:" <+> pretty a' ]
                    fail $ s ++ "\n" ++ s'
                h <- evaluated (Def x)
                ret n =<< apps h (us ++ ts)
    where
        apps :: Term -> [Term] -> TC Term
        apps s []     = return s
        apps s (t:ts) = do
            st <- evaluated (App s t)
            apps st ts
        

isType :: Abs.Expr -> TC Type
isType e = suspend (isType' e)

checkType :: Abs.Expr -> Type -> TC Term
checkType e t = suspend (checkType' e t)

inferType :: Abs.Expr -> TC (Term, Type)
inferType e = do
    p   <- suspend (inferType' e)
    ptm <- suspend $ fst <$> forceClosure p
    ptp <- (forceClosure . snd) `liftPtrM` p
    return (ptm, ptp)

isType' :: Abs.Expr -> TC Type'
isType' e = do
  case e of
    Abs.Pi x e1 e2 -> do
        x <- return $ identToName x
        a <- isType e1
        b <- extendContext x a $ isType e2
        return $ Pi a (Abs x b)
    Abs.RPi tel e -> do
        tel <- checkTel tel
        a   <- extendContextTel tel $ isType e
        return $ RPi tel a
    Abs.Fun e1 e2 -> Fun <$> isType e1 <*> isType e2
    Abs.Set       -> return Set
    e             -> do
        set <- evaluated Set
        El <$> checkType e set

checkTel :: Abs.Telescope -> TC Telescope
checkTel (Abs.Tel tel) = do
  let mkTel as = [ RBind x a | (Abs.RBind (Abs.Ident x) _, a) <- zip tel as ]
      check as (Abs.RBind _ e) = extendContextTel (mkTel as) $ isType' e
  as <- recursives tel check :: TC [Type]
  return $ mkTel as

checkType' :: Abs.Expr -> Type -> TC Term'
checkType' e a = do
  case e of
    Abs.Lam [] e     -> checkType' e a
    Abs.Lam xs0@(x:xs) e -> do
        let e' = Abs.Lam xs e
        x <- return $ identToName x
        a <- forceClosure a
        s <- case a of
            Pi a b    -> extendContext x a (checkType e' (absBody b))
            Fun a b   -> extendContext x a (checkType e' =<< raise b)
            RPi tel b -> do
              unless (length xs0 >= length tel) $ fail $ "Too few arguments in insane lambda: " ++ printTree xs0 ++ " < " ++ show (length tel)
              let (ys, zs) = splitAt (length tel) xs0
                  tel'     = [ RBind (identToName y) a | (y, RBind _ a) <- zip ys tel ]
              extendContextTel tel' $ checkType (Abs.Lam zs e) b
            _       -> fail $ "expected function type, found " ++ show a
        return $ Lam (Abs x s)
    e -> do
        (v, b) <- inferType' e
        addConstraint $
          a === b `sayWhen` do
              gently $ force (v, (a, b))
              vcat [ sep [text "when checking the type of", nest 4 $ pretty v]
                   , nest 2 $ text "expected:" <+> pretty a
                   , nest 2 $ text "inferred:" <+> pretty b ]
        return v
  `sayWhen` sep [ text "when checking that"
                , nest 4 $ text (printTree e)
                , nest 2 $ text "has type"
                , nest 4 $ pretty a ]

sayWhen m wh = m `catchError` \(Fail s) -> do
  s' <- show <$> wh
  fail $ s ++ "\n" ++ s'

appView :: Abs.Expr -> [Abs.Expr]
appView (Abs.App e1 e2) = appView e1 ++ [e2]
appView e               = [e]

checkArgs :: Type -> [Abs.Expr] -> [Abs.Expr] -> TC ([Term], Type)
checkArgs a _ [] = return ([], a)
checkArgs a es0 es@(e:es1) = do
  a <- forceClosure a
  case a of
    Fun a b   -> do
      v <- checkType e a
      (vs, c) <- checkArgs b (es0 ++ [e]) es1
      return (v : vs, c)
    Pi  a b   -> do
      v <- checkType e a
      b <- subst v b
      (vs, c) <- checkArgs b (es0 ++ [e]) es1
      return (v : vs, c)
    RPi tel b -> do
      unless (length es >= length tel) $ fail $ "Insanely dependent functions must be fully applied: " ++ show es ++ " < " ++ show tel
      let (es1, es2) = splitAt (length tel) es
      vs <- recursives (zip tel es1) $ \vs (RBind _ a, e) -> do
        a <- substs vs a
        v <- checkType' e a
        return v
      b <- substs vs b
      (us, c) <- checkArgs b (es0 ++ es1) es2
      return (vs ++ us, c)
    _ -> fail $ unlines [ "Expected function type, found " ++ show a
                        , "in the application of " ++ printTree (foldl1 Abs.App es0)
                        , "to " ++ printTree (head es)
                        ]

inferType' :: Abs.Expr -> TC (Term', Type)
inferType' e0 = do
  case e0 of
    Abs.Name i -> do
         t <- defType x
         return (Def x, t)
     `catchError` \_ -> do
         (n,t) <- lookupContext x
         return (Var n, t)
     where
         x = identToName i
    Abs.App{} -> do
      let e : es@(_:_) = appView e0
      (f, a)    <- inferType e
      (args, b) <- checkArgs a [e] es
      v <- buildApp f args
      return (v, b)
      where
        buildApp :: Term -> [Term] -> TC Term'
        buildApp f [] = forceClosure f
        buildApp f (e : es) = do
          fe <- evaluated $ App f e
          buildApp fe es
    e -> fail $ "inferType not implemented for " ++ printTree e

class Convert a where
    (===) :: a -> a -> TC ()

instance (Pretty a, Pointer ptr a, Convert a, Force a, WHNF ptr) => Convert ptr where
    p === q
        | p == q    = return ()
        | otherwise = do
            whnf (p, q)
            x <- forceClosure p
            y <- forceClosure q
            x === y `sayWhen` do
              gently $ force (x, y)
              sep [ text "when checking that"
                  , nest 2 $ pretty x <+> text "=="
                  , nest 2 $ pretty y ]

instance Convert Type' where
    Pi a b  === Pi a' b'  = (a,b) === (a',b')
    Fun a b === Fun a' b' = (a,b) === (a',b')
    Pi a b  === Fun a' b' = do
        a === a'
        b' <- raise b'
        b === Abs "x" b'
    Fun a b  === Pi a' b' = do
        a === a'
        b <- raise b
        Abs "x" b === b'
    Set     === Set       = return ()
    El t    === El t'     = t === t'
    a       === b         = fail . show =<< pretty a <+> text "!=" <+> pretty b

instance Convert Term' where
    a === b = test a b
        where
            test (Lam s) (Lam t) =
                extendContext (absName s) (error "<unknown type>") $ s === t
            test (App s s') (App t t') = do
                s  === t
                s' === t'
            test (Var n) (Var m)
                | n == m    = return ()
                | otherwise = do
                    x <- getVarName n
                    y <- getVarName m
                    fail $ x ++ " (" ++ show n ++ ") != " ++ y ++ " (" ++ show m ++ ")"
            test (Def f) (Def g)
                | f == g    = return ()
                | otherwise = fail $ f ++ " != " ++ g
            test s t = do
                force (s, t) `catchError` \_ -> return ()
                d <- pretty s <+> text " != " <+> pretty t
                fail $ show d

instance (Convert a, Convert b) => Convert (a,b) where
    (x,y) === (x',y') = do x === x'; y === y'

instance Convert a => Convert (Abs a) where
    (===) = (===) `on` absBody

