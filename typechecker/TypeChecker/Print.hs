{-# LANGUAGE FlexibleInstances, UndecidableInstances, OverlappingInstances #-}

module TypeChecker.Print where

import Control.Monad.Error
import Control.Applicative
import qualified Text.PrettyPrint as PP

import Syntax.Internal
import qualified Syntax.Abs as Abs
import TypeChecker.Monad
import TypeChecker.Monad.Heap
import TypeChecker.Monad.Context
import Utils

type Doc = PP.Doc

text s	 = return $ PP.text s
vcat ds  = PP.vcat <$> sequence ds
fsep ds  = PP.fsep <$> sequence ds
hsep ds  = PP.hsep <$> sequence ds
sep ds   = PP.sep  <$> sequence ds
nest n d = PP.nest n <$> d
d <+> d' = (PP.<+>) <$> d <*> d'
d <> d'  = (PP.<>) <$> d <*> d'
parens d = PP.parens <$> d
brackets d = PP.brackets <$> d
comma    = return PP.comma

punctuate :: TC Doc -> [TC Doc] -> TC Doc
punctuate d xs = (.) PP.fsep . PP.punctuate <$> d <*> sequence xs

mparens True  = parens
mparens False = id

class Pretty a where
    pretty :: a -> TC Doc
    prettyPrec :: Int -> a -> TC Doc

    pretty	 = prettyPrec 0
    prettyPrec _ = pretty

instance (Pointer ptr a, Pretty a) => Pretty ptr where
    prettyPrec n p = do
    	cl <- getClosure p
	case cl of
	    Unevaluated	_   -> text "_"
	    Evaluated x	    -> prettyPrec n x

instance Pretty Definition where
    pretty (Axiom x t) =
	hsep [ text x, text ":", pretty t ]
    pretty (Defn x t cs) =
	vcat $ pretty (Axiom x t) : [ text x <+> d | d <- map pretty cs ]
    pretty (Cons c t) = pretty (Axiom c t)
    pretty (Data d t cs) =
	vcat [ hsep [ text "data", text d, text ":", pretty t, text "where" ]
	     , nest 2 $ vcat $ map pretty cs
	     ]

instance Pretty Constructor where
    pretty (Constr c ar) = text c <> text "/" <> text (show ar)

instance Pretty Clause' where
    pretty (Clause ps t) =
	thread (prettyPat 1) ps $ \ds ->
	sep [ fsep (map return ds) <+> text "="
	    , nest 2 $ pretty t
	    ]

instance Pretty Type' where
    prettyPrec n t = case t of
	Pi a b ->
	    mparens (n > 0) $
	    sep [ parens (text x <+> text ":" <+> pretty a) <+> text "->"
		, pretty b
		]
	    where x = absName b
        RPi tel a ->
            extendContextTel tel $
            mparens (n > 0) $
            sep [ brackets (punctuate comma $ map pretty tel) <+> text "->"
                , pretty a ]
	Fun a b ->
	    mparens (n > 0) $
	    sep [ prettyPrec 1 a <+> text "->"
		, pretty b
		]
	Set -> text "Set"
	El t -> prettyPrec n t

instance Pretty a => Pretty (RBind a) where
    pretty (RBind x a) =
      hsep [ text x, text ":", pretty a ]

instance Pretty Term' where
    prettyPrec n t = case t of
	Var m	-> do
	    x <- getVarName m
	    text x
          `catchError` \_ ->
            text ("!" ++ show m ++ "!")
	Def x	-> text x
	App s t ->
	    mparens (n > 5) $
	    sep [ prettyPrec 5 s, prettyPrec 6 t ]
	Lam t	->
	    mparens (n > 0) $
	    sep [ text "\\" <> text (absName t) <+> text "->"
		, nest 2 $ pretty t
		]

prettyPat n p ret = case p of
    VarP x    -> extendContext_ x $ ret $ PP.text x
    ConP c ps ->
	thread (prettyPat 1) ps $ \ds ->
	ret $ mparens' (n > 0 && not (null ps))
	    $ PP.fsep $ PP.text c : ds
    where
	mparens' True  = PP.parens
	mparens' False = id

instance Pretty a => Pretty (Abs a) where
    prettyPrec n (Abs x b) = extendContext_ x $ prettyPrec n b

