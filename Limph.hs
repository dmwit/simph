{-# LANGUAGE ConstraintKinds #-}
module Limph where

import Control.Monad.Except
import Control.Monad.RWS hiding ((<>))
import Data.Map (Map)
import Data.Maybe
import Data.Semigroup
import Data.Set (Set)
import Data.Text.Prettyprint.Doc
import Data.Void
import qualified Data.Map as M
import qualified Data.Set as S

data SourceExpr = SourceVar String | SourceLambda String SourceExpr | SourceApp SourceExpr SourceExpr
	deriving (Eq, Ord, Read, Show)

data TargetExpr pv
	= TargetVar String
	| TargetLambda String (Purity pv) (Purity pv) (TargetExpr pv)
	| TargetApp (Purity pv) (Purity pv) (Purity pv) (Purity pv) (TargetExpr pv) (TargetExpr pv)
	deriving (Eq, Ord, Read, Show)

data Purity pv = PurityVar pv | Pure | Monadic
	deriving (Eq, Ord, Read, Show)

data BareTy pv tv = TyVar tv | Base | Arrow (BareTy pv tv) (MTy pv tv)
	deriving (Eq, Ord, Read, Show)

data MTy pv tv = MTy (Purity pv) (BareTy pv tv)
	deriving (Eq, Ord, Read, Show)

type Env pv tv = Map String (MTy pv tv)

data PurityConstraints pv = PurityConstraints
	{ pcLT :: [(pv, pv)]
	, pcMonadic :: Set pv
	, pcPure :: Set pv
	} deriving (Eq, Ord, Read, Show)

instance Ord pv => Semigroup (PurityConstraints pv) where
	pc <> pc' = PurityConstraints
		{ pcLT = pcLT pc <> pcLT pc'
		, pcMonadic = pcMonadic pc <> pcMonadic pc'
		, pcPure = pcPure pc <> pcPure pc'
		}

instance Ord pv => Monoid (PurityConstraints pv) where
	mempty = PurityConstraints mempty mempty mempty
	mappend = (<>)

instance Pretty SourceExpr where
	pretty (SourceVar v) = pretty v
	pretty e@(SourceLambda{}) = nest 4 (pretty "\\" <> sep (go e)) where
		go (SourceLambda v body) = pretty v : go body
		go body = [pretty "->", pretty body]
	pretty (SourceApp e1 e2) = nest 4 $ sep [pretty1, pretty2] where
		pretty1 = case e1 of
			SourceLambda{} -> parens (pretty e1)
			_ -> pretty e1
		pretty2 = case e2 of
			SourceVar{} -> pretty e2
			_ -> parens (pretty e2)

instance Pretty pv => Pretty (TargetExpr pv) where
	pretty (TargetVar v) = pretty v
	-- TODO: specialize the printing of TargetLambda and TargetApp when there
	-- are no purity variables
	pretty (TargetLambda v src tgt e) = nest 4 $ sep
		[ pretty "\\" <> pretty v <> pretty " ->"
		, parens $ hsep
			[ pretty "lift ::"
			, pretty (MTy src voidBase)
			, pretty "->"
			, pretty (MTy tgt voidBase)
			]
		]
	pretty (TargetApp m1 m2 m1res fullres e1 e2) = nest 4 $ sep
		[ parens $ hsep
			[ pretty "app ::"
			, parens (pretty (MTy m1 (Arrow Base (MTy m1res voidBase))))
			, pretty "->"
			, pretty (MTy m2 voidBase)
			, pretty "->"
			, pretty (MTy fullres voidBase)
			]
		, parensUnlessVar e1
		, parensUnlessVar e2
		] where
		parensUnlessVar e@TargetVar{} = pretty e
		parensUnlessVar e = parens (pretty e)

voidBase :: BareTy pv Void
voidBase = Base

instance Pretty pv => Pretty (Purity pv) where
	pretty Pure = pretty "Id"
	pretty Monadic = pretty "m"
	pretty (PurityVar pv) = pretty "ρ" <> pretty pv

instance (Pretty pv, Pretty tv) => Pretty (BareTy pv tv) where
	pretty (TyVar tv) = pretty "α" <> pretty tv
	pretty Base = pretty "_"
	pretty (Arrow i o) = nest 4 $ sep [prettyParenthesizeArrow i, pretty "-> " <> pretty o]

instance (Pretty pv, Pretty tv) => Pretty (MTy pv tv) where
	pretty (MTy Pure bty) = pretty bty
	pretty (MTy m bty) = nest 4 $ sep [pretty m, prettyParenthesizeArrow bty]

prettyParenthesizeArrow bty@Arrow{} = parens (pretty bty)
prettyParenthesizeArrow bty = pretty bty

instance Pretty pv => Pretty (PurityConstraints pv) where
	pretty pc = braces . sep . punctuate comma
		$  [hsep [pretty "ρ" <> pretty pv1, pretty "≤", pretty "ρ" <> pretty pv2] | (pv1, pv2) <- pcLT pc]
		++ [hsep [pretty "ρ" <> pretty pv , pretty "=", pretty monadic] | pv <- S.toList (pcMonadic pc)]
		++ [hsep [pretty "ρ" <> pretty pv , pretty "=", pretty pure   ] | pv <- S.toList (pcPure pc)]
		where
		monadic = Monadic :: Purity Void
		pure = Pure :: Purity Void

simpleEnv :: Env pv tv
simpleEnv = M.fromList
	[ ("print", MTy Pure (Arrow Base (MTy Monadic Base)))
	, ("readLn", MTy Monadic Base)
	, ("plus", MTy Pure (Arrow Base (MTy Pure (Arrow Base (MTy Pure Base)))))
	]

data TCError pv tv
	= NotInScope String
	| AlreadyInScope String
	| CannotEscapeMonad
	| TypeError (BareTy pv tv) (BareTy pv tv)
	deriving (Eq, Ord, Read, Show)

data TCState pv tv = TCState
	{ nextPV :: pv
	, nextTV :: tv
	, bindings :: Map tv (BareTy pv tv)
	} deriving (Eq, Ord, Read, Show)

emptyState :: (Ctx pv tv, Num pv, Num tv) => TCState pv tv
emptyState = TCState 0 0 M.empty

type TC pv tv = ExceptT (TCError pv tv) (RWS (Env pv tv) (PurityConstraints pv) (TCState pv tv))
type Ctx pv tv = (Enum pv, Enum tv, Ord pv, Ord tv)

runTC :: TC Int Int a -> (Either (TCError Int Int) a, TCState Int Int, PurityConstraints Int)
runTC act = runRWS (runExceptT act) simpleEnv emptyState

freshPV :: Ctx pv tv => TC pv tv (Purity pv)
freshPV = do
	pv <- gets nextPV
	modify (\s -> s { nextPV = succ pv })
	return (PurityVar pv)

freshTV :: Ctx pv tv => TC pv tv (BareTy pv tv)
freshTV = do
	tv <- gets nextTV
	modify (\s -> s { nextTV = succ tv })
	return (TyVar tv)

(≤) :: Ctx pv tv => Purity pv -> Purity pv -> TC pv tv ()
PurityVar pv ≤ PurityVar pv' = tell mempty { pcLT = [(pv, pv')] }
PurityVar pv ≤ Pure = tell mempty { pcPure = S.singleton pv }
Monadic ≤ PurityVar pv = tell mempty { pcMonadic = S.singleton pv }
Monadic ≤ Pure = throwError CannotEscapeMonad
_ ≤ _ = return ()

canon :: Ctx pv tv => tv -> TC pv tv (BareTy pv tv)
canon tv = do
	mty <- gets (M.lookup tv . bindings)
	case mty of
		Nothing -> return (TyVar tv)
		Just (TyVar tv') -> canon tv'
		Just ty -> return ty

canonVar :: Ctx pv tv => BareTy pv tv -> TC pv tv (BareTy pv tv)
canonVar (TyVar tv) = canon tv
canonVar ty = return ty

unifyCanonical :: Ctx pv tv => BareTy pv tv -> BareTy pv tv -> TC pv tv ()
unifyCanonical (TyVar tv) ty = modify (\s -> s { bindings = M.insert tv ty (bindings s) })
unifyCanonical ty (TyVar tv) = modify (\s -> s { bindings = M.insert tv ty (bindings s) })
unifyCanonical Base Base = return ()
unifyCanonical (Arrow i (MTy m o)) (Arrow i' (MTy m' o')) = do
	m  ≤ m'
	m' ≤ m
	unify i i'
	unify o o'
unifyCanonical ty ty' = throwError (TypeError ty ty')

unify :: Ctx pv tv => BareTy pv tv -> BareTy pv tv -> TC pv tv ()
unify ty_ ty_' = do
	ty  <- canonVar ty_
	ty' <- canonVar ty_'
	unifyCanonical ty ty'

infer :: Ctx pv tv => SourceExpr -> TC pv tv (TargetExpr pv, MTy pv tv)
infer (SourceVar v) = asks (M.lookup v) >>= \mty -> case mty of
	Nothing -> throwError (NotInScope v)
	Just ty -> return (TargetVar v, ty)

infer (SourceLambda v e) = do
	mty <- asks (M.lookup v)
	when (isJust mty) (throwError (AlreadyInScope v))
	α <- freshTV
	(eh, MTy m ty) <- local (M.insert v (MTy Pure α)) (infer e)
	ρ <- freshPV
	ρ ≤ m
	return (TargetLambda v m ρ eh, MTy Pure (Arrow α (MTy ρ ty)))

infer (SourceApp e e') = do
	(eh , MTy m  ty ) <- infer e
	(eh', MTy m' ty') <- infer e'
	ρ <- freshPV
	α <- freshTV
	unify ty (Arrow ty' (MTy ρ α))
	ρ' <- freshPV
	m  ≤ ρ'
	m' ≤ ρ'
	ρ  ≤ ρ'
	return (TargetApp m m' ρ ρ' eh eh', MTy ρ' α)
