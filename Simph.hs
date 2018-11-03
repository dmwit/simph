{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Simph where

import Control.Monad.Trans.Except
import Control.Monad.Except
import Control.Monad.RWS hiding ((<>))
import Data.Graph
import Data.IntMap (IntMap)
import Data.IntSet (IntSet)
import Data.Map (Map)
import Data.Maybe
import Data.Semigroup
import Data.Set (Set)
import Data.Text.Prettyprint.Doc
import Data.Void
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
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
newtype PurityConstraints pv = PurityConstraints [(Purity pv, Purity pv)]
	deriving (Eq, Ord, Read, Show, Semigroup, Monoid)

data Compilation pv tv = Compilation
	{ cTerm :: TargetExpr pv
	, cType :: MTy pv tv
	} deriving (Eq, Ord, Read, Show)

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
	pretty (TargetLambda v src tgt e) = nest 4 . sep
		$  [pretty "\\" <> pretty v <> pretty " ->"]
		++ case lift of
			Nothing -> [pretty e]
			Just liftDoc -> case e of
				TargetVar{} -> [liftDoc, pretty e]
				_ -> [liftDoc, parens (pretty e)]
		where
		lift = case (src, tgt) of
			(Pure, Pure) -> Nothing
			(Monadic, Monadic) -> Nothing
			(Pure, Monadic) -> Just $ pretty "pure"
			_ -> Just . parens $ hsep
				[ pretty "lift ::"
				, pretty (MTy src voidBase)
				, pretty "->"
				, pretty (MTy tgt voidBase)
				]
	pretty (TargetApp m1 m2 m1res fullres e1 e2) = nest 4 . sep
		$  case app of
		   	Just appDoc -> [appDoc, parensUnlessVar e1]
		   	Nothing -> case e1 of
		   		TargetApp{} -> [pretty e1]
		   		_ -> [parens (pretty e1)]
		++ [parensUnlessVar e2]
		where
		app = case (m1, m1res, m2, fullres) of
			(Pure   , Pure   , Pure   , Pure   ) -> Nothing
			(Pure   , Pure   , Pure   , Monadic) -> Just (pretty "(pure.)")
			(Pure   , Pure   , Monadic, Monadic) -> Just (pretty "fmap")
			(Pure   , Monadic, Pure   , Monadic) -> Nothing
			(Pure   , Monadic, Monadic, Monadic) -> Just (pretty "(=<<)")
			(Monadic, Pure   , Pure   , Monadic) -> Just (pretty "(??)")
			(Monadic, Pure   , Monadic, Monadic) -> Just (pretty "(<*>)")
			(Monadic, Monadic, Pure   , Monadic) -> Just (pretty "(\\f x -> f >>= ($x))")
			(Monadic, Monadic, Monadic, Monadic) -> Just (pretty "((join.) . liftA2 ($))")
			_ -> Just . parens . hsep $
				[ pretty "app ::"
				, parens (pretty (MTy m1 (Arrow Base (MTy m1res voidBase))))
				, pretty "->"
				, pretty (MTy m2 voidBase)
				, pretty "->"
				, pretty (MTy fullres voidBase)
				]

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
	pretty (PurityConstraints cs) = braces . sep . punctuate comma
		$  [hsep [pretty m, pretty "≤", pretty m'] | (m, m') <- cs]

instance (Pretty pv, Pretty tv) => Pretty (Compilation pv tv) where
	pretty (Compilation eh ty) = sep
		[ pretty eh
		, hsep [pretty "::", pretty ty]
		]

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
	| AmbiguousPurityVariable
	deriving (Eq, Ord, Read, Show)

data TCState pv tv = TCState
	{ nextPV :: pv
	, nextTV :: tv
	, bindings :: Map tv (BareTy pv tv)
	} deriving (Eq, Ord, Read, Show)

emptyState :: (Ctx pv tv, Num pv, Num tv) => TCState pv tv
-- The starting point of 0 for purity variables is abused during constraint
-- solving: it is assumed that negative numbers are available for system use.
emptyState = TCState 0 0 M.empty

type TC pv tv = ExceptT (TCError pv tv) (RWS (Env pv tv) (PurityConstraints pv) (TCState pv tv))
type Ctx pv tv = (Enum pv, Enum tv, Ord tv)

runTC :: TC Int Int a -> (Either (TCError Int Int) a, TCState Int Int, PurityConstraints Int)
runTC act = runRWS (runExceptT act) simpleEnv emptyState

runInfer :: SourceExpr -> Either (TCError Int Int) (Compilation Void Int)
runInfer e = runExcept $ do
	let (res, s, pc) = runTC (infer e)
	Compilation eh mty <- except res
	σ <- solvePurityConstraints (nextPV emptyState, nextPV s) pc
	unless (IS.null (psAmbiguous σ)) (throwError AmbiguousPurityVariable)
	return (Compilation (substExpr σ eh) (substMTy σ (bindings s) mty))

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
m ≤ m' = tell (PurityConstraints [(m, m')])

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

infer :: Ctx pv tv => SourceExpr -> TC pv tv (Compilation pv tv)
infer (SourceVar v) = asks (M.lookup v) >>= \mty -> case mty of
	Nothing -> throwError (NotInScope v)
	Just ty -> return (Compilation (TargetVar v) ty)

infer (SourceLambda v e) = do
	mty <- asks (M.lookup v)
	when (isJust mty) (throwError (AlreadyInScope v))
	α <- freshTV
	Compilation eh (MTy m ty) <- local (M.insert v (MTy Pure α)) (infer e)
	ρ <- freshPV
	ρ ≤ m
	return (Compilation (TargetLambda v m ρ eh) (MTy Pure (Arrow α (MTy ρ ty))))

infer (SourceApp e e') = do
	Compilation eh  (MTy m  ty ) <- infer e
	Compilation eh' (MTy m' ty') <- infer e'
	ρ <- freshPV
	α <- freshTV
	unify ty (Arrow ty' (MTy ρ α))
	ρ' <- freshPV
	m  ≤ ρ'
	m' ≤ ρ'
	ρ  ≤ ρ'
	return (Compilation (TargetApp m m' ρ ρ' eh eh') (MTy ρ' α))

data PuritySubstitution = PuritySubstitution
	{ psAmbiguous :: IntSet -- could produce more structure, I guess...
	, psUnambiguous :: IntMap (Purity Void)
	} deriving (Eq, Ord, Read, Show)

instance Semigroup PuritySubstitution where
	ps <> ps' = PuritySubstitution
		{ psAmbiguous = psAmbiguous ps <> psAmbiguous ps'
		, psUnambiguous = psUnambiguous ps <> psUnambiguous ps'
		}

instance Monoid PuritySubstitution where
	mempty = PuritySubstitution mempty mempty
	mappend = (<>)

-- assumes that all purity variables are in the left-inclusive range given by the
-- first argument, and that there's room for two more variables above the range
solvePurityConstraints ::
	(Int, Int) ->
	PurityConstraints Int ->
	Except (TCError Int Int) PuritySubstitution
solvePurityConstraints (ρ_min, ρ_max) (PurityConstraints pc) = mconcat <$> mapM flattenComponent components where
	flattenComponent :: Tree Vertex -> Except (TCError Int Int) PuritySubstitution
	flattenComponent c = case (hasPure, hasMonadic) of
		(False, False) -> return $ PuritySubstitution varSet mempty
		(False, True ) -> return $ PuritySubstitution mempty (IM.fromSet (const Monadic) varSet)
		(True , False) -> return $ PuritySubstitution mempty (IM.fromSet (const Pure   ) varSet)
		(True , True ) -> throwError CannotEscapeMonad
		where
		(Any hasPure, Any hasMonadic, varSet) = foldMap inject c
		inject vertex | vertex == pure    = (Any True, mempty, mempty)
		              | vertex == monadic = (mempty, Any True, mempty)
		              | otherwise         = (mempty, mempty, IS.singleton vertex)

	components = scc (buildG (ρ_min, monadic) (minimalEdges ++ maximalEdges ++ constraintEdges))

	minimalEdges = [(pure, pv) | pv <- monadic:[ρ_min .. ρ_max-1]]
	maximalEdges = [(pv, monadic) | pv <- pure:[ρ_min .. ρ_max-1]]
	constraintEdges = [(vertex m, vertex m') | (m, m') <- pc]

	vertex (PurityVar pv) = pv
	vertex Pure = pure
	vertex Monadic = monadic

	pure = ρ_max
	monadic = succ pure

-- | It's on you to guarantee all the variables are unambiguous.
substExpr :: PuritySubstitution -> TargetExpr Int -> TargetExpr Void
substExpr (PuritySubstitution { psUnambiguous = im }) = go where
	go (TargetVar s) = TargetVar s
	go (TargetLambda s m0 m1 e) = TargetLambda s (resolve m0) (resolve m1) (go e)
	go (TargetApp m0 m1 m2 m3 e e') = TargetApp (resolve m0) (resolve m1) (resolve m2) (resolve m3) (go e) (go e')

	resolve Pure = Pure
	resolve Monadic = Monadic
	resolve (PurityVar pv) = im IM.! pv

-- | It's on you to guarantee all the variables are unambiguous.
substMTy :: Ord tv => PuritySubstitution -> Map tv (BareTy Int tv) -> MTy Int tv -> MTy Void tv
substMTy (PuritySubstitution { psUnambiguous = pvm }) tvm = goMTy where
	goMTy (MTy m ty) = MTy (resolve m) (goBareTy ty)

	goBareTy ty = case ty of
		TyVar tv -> case M.lookup tv tvm of
			Just ty' -> goBareTy ty'
			_ -> TyVar tv
		Base -> Base
		Arrow i o -> Arrow (goBareTy i) (goMTy o)

	resolve Pure = Pure
	resolve Monadic = Monadic
	resolve (PurityVar pv) = pvm IM.! pv
