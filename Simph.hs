{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
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

data SourceExpr
	= SourceVar String
	| SourceLambda (Purity Void) String SourceExpr
	| SourceApp SourceExpr SourceExpr
	| SourceCase SourceExpr [(Pattern, SourceExpr)]
	| SourceAscription SourceExpr (MTy String String)
	deriving (Eq, Ord, Read, Show)

data Pattern = PatternVar String | PatternConstructor String [Pattern]
	deriving (Eq, Ord, Read, Show)

-- | Returns Left if it tries to bind a single variable twice.
patBindings :: Pattern -> Either String (Set String)
patBindings (PatternVar s) = Right (S.singleton s)
patBindings (PatternConstructor _ pats) = mapM patBindings pats >>= disjointUnion where
	disjointUnion [] = Right S.empty
	disjointUnion (s:ss) = do
		s' <- disjointUnion ss
		if S.disjoint s s' then Right (S.union s s') else Left (S.elemAt 0 (S.intersection s s'))

data TargetExpr pv
	= TargetVar String
	| TargetLambda String (TargetExpr pv)
	| TargetApp (Purity pv) (Purity pv) (Purity pv) (Purity pv) (Purity pv) (TargetExpr pv) (TargetExpr pv)
	| TargetCase (Purity pv) (TargetExpr pv) [(Pattern, TargetExpr pv)]
	| TargetLift (Purity pv) (Purity pv) (TargetExpr pv)
	deriving (Eq, Ord, Read, Show)

data Purity pv = PurityVar pv | Pure | Monadic
	deriving (Eq, Ord, Read, Show, Functor)

data BareTy pv tv = TyVar tv | Base | Arrow (MTy pv tv) (MTy pv tv)
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

data Container = None | AppL | AppR deriving (Bounded, Enum, Eq, Ord, Read, Show)

class PrettyPrec a where
	prettyPrec :: Container -> a -> Doc ann

parensIf False = id
parensIf True  = parens

instance Pretty SourceExpr where pretty = prettyPrec None
instance PrettyPrec SourceExpr where
	prettyPrec _ (SourceVar v) = pretty v
	prettyPrec c (SourceLambda m v body)
		= parensIf (c /= None)
		. nest 4
		$ pretty "\\" <> sep
			[ hsep [pretty v, pretty $ if m == Pure then "->" else ">->"]
			, pretty body
			]
	prettyPrec c (SourceApp e e')
		= parensIf (c == AppR)
		. nest 4
		$ sep [prettyPrec AppL e, prettyPrec AppR e']
	prettyPrec c (SourceCase scrutinee clauses)
		= parensIf (c /= None)
		. nest 4
		. mconcat
		. punctuate hardline
		$ hsep [pretty "case", pretty scrutinee, pretty "of"]
		: [ hsep [pretty pat, pretty "->", pretty e]
		  | (pat, e) <- clauses
		  ]
	prettyPrec c (SourceAscription e mty)
		= parensIf (c /= None)
		. nest 4
		$ sep [prettyPrec AppL e, pretty ":: " <> pretty mty]

instance Pretty Pattern where pretty = prettyPrec None
instance PrettyPrec Pattern where
	prettyPrec _ (PatternVar v) = pretty v
	prettyPrec _ (PatternConstructor constructor []) = pretty constructor
	prettyPrec c (PatternConstructor constructor pats)
		= parensIf (c == AppR)
		$ hsep (pretty constructor : map (prettyPrec AppR) pats)

instance (Eq pv, Pretty pv) => Pretty (TargetExpr pv) where pretty = prettyPrec None
instance (Eq pv, Pretty pv) => PrettyPrec (TargetExpr pv) where
	prettyPrec _ (TargetVar v) = pretty v
	prettyPrec c (TargetLambda v body)
		= parensIf (c /= None)
		. nest 4
		$ pretty "\\" <> sep [pretty v <> pretty " ->", pretty body]
	prettyPrec c (TargetApp m marg mres m' mfullres e e') = parensIf (c == AppR) . nest 4 . sep $ case app of
		Just doc -> [doc, prettyPrec AppR e, prettyPrec AppR e']
		Nothing ->  [     prettyPrec AppL e, prettyPrec AppR e']
		where
		app = case (m, marg, mres, m', mfullres) of
			(Pure, _, _, _, _) | marg == m' && mres == mfullres -> Nothing
			(Monadic, _, Monadic, _, Monadic) | marg == m' -> Just $ pretty "(\\f x -> (f >>=) . ($x))"
			(Monadic, Monadic, Monadic, Pure, Monadic) -> Just $ pretty "(\\f x -> f <&> ($return x))"
			-- TODO: more special cases
			_ -> Just . parens $ sep
				[ pretty "app ::"
				, pretty (Arrow (MTy m (Arrow (MTy marg voidBase) (MTy mres voidBase))) (MTy Pure (Arrow (MTy m' voidBase) (MTy mfullres voidBase))))
				]
	-- TODO: use m, lol
	prettyPrec c (TargetCase m scrutinee clauses)
		= parensIf (c /= None)
		. nest 4
		. vsep
		$ [ hsep [pretty "case", pretty scrutinee, pretty "of"]
		  , braces . vsep . punctuate (pretty ";") $
		  	[ nest 4 $ sep [pretty pat <> pretty " ->", pretty e]
		  	| (pat, e) <- clauses
		  	]
		  ]
	-- TODO: specialize for when there are no purity variables
	prettyPrec c (TargetLift msrc mtgt e)
		= parensIf (c == AppR)
		. nest 4
		. sep
		$ [ parens $ sep
		  	[ pretty "lift ::"
		  	, pretty (Arrow (MTy msrc voidBase) (MTy mtgt voidBase))
		  	]
		  , prettyPrec AppR e
		  ]

voidBase :: BareTy pv Void
voidBase = Base

instance Pretty pv => Pretty (Purity pv) where
	pretty Pure = pretty "Id"
	pretty Monadic = pretty "m"
	pretty (PurityVar pv) = pretty "ρ" <> pretty pv

instance (Pretty pv, Pretty tv) => Pretty (BareTy pv tv) where pretty = prettyPrec None
instance (Pretty pv, Pretty tv) => PrettyPrec (BareTy pv tv) where
	prettyPrec _ (TyVar tv) = pretty "α" <> pretty tv
	prettyPrec _ Base = pretty "_"
	prettyPrec c (Arrow i o)
		= parensIf (c /= None)
		. nest 4
		$ sep [prettyPrec AppL i, pretty "-> " <> pretty o]

instance (Pretty pv, Pretty tv) => Pretty (MTy pv tv) where pretty = prettyPrec None
instance (Pretty pv, Pretty tv) => PrettyPrec (MTy pv tv) where
	prettyPrec c (MTy Pure bty) = prettyPrec c bty
	prettyPrec _ (MTy m bty) = nest 4 $ sep [pretty m, prettyPrec AppR bty]

instance Pretty pv => Pretty (PurityConstraints pv) where
	pretty (PurityConstraints cs) = braces . sep . punctuate comma
		$  [hsep [pretty m, pretty "≤", pretty m'] | (m, m') <- cs]

instance (Eq pv, Pretty pv, Pretty tv) => Pretty (Compilation pv tv) where
	pretty (Compilation eh ty) = sep
		[ pretty eh
		, hsep [pretty "::", pretty ty]
		]

simpleEnv :: Env pv tv
simpleEnv = M.fromList
	[ ("print", MTy Pure (Arrow (MTy Pure Base) (MTy Monadic Base)))
	, ("readLn", MTy Monadic Base)
	, ("plus", MTy Pure (Arrow (MTy Pure Base) (MTy Pure (Arrow (MTy Pure Base) (MTy Pure Base)))))
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
unifyCanonical (Arrow i o) (Arrow i' o') = unifyM i i' >> unifyM o o'
unifyCanonical ty ty' = throwError (TypeError ty ty')

unify :: Ctx pv tv => BareTy pv tv -> BareTy pv tv -> TC pv tv ()
unify ty_ ty_' = do
	ty  <- canonVar ty_
	ty' <- canonVar ty_'
	unifyCanonical ty ty'

unifyM :: Ctx pv tv => MTy pv tv -> MTy pv tv -> TC pv tv ()
unifyM (MTy m ty) (MTy m' ty') = do
	m  ≤ m'
	m' ≤ m
	unify ty ty'

freshenUserMTy :: Ctx pv tv => MTy String String -> TC pv tv (MTy pv tv)
freshenUserMTy mty = snd <$> goMTy M.empty M.empty mty where
	goMTy pvs tvs (MTy m ty) = do
		(pvs', m') <- goM pvs m
		(res, ty') <- goBareTy pvs' tvs ty
		return (res, MTy m' ty')

	goM pvs m = case m of
		PurityVar pv -> do
			ρ <- maybe freshPV return $ M.lookup pv pvs
			return (M.insert pv ρ pvs, ρ)
		Pure -> return (pvs, Pure)
		Monadic -> return (pvs, Monadic)

	goBareTy pvs tvs ty = case ty of
		TyVar tv -> do
			α <- maybe freshTV return $ M.lookup tv tvs
			return ((pvs, M.insert tv α tvs), α)
		Base -> return ((pvs, tvs), Base)
		Arrow i o -> do
			((pvs' , tvs' ), i') <- goMTy pvs  tvs  i
			((pvs'', tvs''), o') <- goMTy pvs' tvs' o
			return ((pvs'', tvs''), Arrow i' o')

infer :: Ctx pv tv => SourceExpr -> TC pv tv (Compilation pv tv)
infer (SourceVar v) = asks (M.lookup v) >>= \mty -> case mty of
	Nothing -> throwError (NotInScope v)
	Just ty -> return (Compilation (TargetVar v) ty)

infer (SourceLambda m_ v e) = do
	mty <- asks (M.lookup v)
	when (isJust mty) (throwError (AlreadyInScope v))
	α <- freshTV
	Compilation eh (MTy m' ty) <- local (M.insert v (MTy m α)) (infer e)
	ρ <- freshPV
	m' ≤ ρ
	return (Compilation (TargetLambda v (TargetLift m' ρ eh)) (MTy Pure (Arrow (MTy m α) (MTy ρ ty))))
	where m = absurd <$> m_

infer (SourceApp e e') = do
	Compilation eh  (MTy m  ty ) <- infer e
	Compilation eh' (MTy m' ty') <- infer e'
	ρ   <- freshPV
	ρ'  <- freshPV
	ρ'' <- freshPV
	α   <- freshTV
	unify ty (Arrow (MTy ρ ty') (MTy ρ' α))
	ρ  ≤ ρ''
	ρ' ≤ ρ''
	m  ≤ ρ''
	m' ≤ ρ''
	return (Compilation (TargetApp m ρ ρ' m' ρ'' eh eh') (MTy ρ'' α))

infer (SourceCase scrutinee clauses) = do
	Compilation eh (MTy m ty) <- infer scrutinee
	unify ty Base
	compilations <- forM clauses $ \(pat, e') -> case patBindings pat of
		Left var -> throwError (AlreadyInScope var)
		Right vars -> do
			env <- ask
			let env' = M.fromSet (const (MTy Pure Base)) vars
			    sharedEnv = M.intersection env env'
			if M.null sharedEnv
				then local (M.union env') (infer e')
				else throwError (AlreadyInScope (fst (M.elemAt 0 sharedEnv)))
	ρ <- freshPV
	α <- freshTV
	m ≤ ρ
	forM compilations $ \(Compilation _ (MTy m' ty')) -> do
		m' ≤ ρ
		unify ty' α
	let clauses' = zipWith (\(pat, _) (Compilation eh' _) -> (pat, eh')) clauses compilations
	return (Compilation (TargetCase m eh clauses') (MTy ρ α))

infer (SourceAscription e userMTy) = do
	Compilation eh mty <- infer e
	mty' <- freshenUserMTy userMTy
	unifyM mty mty'
	return (Compilation eh mty')

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
	go (TargetLambda s e) = TargetLambda s (go e)
	go (TargetApp m0 m1 m2 m3 m4 e e') = TargetApp (resolve m0) (resolve m1) (resolve m2) (resolve m3) (resolve m4) (go e) (go e')
	go (TargetCase m scrutinee clauses) = TargetCase (resolve m) (go scrutinee) [(pat, go e) | (pat, e) <- clauses]
	go (TargetLift m m' e) = TargetLift (resolve m) (resolve m') (go e)

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
		Arrow i o -> Arrow (goMTy i) (goMTy o)

	resolve Pure = Pure
	resolve Monadic = Monadic
	resolve (PurityVar pv) = pvm IM.! pv
