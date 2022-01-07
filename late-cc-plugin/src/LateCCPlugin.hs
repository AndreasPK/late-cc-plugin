{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE CPP #-}

module LateCCPlugin where

import GHC.Plugins
import Control.Applicative
import Control.Monad.State.Strict
import Control.Monad

import GHC.Prelude
import GHC.Utils.Outputable as Outputable
import GHC.Driver.Session
import GHC.Types.CostCentre
import GHC.Types.CostCentre.State
import GHC.Types.Name hiding (varName)
-- import GHC.Types.Tickish
-- import GHC.Unit.Module.ModGuts
import GHC.Types.Var
import GHC.Unit.Types
import GHC.Data.FastString
import GHC.Core
import GHC.Core.Opt.Monad
import GHC.Types.Id

#if __GLASGOW_HASKELL__ >= 902
import GHC.Types.Tickish
#endif
import GHC.Core
-- import GHC.Types.Tickish

plugin :: Plugin
plugin = defaultPlugin {
  installCoreToDos = install
  }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = do
  return (todo ++ [lateCCPass])

lateCCPass :: CoreToDo
lateCCPass = CoreDoPluginPass "late-cc-plugin" addLateCostCentres

addLateCostCentres :: ModGuts -> CoreM ModGuts
addLateCostCentres guts = do
  dflags <- getDynFlags
  let env :: Env
      env = Env
        { thisModule = mg_module guts
        , ccState = newCostCentreState
        , dflags = dflags
        }
  let guts' = guts { mg_binds = doCoreProgram env (mg_binds guts)
                   }
  return guts'

doCoreProgram :: Env -> CoreProgram -> CoreProgram
doCoreProgram env binds = flip evalState newCostCentreState $ do
    mapM (doBind env) binds

doBind :: Env -> CoreBind -> M CoreBind
doBind env (NonRec b rhs) = NonRec b <$> doBndr env b rhs
doBind env (Rec bs) = Rec <$> mapM doPair bs
  where
    doPair :: ((Id, CoreExpr) -> M (Id, CoreExpr))
    doPair (b,rhs) = (b,) <$> doBndr env b rhs

doBndr :: Env -> Id -> CoreExpr -> M CoreExpr
doBndr env bndr rhs = do
    -- pprTraceM "dobnd" (ppr bndr)
    let name = idName bndr
        name_loc = nameSrcSpan name
        cc_name = getOccFS name
        count = gopt Opt_ProfCountEntries (dflags env)
    cc_flavour <- (getCCExprFlavour cc_name) -- (ccState env)
    let cc_mod = thisModule env
        bndrCC = NormalCC cc_flavour cc_name cc_mod name_loc
        note = ProfNote bndrCC count True
    return $ LateCCPlugin.mkTick note rhs

type M = State CostCentreState

getCCExprFlavour :: FastString -> M CCFlavour
getCCExprFlavour name = ExprCC <$> getCCIndex' name

getCCIndex' :: FastString -> M CostCentreIndex
getCCIndex' name = state (getCCIndex name)

data Env = Env
  { thisModule  :: Module
  , dflags      :: DynFlags
  , ccState     :: CostCentreState
  }

-- | Wraps the given expression in the source annotation, dropping the
-- annotation if possible.
-- mkTick :: CoreTickish -> CoreExpr -> CoreExpr
mkTick t orig_expr = mkTick' id id orig_expr
 where
  -- Some ticks (cost-centres) can be split in two, with the
  -- non-counting part having laxer placement properties.
  canSplit = tickishCanSplit t && tickishPlace (mkNoCount t) /= tickishPlace t

  mkTick' :: (CoreExpr -> CoreExpr) -- ^ apply after adding tick (float through)
          -> (CoreExpr -> CoreExpr) -- ^ apply before adding tick (float with)
          -> CoreExpr               -- ^ current expression
          -> CoreExpr
  mkTick' top rest expr = case expr of

    -- Cost centre ticks should never be reordered relative to each
    -- other. Therefore we can stop whenever two collide.
    Tick t2 e
      | ProfNote{} <- t2, ProfNote{} <- t -> top $ Tick t $ rest expr

    -- Otherwise we assume that ticks of different placements float
    -- through each other.
      | tickishPlace t2 /= tickishPlace t -> mkTick' (top . Tick t2) rest e

    -- For annotations this is where we make sure to not introduce
    -- redundant ticks.
      | tickishContains t t2              -> mkTick' top rest e
      | tickishContains t2 t              -> orig_expr
      | otherwise                         -> mkTick' top (rest . Tick t2) e

    -- Ticks don't care about types, so we just float all ticks
    -- through them. Note that it's not enough to check for these
    -- cases top-level. While mkTick will never produce Core with type
    -- expressions below ticks, such constructs can be the result of
    -- unfoldings. We therefore make an effort to put everything into
    -- the right place no matter what we start with.
    Cast e co   -> mkTick' (top . flip Cast co) rest e
    Coercion co -> Coercion co

    Lam x e
      -- Always float through type lambdas. Even for non-type lambdas,
      -- floating is allowed for all but the most strict placement rule.
      | not (isRuntimeVar x) || tickishPlace t /= PlaceRuntime
      -> mkTick' (top . Lam x) rest e

      -- If it is both counting and scoped, we split the tick into its
      -- two components, often allowing us to keep the counting tick on
      -- the outside of the lambda and push the scoped tick inside.
      -- The point of this is that the counting tick can probably be
      -- floated, and the lambda may then be in a position to be
      -- beta-reduced.
      | canSplit
      -> top $ Tick (mkNoScope t) $ rest $ Lam x $ LateCCPlugin.mkTick (mkNoCount t) e

    App _f _arg
      -- See Note [Float runtime ticks through type applications]
      -- -- Always float through type applications.
      -- | not (isRuntimeArg arg) && tickishPlace t /= PlaceRuntime
      -- -> mkTick' (top . flip App arg) rest f

      -- We can also float through constructor applications, placement
      -- permitting. Again we can split.
      | LateCCPlugin.isSaturatedConApp expr && (tickishPlace t==PlaceCostCentre || canSplit)
      -> if tickishPlace t == PlaceCostCentre
         then top $ rest $ tickHNFArgs t expr
         else top $ Tick (mkNoScope t) $ rest $ tickHNFArgs (mkNoCount t) expr

    Var x
      | notFunction && tickishPlace t == PlaceCostCentre
      -> orig_expr
      | notFunction && canSplit
      -> top $ Tick (mkNoScope t) $ rest expr
      where
        -- SCCs can be eliminated on variables provided the variable
        -- is not a function.  In these cases the SCC makes no difference:
        -- the cost of evaluating the variable will be attributed to its
        -- definition site.  When the variable refers to a function, however,
        -- an SCC annotation on the variable affects the cost-centre stack
        -- when the function is called, so we must retain those.
        notFunction = not (isFunTy (idType x))

    Lit{}
      | tickishPlace t == PlaceCostCentre
      -> orig_expr

    -- Catch-all: Annotate where we stand
    _any -> top $ Tick t $ rest expr

isSaturatedConApp :: CoreExpr -> Bool
isSaturatedConApp e = go e []
  where go (App f a) as = go f (a:as)
        go (Var fun) args
           = isConLikeId fun && idArity fun == valArgCount args
        go (Cast f _) as = go f as
        go _ _ = False