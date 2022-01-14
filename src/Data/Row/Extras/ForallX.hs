{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications, ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.Row.Extras.ForallX (ForallX(..)) where

import Data.Row
    ( KnownSymbol,
      AllUniqueLabels,
      Forall,
      Row,
      Empty,
      HasType,
      Label(..),
      type (.-) )
import Data.Kind ( Type, Constraint )
import Data.Row.Internal
    ( KnownSymbol,
      LT((:->)),
      FrontExtends(..),
      AllUniqueLabels,
      Extend,
      Forall,
      Unconstrained1,
      Row(..),
      Empty,
      HasType,
      Label(..),
      type (.-),
      FrontExtendsDict(FrontExtendsDict) )
import Data.Row.Dictionaries ( Unconstrained1, Dict(Dict) )
import Data.Singletons ( Proxy )
import Data.Bifunctor ( Bifunctor(first) )
import Data.Row.Records
    ( KnownSymbol,
      AllUniqueLabels,
      Extend,
      Forall,
      Row,
      Empty,
      HasType,
      Label(..),
      type (.-) )
import GHC.TypeLits (Symbol)
import Data.Constraint ( Constraint, Dict(Dict) )

type ForallX :: forall k. Row k -> (Symbol -> k -> Constraint) -> Constraint 
class Forall r Unconstrained1 => ForallX (r :: Row k) (c :: Symbol -> k -> Constraint) -- (c' :: Symbol -> Constraint) 
  where
  metamorphX :: forall (p :: Type -> Type -> Type) 
                       (f :: Row k -> Type) 
                       (g :: Row k -> Type) 
                       (h :: k -> Type)
             . Bifunctor p
            => Proxy (Proxy h, Proxy p)
            -> (f Empty -> g Empty)
               -- ^ The way to transform the empty element
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c ℓ τ, HasType ℓ τ ρ)
               => Label ℓ -> f ρ -> p (f (ρ .- ℓ)) (h τ))
               -- ^ The unfold
            -> (forall ℓ τ ρ. (KnownSymbol ℓ, c ℓ τ, FrontExtends ℓ τ ρ, AllUniqueLabels (Extend ℓ τ ρ))
               => Label ℓ -> p (g ρ) (h τ) -> g (Extend ℓ τ ρ))
               -- ^ The fold
            -> f r  -- ^ The input structure
            -> g r 

instance ForallX (R '[]) c  where
  {-# INLINE metamorphX #-}
  metamorphX _ empty _ _ = empty

instance (KnownSymbol ℓ, c ℓ τ, ForallX ('R ρ) c, FrontExtends ℓ τ ('R ρ), AllUniqueLabels (Extend ℓ τ ('R ρ))) => ForallX ('R (ℓ :-> τ ': ρ) :: Row k) c where
  {-# INLINE metamorphX #-}
  metamorphX h empty uncons cons = case frontExtendsDict @ℓ @τ @('R ρ) of
    FrontExtendsDict Dict ->
      cons (Label @ℓ) . first (metamorphX @_ @('R ρ) @c h empty uncons cons) . uncons (Label @ℓ)