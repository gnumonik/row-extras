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

module Data.Row.Extras.BiForallX where
  
import Data.Row
import Data.Kind
import Data.Row.Internal
import Data.Row.Dictionaries
import GHC.TypeLits.Singletons
import Data.Singletons
import Data.Singletons.Sigma
import Data.Functor.Identity
import Data.Bifunctor

-- | @BiForallX@ is exactly like @BiForall@ from Data.Row.Internal, except the constraint is of kind 
--   @:: Symbol -> k1 -> k2 -> Constraint@ instead of @k1 -> k2 -> Constraint@. 
-- 
--   This only exists to rewrite a few Data.Row.Records functions, but there's *probably* an actual 
--   use for it beyond that which I haven't thought of. 
class BiForallX (r1 :: Row k1) (r2 :: Row k2) (c :: Symbol -> k1 -> k2 -> Constraint) where
  -- | A metamorphism is an anamorphism (an unfold) followed by a catamorphism (a fold).
  biMetamorphX :: forall (p :: Type -> Type -> Type) (f :: Row k1 -> Row k2 -> Type) (g :: Row k1 -> Row k2 -> Type)
                        (h :: k1 -> k2 -> Type). Bifunctor p
              => Proxy (Proxy h, Proxy p)
              -> (f Empty Empty -> g Empty Empty)
              -> (forall ℓ τ1 τ2 ρ1 ρ2. (KnownSymbol ℓ, c ℓ τ1 τ2, HasType ℓ τ1 ρ1, HasType ℓ τ2 ρ2)
                  => Label ℓ -> f ρ1 ρ2 -> p (f (ρ1 .- ℓ) (ρ2 .- ℓ)) (h τ1 τ2))
              -> (forall ℓ τ1 τ2 ρ1 ρ2. ( KnownSymbol ℓ
                                        , c ℓ τ1 τ2
                                        , FrontExtends ℓ τ1 ρ1
                                        , FrontExtends ℓ τ2 ρ2
                                        , AllUniqueLabels (Extend ℓ τ1 ρ1)
                                        , AllUniqueLabels (Extend ℓ τ2 ρ2))
                  => Label ℓ 
                  -> p (g ρ1 ρ2) (h τ1 τ2) 
                  -> g (Extend ℓ τ1 ρ1) (Extend ℓ τ2 ρ2))
                  -> f r1 r2 
                  -> g r1 r2

instance BiForallX (R '[]) (R '[]) c1 where
  {-# INLINE biMetamorphX #-}
  biMetamorphX _ empty _ _ = empty

instance ( KnownSymbol ℓ
         , c ℓ τ1 τ2 
         , BiForallX ('R ρ1) ('R ρ2) c
         , FrontExtends ℓ τ1 ('R ρ1)
         , FrontExtends ℓ τ2 ('R ρ2)
         , AllUniqueLabels (Extend ℓ τ1 ('R ρ1))
         , AllUniqueLabels (Extend ℓ τ2 ('R ρ2)))
      => BiForallX ('R (ℓ :-> τ1 ': ρ1)) ('R (ℓ :-> τ2 ': ρ2)) c where
  {-# INLINE biMetamorphX #-}
  biMetamorphX h empty uncons cons = case (frontExtendsDict @ℓ @τ1 @('R ρ1), frontExtendsDict @ℓ @τ2 @('R ρ2)) of
    (FrontExtendsDict Dict, FrontExtendsDict Dict) ->
      cons (Label @ℓ) . first (biMetamorphX @_ @_ @('R ρ1) @('R ρ2) @c h empty uncons cons) . uncons (Label @ℓ)

