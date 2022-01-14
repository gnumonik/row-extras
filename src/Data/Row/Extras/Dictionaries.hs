{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications, ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE FlexibleInstances, OverloadedLabels #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Row.Extras.Dictionaries (
  forall,
  ui,
  forallX,
  uiX,
  unique,
  UniquenessProof(..),
  mkUniquenessProof
) where
  
import Data.Row
    ( KnownSymbol,
      AllUniqueLabels,
      Forall,
      HasType,
      Label(Label),
      Rec,
      (.!) )
import Data.Constraint
    ( Constraint, type (:-), Dict(..), (\\), unmapDict, mapDict )
import Data.Kind ( Type )
import qualified Data.Row.Records as R
import Data.Singletons (Proxy (Proxy), Sing, SingI (sing))
import Data.Row.Dictionaries ( mapHas )
import Data.Row.Variants (AllUniqueLabels)
import Data.Type.Equality ( type (:~:)(..) ) 
import qualified Unsafe.Coerce as UNSAFE 
import GHC.TypeLits.Singletons (Symbol)

import Data.Row.Extras.Util ( Coherent(..) )
import Data.Row.Extras.ForallX (ForallX)
import Data.Row.Extras.Records (transformX)


-- This is a GADT which holds a dictionary. Here, it is used to implement `forall`, 
data Constrained (c :: k -> Constraint) :: k -> Type where
  Constrained :: forall k (c :: k -> Constraint) (a :: k)
               . Dict (c a) -> Constrained c a

-- This is a GADT which holds a dictionary. Here, it is used to implement `forall`, 
data ConstrainedX (c :: Symbol -> k -> Constraint) :: k -> Type where
  ConstrainedX :: forall k (c :: Symbol -> k -> Constraint) (a :: k) (l :: Symbol)
               . Sing l -> Dict (c l a) ->  ConstrainedX c a

-- | Universal instantiation for Rows. If some row satisfies `Forall r c` then, 
-- if we know that `t` is an element of that row, we also know that `t` satisfies `c`. 
--
-- The `row-types` package doesn't include this entailment, but I needed it, so I made it. 
forall :: forall r c l t
        . (Coherent r
        ,  Forall r c
        ,  KnownSymbol l
        ) => HasType l t r :- c t -- This is the newtype for constraint entailment from Data.Constraint 
forall = unmapDict go             -- If you have a dict: myDict = Dict @(HasType l t r), you can 
  where                           -- use `mapDict (forall @r @c @l @t) myDict` to get a `Dict @(c t)`
                                  -- (This lets us do things that wouldn't otherwise typecheck due to escaped skolems)
    go :: Dict (HasType l t r) -> Dict (c t)
    go Dict = case key .! (Label @l) \\ mapHas @(Constrained c) @l @t @r of 
      Constrained d -> d 
    
    key :: Rec (R.Map (Constrained c) r)
    key = R.transform @c @r @Proxy @(Constrained c) mkKey (represent (Proxy @r))
      where 
        mkKey:: forall a. c a => Proxy a -> Constrained c a
        mkKey _ = Constrained Dict 

-- | Produce the dictionary for (c t) directly when @(HasType l t r, Forall r c, KnownSymbol l, Coherent r)@
-- are satisfied. 
ui :: forall l c r t 
      . ( Coherent r 
        , Forall r c 
        , KnownSymbol l 
        , HasType l t r 
      ) => Dict (c t)
ui = mapDict (forall @r @c @l @t) Dict 

-- | Like @forall@ but for @ForallX@. Needs to use @unsafeCoerce@ under the hood.
forallX :: forall r c l t 
         . ( Coherent r 
         ,   ForallX r c
         ,   KnownSymbol l
         ) => HasType l t r :- c l t 
forallX = unmapDict goA 
  where 
    key :: Rec (R.Map (ConstrainedX c) r) 
    key = transformX @_ @c @r @Proxy @(ConstrainedX c) mkCX (represent (Proxy @r))
      where 
        mkCX :: forall l' a. KnownSymbol l' => Dict (c l' a) -> Proxy a -> ConstrainedX c a
        mkCX d _ = ConstrainedX (sing @l') d 

    goA :: Dict (HasType l t r) -> Dict (c l t)
    goA Dict = goB (key .! (Label @l) \\ mapHas @(ConstrainedX c) @l @t @r )
      where 
        goB :: ConstrainedX c t -> Dict (c l t) 
        goB (ConstrainedX l d) = goC l d 
          where 
            goC :: forall (l' :: Symbol). Sing l' -> Dict (c l' t) -> Dict (c l t) 
            goC sl d = case UNSAFE.unsafeCoerce Refl :: l' :~: l of -- this is safe here because of the way that `key` is 
              Refl -> d                                             -- constructed. the only label available to `mkCX` is the correct one, 
                                                                    -- but we can't prove the equality to GHC and it would be                                    
                                                                    -- absurdly unsafe *in general*. 

-- | Produce the dictionary for (c l t) directly when @(HasType l t r, ForallX r c, KnownSymbol l, Coherent r)@
-- are satisfied. 
uiX :: forall l c r t 
      . ( Coherent r 
        , ForallX r c 
        , KnownSymbol l 
        , HasType l t r 
      ) => Dict (c l t)
uiX = mapDict (forallX @r @c @l @t) Dict 


-- | Uniqueness axiom. If some row r has type t at label l,
--   and all the labels in r are unique, then we know that 
--   every other type at label l in r has to be equal to t
unique :: forall l t t' r 
        . (HasType l t r
        ,  HasType l t' r
        ,  AllUniqueLabels r) 
       => t :~: t' 
unique = UNSAFE.unsafeCoerce Refl 

-- | A "Boxed" uniqueness proof. It's conceivable that you might want to 
--   "stash" a uniqueness proof for some label/type/row for use in some other scope, 
--   and this lets you do that.
newtype UniquenessProof l t r 
  = UniquenessProof {proveUnique :: forall t'. HasType l t' r => t :~: t}

mkUniquenessProof :: forall l t r 
                   . (HasType l t r, AllUniqueLabels r) 
                   => UniquenessProof l t r 
mkUniquenessProof = UniquenessProof go 
  where 
    go :: forall t'. HasType l t' r => t :~: t' 
    go = unique @l @t @t' @r 