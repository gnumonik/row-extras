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
    ( Constraint, type (:-), Dict(..), (\\), unmapDict )
import Data.Kind ( Type )
import qualified Data.Row.Records as R
import Data.Singletons (Proxy (Proxy))
import Data.Row.Dictionaries ( mapHas )
import Data.Row.Variants (AllUniqueLabels)
import Data.Type.Equality ( type (:~:)(..) ) 
import qualified Unsafe.Coerce as UNSAFE 

import Data.Row.Extras.Util ( Coherent(..) )


-- This is a GADT which holds a dictionary. Here, it is used to implement `forall`, 
-- although it serves other purposes in the rest of the library
data Constrained (c :: k -> Constraint) :: k -> Type where
  Constrained :: forall k (c :: k -> Constraint) (a :: k)
               . Dict (c a) ->  Constrained c a

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
    key = R.transform @c @r @Proxy @(Constrained c) go2 (represent (Proxy @r))

    go2 :: forall a. c a => Proxy a -> Constrained c a
    go2 _ = Constrained Dict 

{- It should be possible to write a `forallX` function...-}

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