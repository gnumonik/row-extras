{-# LANGUAGE RankNTypes, TemplateHaskell #-}
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
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE LambdaCase, MultiWayIf #-}

module Data.Row.Extras.Dictionaries where
  
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
data ConstrainT (c :: k -> Constraint) :: k -> Type where
  ConstrainT :: forall k (c :: k -> Constraint) (a :: k)
               . Dict (c a) ->  ConstrainT c a

-- Universal instantiation for Rows. If some row satisfies `Forall r c` then, 
-- presumably, if we know that `t` is an element of that row, we should also know that `t` 
-- satisfies `c. The `row-types` package doesn't include this entailment, but I needed it, so I made it. 
forall :: forall r c l t
        . (Coherent r
        ,  Forall r c
        ,  KnownSymbol l
        ) => HasType l t r :- c t -- This is the newtype for constraint entailment from Data.Constraint 
forall = unmapDict go             -- If you have a dict: myDict = Dict @(HasType l t r), you can 
  where                           -- use `mapDict (forall @r @c @l @t) myDict` to get a `Dict @(c t)`
                                  -- (This lets us do things that wouldn't otherwise typecheck due to escaped skolems)
                                  -- This is *extremely* powerful when combined with a uniqueness axiom (which isn't included here because 
                                  -- I don't use it in this module )
    go :: Dict (HasType l t r) -> Dict (c t)
    go Dict = case key .! (Label @l) \\ mapHas @(ConstrainT c) @l @t @r of 
      ConstrainT d -> d 
    
    key :: Rec (R.Map (ConstrainT c) r)
    key = R.transform @c @r @Proxy @(ConstrainT c) go2 (represent (Proxy @r))

    go2 :: forall a. c a => Proxy a -> ConstrainT c a
    go2 _ = ConstrainT Dict 

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