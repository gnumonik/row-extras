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

module Data.Row.Extras.ApplyRow (
  Functorially(..), 
  Applicatively(..),

) where
import Data.Row
import Data.Singletons
import Data.Kind
import Data.Constraint
import GHC.TypeLits.Singletons (Symbol, withKnownSymbol)
import Data.Row.Extras.ForallX
import qualified Data.Row.Records as R
import Data.Row.Extras.Records
import Data.Row.Extras.Util
import Data.Functor.Identity
import Data.Row.Extras.Dictionaries (forall)
import qualified Unsafe.Coerce as UNSAFE
import Data.Row.Dictionaries (mapHas)

{- 

This module is experimental. It defines a set of data types, type classes, and functions which 
allow for paramaterizing some (r :: Row Type) over some (rp :: Row (Type ~> Type)). The API is 
rudimentary ATM but, assuming everything is solid here, it should be possible to extend this in 
a bunch of interesting ways.

-}


-- | Special GADT which holds this thing together. If we have one of these, we have evidence: 
--
--    1) That the first type argument (rp :: Row (k ~> Type)) is well behaved. This isn't relevant here, but 
--       WellBehaved entails AllUniqueLabels, so if we know that `rp` is WellBehaved and that it has some (p :: k ~> Type) at 
--       label `l`, then we can use the uniqueness axiom to assert that *any* type which rp has at label `l` must be equal to 
--       `t` 
-- 
--
--    2) That rp has a (p :: k ~> Type) at label l 
-- 
--
-- It also contains an existentially hidden  singleton for the symbol which serves as the label for `p` in `rp`, and an instance of the type which 
-- results from applying `p` to `t`. We need a singleton (vs a KnownSymbol constraint) and a Dict (vs an implicit constraint) for pretty much 
-- everything to typecheck. GHC can cope with a Dict or a Singleton inside of nested CPS "existential elimination" functions, but it gets very angry
-- when you try to introduce a constraint in those functions, so we'd have to convert to this from the implicit version anyway if we went down that road
--
-- (This is kind polymorphic and works where `k` is `Type` but also where it is not)
data Of :: Row (k ~> Type) -> k -> Type where 
  Of :: forall k (rp :: Row (k ~> Type)) (p :: k ~> Type) (l :: Symbol) (t :: k) 
      . ( WellBehaved rp 
      ) => Dict (HasType l p rp) 
        -> Sing l 
        -> p @@ t 
        -> Of rp t 

-- This is the existential eliminator for `Of`
withOf :: forall rp t r
        . Of rp t 
       -> (forall l (p :: Type ~> Type). WellBehaved rp => Dict (HasType l p rp) -> Sing l -> p @@ t -> r) 
       -> r 
withOf (Of d sl pa) f = f d sl pa 

-- | Defunctionalized/partially applied functors and applicatives
-- In the context of this excerpt these just help with type inference a bit. In the library I split this package 
-- off of, I do a lot of things with those defunctionalized type functions (things of kind :: k ~> Type), so the real reason these 
-- use the squiggly arrows is for parsimony/compatibility 
-- 
-- In case you're wondering: Something of kind (k ~> Type) can be "matched on" in things like typeclass instances/etc  
-- (that's what makes it different from something of kind (k -> Type)). That's a lot more important when `k` is NOT `Type`
-- 
-- These are subtly distinct from Functor/Applicative/Monad in that there isn't a superclass relation between them. 
-- This is because there *might* be some space for useful instances of these that strictly can't be given functor/applicative/monad
-- instances. (It might even make sense to split off `purely` from `aply`, since we can define aply for a bunch of comonads that we can't 
-- define purely for)
class Functorially (p :: Type ~> Type) where 
  fmaply :: forall (a :: Type) (b :: Type)          
          . (a -> b) -> p @@ a -> p @@ b 

instance Functor f => Functorially (TyCon1 f) where 
  fmaply = fmap  

class Functorially p => Applicatively (p :: Type ~> Type) where 
  purely :: forall (a :: Type). a -> p @@ a 

  aply :: forall  (a :: Type) (b :: Type)
            . p @@ (a -> b) -> p @@ a -> p @@ b 

instance (Applicative f) => Applicatively (TyCon1 f) where 
  purely = pure 

  aply pf pa =  pf <*> pa 

-- | `ApplyRow r l t` is a class constraint satisfies by every (rp :: Row (Type ~> Type)), (l :: Symbol), and Type such that, 
-- we can "inject" the type into (Of rp)`. In practice we use this with ForallX (see the `implement` function below) as something like 
-- a "pure" (from Control.Applicative) for rows of applicative functors. 
type ApplyRow :: Row (Type ~> Type) -> Symbol -> Type -> Constraint 
class ( forall (p :: Type ~> Type). HasType l p rp => Applicatively p -- Ok to be fair I don't know that I need this but if I do it's 
      , KnownSymbol l) => ApplyRow rp l t where                     -- *really* nice to have it. (See `implied` in Data.Constraint) 
            liftT :: t -> Of rp t                                      
                                                                  
instance ( Applicatively p
         , HasType l p rp 
         , WellBehaved rp 
         , KnownSymbol l
         ) => ApplyRow rp l t where  
              liftT t = Of Dict (sing @l) (purely @p t)

-- | @Applied@ is a wrapper around `Rec (R.Map (Of rp) rt)` and uses applyRow as a kind of smart constructor.  
-- A record with that type signature,  *so long as it was constructed with the `applyRow` function*, holds a collection of elements paramterized by the 
-- functor at their label in the parameter row (of kind :: Type ~> Type) 
-- 
-- This structure enforces some odd invariants: Every element of (R.Map (Of rp) rt) is an `Of rp x` GADT which contains a singleton of a symbol which 
-- serves as the label for some predicate in `rp`, for some `x` which (due to R.Map (Of rp)) *must* exist at label `l` in `rt`. As far as I can tell, it is 
-- *impossible* (even with fancy Sigma stuff from the singletons library) to enforce that the singleton symbol inside `Of rp` matches the 
-- label of `x` in `rt`. 
-- 
-- That is, in theory you could have (Of rp x) with the "wrong" functor inside (because the type of the functor depends on the symbol). Fortunately, 
-- this can be alleviated in practice by not exporting the `MkImplementation` constructor. 
newtype Applied :: Row (Type ~> Type) -> Row Type -> Type where 
  MkApplied :: forall (rp :: Row (Type ~> Type)) (rt :: Row Type)  
                    . Rec (R.Map (Of rp) rt) 
                   -> Applied rp rt 

-- | Creates an `Applied`. The first type argument (needs a type application) is the parameter row (the row of functors).
--   As mentioned above, this is roughly analogous to "pure". 
applyRow :: forall rp rt
           . ForallX rt (ApplyRow rp)
          => Rec rt 
          -> Applied rp rt 
applyRow r = MkApplied $ mapX @rt @(Of rp) @(ApplyRow rp) go r
  where 
    go :: forall (l :: Symbol) (a :: Type)
        . Dict (ApplyRow rp l a) 
       -> Sing l  
       -> a 
       -> Of rp a 
    go d@Dict sl = liftT @rp @l @a 

-- |  `FMap l rp rt rt' a b` is a class constraint satisfied when you can transform one row (rt) into another row 
-- (rt') by replacing the (Of rp a) at label l with an (Of rp b). 
-- 
-- Since (Of rp) is just a weird row-parameterized container for some functor applied to some type, transforming (Of rp a) 
-- into (Of rp b) is, as the class name might indicate, a kind of generalized fmap. 
class ( KnownSymbol l
      , Coherent rp  
      , Forall rp Functorially  
      , HasType l (Of rp b) rt'  
      , HasType l (Of rp a) rt 
      , rt' ~ R.Modify l (Of rp b) rt
      , rt  ~ R.Modify l (Of rp a) rt' 
      ) => FMap l rp rt rt' a b 
  where 
    fmaprec :: (a -> b) -> Rec rt -> Rec rt' 
    fmaprec f r = runIdentity $ R.focus (Label @l) (pure . goA) r 
     where 
        goA :: Of rp a -> Of rp b 
        goA  of' = withOf of' goB 
          where 
            goB :: forall (l' :: Symbol) (p' :: Type ~> Type)  
                .  Dict (HasType l' p' rp) -> Sing l' -> p' @@ a -> Of rp b 
            goB d@Dict sl pa = withKnownSymbol sl 
                            $ goC d (forall @rp @Functorially @l' @p')  -- for some reason the continuation seems to be mandatory here 
                                                                        -- despite the fact that goC and goD aren't introducing 
                                                                        -- any new universally quantified type variables. which shouldn't happen...
              where 
                goC :: Dict (HasType l' p' rp) -> (HasType l' p' rp :- Functorially p') -> Of rp b
                goC dx@Dict ax = case mapDict ax dx of 
                  cx -> goD cx 
                  where 
                    goD :: Dict (Functorially p') -> Of rp b
                    goD Dict = Of Dict sl (fmaply @p' f pa)

instance ( KnownSymbol l
      , Coherent rp  
      , Forall rp Functorially  
      , HasType l (Of rp b) rt'  
      , HasType l (Of rp a) rt 
      , rt' ~ R.Modify l (Of rp b) rt 
      , rt  ~ R.Modify l (Of rp a) rt' 
      ) => FMap l rp rt rt' a b 

-- map a function over the functor at the designated label of the `Applied`  
rMap :: forall (l :: Symbol) 
               (rp :: Row (Type ~> Type)) 
               (rt :: Row Type) 
               (a :: Type) 
               (b :: Type) 
      . FMap l 
             rp 
             (R.Map (Of rp) rt) 
             (R.Map (Of rp) (R.Modify l b rt))
             a 
             b 
     => (a -> b) 
     -> Applied rp rt 
     -> Applied rp (R.Modify l b rt)
rMap f (MkApplied r) = MkApplied $ fmaprec @l @rp @(R.Map (Of rp) rt) @(R.Map (Of rp) (R.Modify l b rt)) @a @b f r 

rLookup :: forall l f a rp rt 
         . ( KnownSymbol l
           , HasType l (TyCon1 f) rp
           , HasType l a rt
         ) => Applied rp rt 
           -> f a
rLookup (MkApplied r) = case r .! (Label @l) \\ mapHas @(Of rp) @l @a @rt of 
  (Of _ sl pt :: Of rp a) -> UNSAFE.unsafeCoerce pt :: f a -- Again, this is safe AS LONG AS the Implementation was created
                                                           -- or manipulated using functions in this module.
                                                           -- (In order to satisfy the ForallX constraint, the labels have to line up, 
                                                           -- but we can't embed any meaningful proof that they do. Well, not here. Sort of can if (a :: k) and SingKind a)