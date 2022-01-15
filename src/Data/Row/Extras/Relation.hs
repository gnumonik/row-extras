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

-- probably this will end up being merged into Dictionaries 

module Data.Row.Extras.Relation (biForallX) where

import Data.Row 
import Data.Singletons 
import Data.Constraint 
import GHC.TypeLits.Singletons
import Data.Kind
import Data.Row.Internal
import Data.Row.Extras.BiForallX 
import Data.Row.Extras.Util
import Data.Row.Records
import qualified Data.Row.Records as R 
import Data.Singletons.Sigma
import Data.Row.Extras.ForallX
import Data.Row.Extras.Records
import Data.Row.Dictionaries
import qualified Unsafe.Coerce as UNSAFE
import Data.Type.Equality

class HasType l a r => HasType' r l a where 
  hasType' :: Dict (HasType l a r)
  hasType' = Dict 
instance HasType l a r => HasType' r l a  

biForallX :: forall (l :: Symbol) k1 k2 
                     (c :: Symbol -> k1 -> k2 -> Constraint) 
                     (a :: k1) 
                     (b :: k2)  
                     (r1 :: Row k1) 
                     (r2 :: Row k2)
               . ( BiForallX r1 r2 c 
                 , ForallX r1 (HasType' r1) 
                 , ForallX r2 (HasType' r2)
                 , Coherent r1
                 , Coherent r2
                 , KnownSymbol l
                 , HasType l a r1 
                 , HasType l b r2
                 ) =>  Dict (c l a b)
biForallX  =  case reifyRelation @_ @_ @c @r1 @r2 :: Relation c r1 r2 r1 r2 of 
      MkRelation _ _ keys -> goB  keys 
 where 
    goB :: Rec (Map (Related' c r1 r2) r2) -> Dict (c l a b)
    goB  r = case (r .! (Label @l) \\ mapHas @(Related' c r1 r2) @l @b @r2) :: Related' c r1 r2 b of -- the type annotation is, bizarrely, necessary here 
      Related' sig -> projSigma2 goC sig 
     where 
       goC :: forall (fst :: Symbol). Related c r1 r2 b fst -> Dict (c l a b)
       goC (Related l d) = case UNSAFE.unsafeCoerce Refl :: fst :~: l of 
         Refl -> d 

-- holds evidence that a is in r at l (along with a singleton of l)
data In :: Row k -> k -> Type where 
  In :: forall k (r :: Row k) (l :: Symbol) (a :: k) 
      . Sing l -> Dict (HasType l a r) -> In r a 

-- Conjure existentially hidden evidence that each element in a row is a member of that row 
-- This seems absolutely trivial at first, but it's actually the key to making this whole thing work. 
-- Although we can't possiblye prove it to GHC, *we* know that the singleton existentially hidden inside `In r a` 
-- matches the label, and can therefore use unsafeCoerce to generate equality proofs. 
-- 
assertMembership :: forall k (r :: Row k). (ForallX r (HasType' r), Coherent r) => Rec (Map (In r) r)   
assertMembership = transformX @_ @(HasType' r) @r @Proxy @(In r) go (represent (Proxy @r))
  where 
    go :: forall l a. KnownSymbol l => Dict (HasType' r l a) -> Proxy a -> In r a
    go Dict _ = In sing (hasType' @r @l @a) 

-- Zipped and Related are both specialized GADTs used to implement `reifyRelation`. 
-- The idea is: We use `mkZipped` to conjure a `Zipped r1 r2 r1 r2` into existence. During the 
-- bimetamorphosis (is that a word?), the second set of variables changes during the cons-ing and uncons-ing, and
-- by the law of BiForallX, we end up with a `Relation c r1 r2 r1 r2`, which is allows us to instantiate the 
-- quantifier(really i guess it's two quantifiers? pretty tired atm from writing all this, not sure)
data Zipped ::  Row k1 -> Row k2 -> Row k1 -> Row k2 -> Type where 
  MkZipped :: forall k1 k2 (r1 :: Row k1) (r2 :: Row k2) r1' r2'  
            . Rec (Map (In r1) r1') -> Rec (Map (In r2) r2') -> Zipped r1 r2 r1' r2'   

mkZipped :: forall r1 r2. (ForallX r1 (HasType' r1), ForallX r2 (HasType' r2), Coherent r1, Coherent r2) 
           => Zipped r1 r2 r1 r2
mkZipped = MkZipped (assertMembership @_ @r1)  (assertMembership @_ @r2) 

data Related :: (Symbol -> k1 -> k2 -> Constraint) -> Row k1 -> Row k2 ->  k2 -> Symbol -> Type where 
  Related :: forall k1 k2 l (c :: Symbol -> k1 -> k2 -> Constraint) (r1 :: Row k1) (r2 :: Row k2) (a :: k1) (b :: k2)
           . ( HasType l a r1 
             , HasType l b r2 
            ) => Sing l 
              -> Dict (c l a b) 
              -> Related c r1 r2 b l 

newtype Related' c r1 r2 k2 = Related' (Sigma Symbol (TyCon1 (Related c r1 r2 k2)))

data Relation :: (Symbol -> k1 -> k2 -> Constraint) -> Row k1 -> Row k2 -> Row k1 -> Row k2 -> Type where 
  MkRelation :: forall k1 k2 
                      (c :: Symbol -> k1 -> k2 -> Constraint) 
                      (r1 :: Row k1) 
                      (r2 :: Row k2)
                      (r3 :: Row k1) 
                      (r4 :: Row k2) 
             .  Proxy c  -- we appear to need the proxies. not at all sure why.
             -> Proxy r3 
             -> Rec (Map (Related' c r1 r2) r4) 
             -> Relation c r1 r2 r3 r4 

-- we need an `h` for the bimetamorphX in reifyRefltion that holds all this evidence and this is it
-- (the `h` type variable argument is a container that holds the result of `uncons`.) 
-- the first 3 parameters (the constraint argument to BiForallX and the two rows) are the invariant "functor"
-- part and the last two arguments are for the uncons'd elements
data InBothC :: (Symbol -> k1 -> k2 -> Constraint) -> Row k1 -> Row k2 -> k1 -> k2 -> Type where 
  InBothC :: forall k1 k2 (c :: Symbol -> k1 -> k2 -> Constraint) (r1 :: Row k1) (r2 :: Row k2) (a :: k1) (b :: k2) (l :: Symbol) 
           . Sing l 
          -> Dict (HasType l a r1) 
          -> Dict (HasType l b r2) 
          -> Dict (c l a b) 
          -> InBothC c r1 r2 a b 

lazyUncons :: KnownSymbol l => Label l -> Rec r -> (Rec (r .- l), r .! l)
lazyUncons l r = (lazyRemove l r, r .! l)

-- it's funny how short it is if you take away the type signatures!
reifyRelation :: forall k1 k2 (c :: Symbol -> k1 -> k2 -> Constraint) 
                      (r1 :: Row k1) 
                      (r2 :: Row k2)
              . ( BiForallX r1 r2 c 
                , ForallX r1 (HasType' r1) 
                , ForallX r2 (HasType' r2)
                , Coherent r1 
                , Coherent r2
              ) =>  Relation c r1 r2 r1 r2 
reifyRelation  = biMetamorphX @k1 @k2 @r1 @r2 @c @(,) @(Zipped r1 r2) @(Relation c r1 r2) h empty uncons cons mkZipped
  where 
    h :: Proxy (Proxy (InBothC c r1 r2), Proxy (,)) 
    h = Proxy 
    
    empty = const $ MkRelation Proxy Proxy R.empty 


    cons :: forall -- it wouldn't be typelevel programming without a whole buncha types now, would it?  
       {l :: Symbol} 
       {a :: k1} 
       {b :: k2} 
       {p1 :: Row k1}
       {p2 :: Row k2}.
        ( KnownSymbol l
        , c l a b
        , FrontExtends l a p1
        , FrontExtends l b p2
        , AllUniqueLabels (Extend l a p1)
        , AllUniqueLabels (Extend l b p2)
        ) => Label l
          -> (Relation c r1 r2 p1 p2, InBothC c r1 r2 a b)
          -> Relation c r1 r2 (Extend l a p1) (Extend l b p2)
    cons _ (MkRelation Proxy Proxy relations,InBothC l d1 d2 d3) = go l d1 d2 d3 
      where 
        go :: forall l'
            . Sing l' 
           -> Dict (HasType l' a r1)
           -> Dict (HasType l' b r2) 
           -> Dict (c l' a b) 
           -> Relation c r1 r2 (Extend l a p1) (Extend l b p2)
        go l Dict Dict d3@Dict = case UNSAFE.unsafeCoerce Refl :: l' :~: l of -- If uncons is safe then this is too 
          rfl@Refl -> let  rel :: Related' c r1 r2 b                          -- (uncons is safe)
                           rel = Related' $ sing @l :&: Related (sing @l) d3  
                      in  MkRelation Proxy Proxy
                        $ extend (Label @l) rel relations
                        \\ mapExtendSwap @(Related' c r1 r2) @l @b @p2

    uncons :: forall l a b p1 p2 
            . (KnownSymbol l, c l a b, HasType l a p1, HasType l b p2) 
           => Label l
           -> Zipped r1 r2 p1 p2
           -> (Zipped r1 r2 (p1 .- l) (p2 .- l),
               InBothC c r1 r2 a b)
    uncons l (MkZipped za zb) = (MkZipped za' zb', inBothC a b)
      where 
        as :: (Rec (Map (In r1) (p1 .- l)), In r1 a)
        as@(za',a) = lazyUncons l za \\ mapHas @(In r1) @l @a @p1 

        bs :: (Rec (Map (In r2) (p2 .- l)), In r2 b)
        bs@(zb',b) = lazyUncons l zb  \\ mapHas @(In r2) @l @b @p2

        inBothC :: In r1 a -> In r2 b -> InBothC c r1 r2 a b 
        inBothC (In l1 d1@Dict) (In l2 d2@Dict) = go l1 l2 d1 d2 
          where 
            -- super unsafe ordinarily, but we conjured this stuff from mkZipped,
            -- (which *obviously* always produces the `correct` singleton) and 
            -- didn't tamper with it, so we can do this here. 
            go :: forall (l1 :: Symbol) (l2 :: Symbol)
                . Sing l1 
               -> Sing l2  
               -> Dict (HasType l1 a r1) 
               -> Dict (HasType l2 b r2) 
               -> InBothC c r1 r2 a b 
            go la lb da db = case UNSAFE.unsafeCoerce Refl :: l1 :~: l2 of 
              Refl -> case UNSAFE.unsafeCoerce Refl :: l :~: l1 of 
                Refl -> InBothC la da db Dict 

         