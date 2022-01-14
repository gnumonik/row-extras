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
{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.Row.Extras.Records (
  MapForallX(..),
  mapForallX,
  transformX, 
  transformX', 
  mapX, 
  zipTransformX,
  sequenceX, 
  distributeX,
  uncomposeX,
  traverseMapX,
  foldX,
  mapFX
) where

import Data.Row
    ( KnownSymbol,
      AllUniqueLabels,
      Row,
      HasType,
      Label,
      type (.-),
      Rec,
      (.!),
      empty,
      type (.!) )
import Data.Kind ( Type, Constraint )
import Data.Row.Internal
    ( FrontExtends(..),
      Extend,
      Map,
      Ap,
      FrontExtendsDict(FrontExtendsDict) )
import Data.Row.Dictionaries
    ( type (:-)(..),
      Dict(..),
      (\\),
      apExtendSwap,
      apHas,
      mapExtendSwap,
      mapHas,
      uniqueMap )
import Data.Singletons ( Proxy(..), Sing, SingI(sing) )
import Data.Functor.Identity ( Identity(Identity) )
import Data.Bifunctor ( Bifunctor(bimap, first, second) )
import Data.Row.Records ( extend, lazyRemove )
import Data.Type.Equality ( type (:~:)(..) )
import Data.Functor.Compose ( Compose(..) )
import Data.Functor.Const ( Const(..) )
import GHC.TypeLits.Singletons ( Symbol, withKnownSymbol )

import Data.Row.Extras.ForallX ( ForallX(..) )
import Data.Row.Extras.Util ( CConst, Top )
import Data.Row.Extras.BiForallX ( BiForallX(..) ) 


type FreeForallX r = ForallX r (CConst Top)

lazyUncons :: KnownSymbol l => Label l -> Rec r -> (Rec (r .- l), r .! l)
lazyUncons l r = (lazyRemove l r, r .! l)

-- | Like 'IsA' from Data.Row.Dictionary, but takes a constraint of type (Symbol -> k -> Constraint) instead of (k -> Constraint)
-- 
--   This allows us to extentially bind the type variable of the field of the record, and is 
--   used to implement MapForall
data HasT :: forall k. (Symbol -> k -> Constraint) -> (k -> Type) -> Type -> Symbol -> Type where 
  HasT :: forall k (l :: Symbol) (c :: Symbol -> k -> Constraint) (f :: k -> Type) (a :: k) (t :: Type)  
       . Sing (l :: Symbol) -> Dict (c l a) -> t :~: f a ->  HasT c f t l 

type HasA :: forall k.  (Symbol -> k -> Constraint) -> (k -> Type) -> Symbol -> Type -> Constraint 
class (KnownSymbol l) => HasA c f l t  where 
  hasA ::  HasT c f t l 

instance (KnownSymbol l, c l a) => HasA c f l (f a) where 
  hasA = HasT sing Dict Refl 

newtype RMapK  (f :: k -> Type) (ρ :: Row k) = RMapK { unRMapK :: Rec (Map f ρ) }

newtype RMap2 f g ρ = RMap2 { unRMap2 :: Rec (Map f (Map g ρ)) }

data RecMapPair f g ρ = RecMapPair (Rec (Map f ρ)) (Rec (Map g ρ))

type MapForallX :: forall k. (Symbol -> k -> Constraint) -> (k -> Type) -> Row k -> Type 
newtype MapForallX c f r  = MapForallX {unMapForallX :: Dict (ForallX (Map f r) (HasA c f)) }


mapForallX :: forall f ρ c . ForallX ρ c :- ForallX (Map f ρ) (HasA c f)
mapForallX = Sub $ unMapForallX $ metamorphX @_ @ρ @c @Const @Proxy @(MapForallX c f) @Proxy Proxy empty uncons cons  Proxy
  where empty _ = MapForallX Dict
        uncons _ _ = Const Proxy
        cons :: forall l t p. (KnownSymbol l, c l t, FrontExtends l t p, AllUniqueLabels (Extend l t p))
             => Label l -> Const (MapForallX c f p) (Proxy t)
             -> MapForallX c f (Extend l t p)
        cons _ (Const (MapForallX d1@Dict)) = case frontExtendsDict @l @t @p of
          FrontExtendsDict d2@Dict -> MapForallX (Dict :: Dict (ForallX (Extend l (f t) (Map f p)) (HasA c f)))
            \\ mapExtendSwap @f @l @t @p 
            \\ uniqueMap @f @(Extend l t p)


transformX :: forall k c r (f :: k -> Type) (g :: k -> Type)
                     . ForallX r c
                    => (forall l a. (KnownSymbol l) => Dict (c l a) -> f a -> g a) 
                    -> Rec (Map f r) 
                    -> Rec (Map g r)
transformX f = unRMapK . metamorphX @_ @r @c @(,) @(RMapK f) @(RMapK g) @f Proxy doNil doUncons doCons . RMapK
  where
    doNil _ = RMapK empty

    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c ℓ τ, HasType ℓ τ ρ)
             => Label ℓ -> RMapK f ρ -> (RMapK f (ρ .- ℓ), f τ)
    doUncons l (RMapK r) = first RMapK $ lazyUncons l r
      \\ mapHas @f @ℓ @τ @ρ

    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c ℓ τ)
           => Label ℓ -> (RMapK g ρ, f τ) -> RMapK g (Extend ℓ τ ρ)
    doCons l (RMapK r, v) = RMapK (extend l (f (Dict :: Dict (c ℓ τ)) v) r)
      \\ mapExtendSwap @g @ℓ @τ @ρ

transformX' :: forall k r (f :: k -> Type) (g :: k -> Type)
                     . FreeForallX r
                    => (forall (a :: k). f a -> g a) 
                    -> Rec (Map f r) 
                    -> Rec (Map g r)
transformX' f = transformX @_ @(CConst Top) @r @f @g go 
  where 
    go :: forall l (a :: k). KnownSymbol l => Dict (CConst Top l a) -> f a -> g a
    go _ fa = f fa 

mapX :: forall r f c. ForallX r c => (forall l a. (Dict (c l a) -> Sing l -> a -> f a)) -> Rec r -> Rec (Map f r)
mapX f = unRMapK . metamorphX @_ @r @c @(,) @Rec @(RMapK f) @f Proxy doNil doUncons doCons
  where
    doNil _ = RMapK empty
    doUncons :: forall l t p. (KnownSymbol l, c l t, HasType l t p)
             => Label l -> Rec p -> (Rec (p .- l), f t)
    doUncons l = second (go Dict (sing @l)) . lazyUncons l
      where 
        go :: forall l' t' x. Dict (c l' t') -> Sing l' -> t' ->  f t' 
        go d@Dict sng x = withKnownSymbol sng $ f d (sing @l') x 
    doCons :: forall l t p. (KnownSymbol l, c l t)
           => Label l -> (RMapK f p, f t) -> RMapK f (Extend l t p)
    doCons l (RMapK r, v) = RMapK (extend l v r)
      \\ mapExtendSwap @f @l @t @p

zipTransformX :: forall c r f g h 
               . ForallX r c 
              => (forall l a. (KnownSymbol l, c l a) => f a -> g a -> h a) 
              -> Rec (Map f r) 
              -> Rec (Map g r) 
              -> Rec (Map h r)
zipTransformX f x y = unRMapK $ metamorphX @_ @r @c @(,) @(RecMapPair f g) @(RMapK h) @h Proxy doNil doUncons doCons $ RecMapPair x y
  where
    doNil _ = RMapK empty
    doUncons :: forall l t p. (KnownSymbol l, c l t, HasType l t p)
             => Label l -> RecMapPair f g p -> (RecMapPair f g (p .- l), h t)
    doUncons l (RecMapPair x y) = (RecMapPair (lazyRemove l x) (lazyRemove l y), f @l (x .! l) (y .! l))
      \\ mapHas @f @l @t @p
      \\ mapHas @g @l @t @p
    doCons :: forall l t p. (KnownSymbol l, c l t)
           => Label l -> (RMapK h p, h t) -> RMapK h (Extend l t p)
    doCons l (RMapK r, h) = RMapK (extend l h r)
      \\ mapExtendSwap @h @l @t @p

sequenceX :: forall f r c. (ForallX r c, Applicative f)
          => Rec (Map f r) -> f (Rec r)
sequenceX = getCompose . metamorphX @_ @r @c @(,) @(RMapK f) @(Compose f Rec) @f Proxy doNil doUncons doCons . RMapK
  where
    doNil _ = Compose (pure empty)
    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c ℓ τ, HasType ℓ τ ρ)
             => Label ℓ -> RMapK f ρ -> (RMapK f (ρ .- ℓ), f τ)
    doUncons l (RMapK r) = first RMapK $ lazyUncons l r
      \\ mapHas @f @ℓ @τ @ρ
    doCons l (Compose fr, fv) = Compose $ extend l <$> fv <*> fr

distributeX :: forall f r. (ForallX r (CConst Top), Functor f) => f (Rec r) -> Rec (Map f r)
distributeX  = unRMapK . metamorphX @_ @r @(CConst Top) @(,) @(Compose f Rec) @(RMapK f) @f Proxy doNil doUncons doCons . Compose
  where
    doNil _ = RMapK empty
    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, HasType ℓ τ ρ)
             => Label ℓ -> Compose f Rec ρ -> (Compose f Rec (ρ .- ℓ), f τ)
    doUncons l (Compose fr) = (Compose $ lazyRemove l <$> fr, (.! l) <$> fr)
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ)
           => Label ℓ -> (RMapK f ρ, f τ) -> RMapK f (Extend ℓ τ ρ)
    doCons l (RMapK r, fv) = RMapK (extend l fv r)
      \\ mapExtendSwap @f @ℓ @τ @ρ

uncomposeX :: forall c f g r . ForallX r c
           => Rec (Map (Compose f g) r) -> Rec (Map f (Map g r))
uncomposeX = unRMap2 . metamorphX @_ @r @c @(,) @(RMapK (Compose f g)) @(RMap2 f g) @(Compose f g) Proxy doNil doUncons doCons . RMapK
  where
    doNil _ = RMap2 empty
    doUncons :: forall ℓ τ ρ. (KnownSymbol ℓ, c ℓ τ, HasType ℓ τ ρ)
             => Label ℓ -> RMapK (Compose f g) ρ -> (RMapK (Compose f g) (ρ .- ℓ), Compose f g τ)
    doUncons l (RMapK r) = first RMapK $ lazyUncons l r
      \\ mapHas @(Compose f g) @ℓ @τ @ρ
    doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c ℓ τ)
           => Label ℓ -> (RMap2 f g ρ, Compose f g τ) -> RMap2 f g (Extend ℓ τ ρ)
    doCons l (RMap2 r, Compose v) = RMap2 $ extend l v r
      \\ mapExtendSwap @f @ℓ @(g τ) @(Map g ρ)
      \\ mapExtendSwap @g @ℓ @τ @ρ

traverseMapX :: forall c f g h (r :: Row Type)
              .( ForallX r c
              ,  Applicative f
              ) => (forall l a. (KnownSymbol l) => Dict (c l a) -> g a -> f (h a)) 
                -> Rec (Map g r) 
                -> f (Rec (Map h r))
traverseMapX f =
  sequenceX @f @(Map h r) @(HasA c h) .
  uncomposeX @c @f @h @r .
  transformX @_ @c @r @g @(Compose f h) (\d -> Compose . f d)
   \\ mapForallX @h @r @c

-- | A fold with labels
foldX :: forall c ρ b
                 . ForallX ρ c
                => (forall l a. (KnownSymbol l, c l a) => a -> b -> b)
                -> b  
                -> Rec ρ 
                -> b 
foldX f b = getConst . metamorphX @_ @ρ @c @(,) @Rec @(Const b) @Identity Proxy doNil doUncons doCons
  where doNil _ = Const b
        doUncons l = second Identity . lazyUncons l
        doCons :: forall ℓ τ ρ. (KnownSymbol ℓ, c ℓ τ)
               => Label ℓ -> (Const b ρ, Identity τ) -> Const b (Extend ℓ τ ρ)
        doCons l (Const c, Identity x) = Const $ f @ℓ x c 

newtype RFMap (g :: k1 -> k2) (ϕ :: Row (k2 -> *)) (ρ :: Row k1) = RFMap { unRFMap :: Rec (Ap ϕ (Map g ρ)) }
newtype RecAp (ϕ :: Row (k -> *)) (ρ :: Row k) = RecAp (Rec (Ap ϕ ρ))
newtype App (f :: k -> *) (a :: k) = App (f a)



-- | A function to map over a Ap record given constraints.
mapFX :: forall k c g (ϕ :: Row (k -> *)) (ρ :: Row k). BiForallX ϕ ρ c
     => (forall l h a. (KnownSymbol l, c l h a) => h a -> h (g a))
     -> Rec (Ap ϕ ρ)
     -> Rec (Ap ϕ (Map g ρ))
mapFX f = unRFMap . biMetamorphX @_ @_ @ϕ @ρ @c @(,) @RecAp @(RFMap g) @App Proxy doNil doUncons doCons . RecAp
  where
    doNil _ = RFMap empty
    doUncons :: forall ℓ f τ ϕ ρ. (KnownSymbol ℓ, c ℓ f τ, HasType ℓ f ϕ, HasType ℓ τ ρ)
             => Label ℓ -> RecAp ϕ ρ -> (RecAp (ϕ .- ℓ) (ρ .- ℓ), App f τ)
    doUncons l (RecAp r) = bimap RecAp App $ lazyUncons l r
      \\ apHas @ℓ @f @ϕ @τ @ρ
    doCons :: forall ℓ f τ ϕ ρ. (KnownSymbol ℓ, c ℓ f τ)
           => Label ℓ -> (RFMap g ϕ ρ, App f τ) -> RFMap g (Extend ℓ f ϕ) (Extend ℓ τ ρ)
    doCons l (RFMap r, App v) = RFMap (extend l (f @ℓ @f @τ v) r)
      \\ mapExtendSwap @g @ℓ @τ @ρ
      \\ apExtendSwap @ℓ @f @ϕ @(g τ) @(Map g ρ)
