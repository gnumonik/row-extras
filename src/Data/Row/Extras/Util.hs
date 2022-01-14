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

module Data.Row.Extras.Util (
  Top(..),
  top, 
  CConst(..),
  mapcc, 
  type ConstraintX, 
  Known(..),
  Coherent(..)
) where

import Data.Row ( Row, Forall, Rec, WellBehaved )
import Data.Kind ( Type, Constraint )
import Data.Row.Internal ( Forall, Row, WellBehaved )
import Data.Row.Dictionaries ( type (:-)(..), Dict(..) )
import Data.Singletons ( Proxy(..) )
import Data.Row.Records ( Rec )
import GHC.TypeLits (Symbol)
import Data.Constraint ( mapDict, unmapDict )
import qualified Data.Row.Records as R

-- | A constraint that is satisfied by any type (of any kind) 
type Top :: forall k. k -> Constraint 
class Top a  
instance Top a 

top :: forall k (c :: k -> Constraint) (a :: k). c a => Dict (Top a) 
top = Dict 

-- | Kind of like const, but for constraints. This is meant to be partially applied (that's why it's a class), and is used 
--   to transform a partially applied constraint of kind (k -> Constraint) into a partially applied 
--   constraint of kind (Symbol -> k -> Constraint) for use with ForallX with some row of kind (Row k)
-- 
--   Technically we could use this to make @Forall@ from Data.Row a special case of @ForallX@ from this package...
--   but that would be a loooot of work without much tangible benefit.
type CConst :: (k -> Constraint) -> j -> k -> Constraint 
class (c k) => CConst c j k where 
  -- | Takes a Proxy of some partially applied constraint of kind @k -> Constraint@ 
  --   and produces an entailment from @CConst c j k@ to @c k@. 
  --
  --   You can use @mapDict@ from Data.Constraint to extract the @c k@ constraint from the @CConst c j k@ constraint 
  --
  --   For example: 
  --  
  -- > mapDict (cconst (Proxy @Ord)) (Dict :: Dict (CConst Ord "hello" Int))  
  --   
  --   gives us a 
  --   
  -- > Dict :: Dict (Ord Int)
  cconst :: Proxy c -> CConst c j k :- c k -- need the proxy, dunno why (type applications won't work)
  cconst proxy = Sub Dict 

instance c k => CConst c j k

-- | Maps an entailment over CConst. 
mapcc :: forall c c' j k. (forall a. c a :- c' a) -> (CConst c j k :- CConst c' j k)  
mapcc f = unmapDict go 
  where 
    go :: forall j1 k1. Dict (CConst c j1 k1) -> Dict (CConst c' j1 k1)
    go dA@Dict = case mapDict (cconst (Proxy @c)) dA of
      dB@Dict -> case mapDict f dB of 
        dC@Dict -> Dict   

type ConstraintX k = Symbol -> k -> Constraint  

-- | Class for things we can conjure into existence  (Like @KnownSymbol@/@KnownNat@ but for... anything)
--   Here, this is primarily used to generate a record of proxies from a proxy of a row.
type Known :: Type -> Constraint 
class Known a where 
  known :: a 

-- fun fact: these two instances actually *don't* overlap!
instance Known (Proxy (a :: k)) where 
  known = Proxy 

instance Known (Proxy (a :: Type)) where 
  known = Proxy 

-- | Class of rows of types which we can conjure a record of proxies of. 
--   Since it is necessary to produce witnesses that each element in a row 
--   satisfies some constraint, and since we'll usually construct those witnesses by 
--   transforming (Proxy a) to (SomeWitnessType a) using `transform` from Data.Row.Records or 
--   `transformX` from this library, this gives us a place to start. (Also comes in handy when we have
--   a row of things of some kind `k`, where `k` isn't `Type`)
type Coherent :: Row k -> Constraint 
class ( WellBehaved rk 
      , WellBehaved (R.Map Proxy rk) 
      , Forall (R.Map Proxy rk) Known 
      ) => Coherent (rk :: Row k)where 
            represent ::  Proxy rk -> Rec (R.Map Proxy rk)
            represent  _ = R.default' @Known known  
instance ( WellBehaved rk 
      , WellBehaved (R.Map Proxy rk) 
      , Forall (R.Map Proxy rk) Known 
      ) => Coherent (rk :: Row k)where 

