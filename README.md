# row-extras

This package defines several utility functions, typeclasses, constraints, and data types for working with the `row-types` library. 

The core of this library is the `ForallX` type class (defined in Data.Row.Extras.ForallX). Whereas `row-types` defines a class `Forall`: 

``` haskell
class Forall (r :: Row k) (c :: k -> Constraint) where (...)
```

Which allows for transformations of types paramaterized by a row that 
utilitze a constraint over the *elements* of the row, this library defines a more powerful type class: 

``` haskell 
class (...) => ForallX (r :: Row k) (c :: Symbol -> k -> Constraint) where (...)
```

Which lets us transform records utilizing a "relational constraint" (of sorts) on the label *and* the element. 

The most useful module in this package is (probably) `Data.Row.Extras.Records`, which defines a `ForallX` version of *almost* all of the `Forall` functions in `Data.Row.Records`. For example, `Data.Row.Records` defines a `map` function: 

``` haskell
map :: forall c f r. Forall r c => (forall a. c a => a -> f a) -> Rec r -> Rec (Map f r)
```

The `ForallX` version of that is: 


``` haskell 
mapX :: forall r f c. ForallX r c => (forall l a. (Dict (c l a) -> Sing l -> a -> f a)) -> Rec r -> Rec (Map f r)
```

Note that the argument function to `mapX` takes a `Dict` (from `Data.Constraint`) and a `Sing (l :: Symbol)` (from the `singletons` package). Many (though not all) of the `ForallX` functions require `Dict`s and singletons in order to typecheck. 

I assume that users of this library are broadly familiar with the equivalent functions from `Data.Row.Records`; if you are, these should all be straightforward to use. 


The second most useful module here is probably `Data.Row.Extras.Dictionaries`. Of primary interest is the `forall` function: 

```haskell 
forall :: forall r c l t
        . (Coherent r -- this is practically equivalent to `WellBehaved` from Data.Row and you can ignore it 
        ,  Forall r c
        ,  KnownSymbol l
        ) => HasType l t r :- c t 
```

Which lets us derive `c a` from `HasType l t r`, `Forall r c` and `KnownSymbol l`. In other words, this gives us universal instantiation for rows (treating constraints as predicates), which opens up some interesting possibilities for type theory experiments. 

At this moment, there are only `ForallX`/`BiForallX` functions defined for *records*. There is no real reason why we couldn't have a set of functions for variants as well, but writing these functions is *extremely* mentally taxing and I don't have a use case for the variant versions :) 

Finally, this library contains a (very experimental and rudimentary!) API in `Data.Row.Extras.ApplyRow` for working with a (r :: Row Type) which is paramterized by a (rp :: Row (Type ~> Type)). This is more or less a proof of concept using the simple case where a row of types (:: Type) are paramaterized against a row of type constructors (:: Type ~> Type). If this works, we should be able to do more fun and complicated things with more exotic rows and type-functions. (Though things get a lot harder when we're working with more than two rows which aren't always of kind `Type`). 

Each module except `Data.Row.Extras.Records` is extensively documented. Please see the documentation for `Data.Row.Records` if the functions in Extras.Records confuse you. 

This is all highly experimental, so if you see a mistake or a better way to do things, please open an issue or submit a pull request! 




