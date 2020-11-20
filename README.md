# Subsets: Runtime checked Refinement Types

This is a small library for refinement types in the
spirit of Haskell's [refined](https://github.com/nikita-volkov/refined)
package.

For now, the focus of this library lies on the refinement of
primitive values, which are mostly useful to at runtime make sure
that values adhere to certain preconditions. A refined value is
a value wrapped in a `Data.DPair.Subset` together with
an erased proof that the wrapped value actually
fulfills the given predicate. While this often
means testing against boolean predicates, the combinators
in this library can be used with other type-level predicates
as well.

## Module Structure

Module `Data.Subset.Predicates` defines a large set of
boolean predicates and related subset aliases plus some
data types for combining predicates.

For validating values at runtime, interface `Predicate` is provided in
module `Data.Subset.Interfaces`.

`Data.Subset` reexports the other two modules
and provides some utility functions for
refining values at compile time, including
`fromString` and `fromInteger` functions for `Subset`.

## Documentation and Examples

Before we start: This is a literate Idris2 file. It can
be typechecked after installing this library using the following
command:

```
idris2 -p subsets --check README.md
```

```idris
module README

import Data.Subset
import Data.Strings

%default total
```

### General Concepts

A refined value in this library is a value together
with an erased proof that the value fulfills a given
predicate. This behavior is provided by `Data.DPair.Subset`:

```idris
MyStr : Type
MyStr = Subset String $ Is ((> 0) . length)
```

We will see why we need predicate `Is` in a moment.

At compile time, Idris2 can often generate the requested proofs
automatically and we provide corresponding `fromString`
and `fromInteger` functions:

```idris
ex1 : MyStr
ex1 = "foo"
```

For values that can not automatically be created from
literals, function `refine` is provided:

```idris
Abundance : Type
Abundance = Subset Double $ Is \x => x >= 0 && x <= 1

pointFive : Abundance
pointFive = refine 0.5
```

In order to refine values at runtime, predicate types
have to implement interface `Predicate`. They can then
be refined using function `refineMay`:

```idris
parseAbundance : String -> Maybe Abundance
parseAbundance s = parseDouble s >>= refineMay
```

That's the reason why we specified `Abundance` and `MyStr` via `Is`:
It has an implementation of `Predicate`. Without that requirement,
we could also have done the following:

```idris
Abundance' : Type
Abundance' = Subset Double $ \x => (x >= 0 && x <= 1) = True

pointNine : Abundance'
pointNine = refine 0.9
```

There are several combinators for defining predicates.
Logical conjuction is provided by the `And` combinator:

```idris
IsAlias : String -> Type
IsAlias = And [AllChars isAlphaNum, IsNonEmptyString, MaxStringLength 50]

Alias : Type
Alias = Subset String IsAlias

hock : Alias
hock = "hock"
```

Logical disjunction is provided by the `Or` combinator:

```idris
OptionalAlias : Type
OptionalAlias = Subset String $ Or [IsEmptyString, IsAlias]

emptyAlias : OptionalAlias
emptyAlias = ""
```

Predicates can be applied by going through additional functions,
using data type `Via`:

```idris
IsSmallPrime : Int -> Type
IsSmallPrime = Is (`elem` [2,3,5,7,11,13,17,19])

IsSmallPrimeString : String -> Type
IsSmallPrimeString = Via cast IsSmallPrime

nineteen : Subset String IsSmallPrimeString
nineteen = "19"
```

Finally, predicates can be negated using `Neg`:

```idris
IsNotASmallPrime : String -> Type
IsNotASmallPrime = Neg IsSmallPrimeString
```

Note however, that for negations of predicates, Idris2 can
typically not come up with a proof automatically. The following
does not compile:

```
twenty : Subset String IsNotASmallPrime
twenty = "20"
```

In such a case, we can try to go via the predicate's
`Predicate` implementation using function `refine'`:

```idris
twenty : Subset String IsNotASmallPrime
twenty = refine' "20"
```

Unlike creating a proof for the predicate directly, `refine'`
runs `refineMay` and checks whether it returns a value
using predicate `IsJust` from `Data.Maybe`.

### Refined Numbers

To be added.

### Refined Characters

To be added.

### Refined Strings

To be added.

### Why Combinators

Many of the examples so far could have been provided
simply by writing dedicated boolean predicates and
using `Is` alone. However, there are several reasons
to provide additional combinators. First, we sometimes
may like to combine structural predicates with
primitive ones. Second, as is described below, I'm looking
into ways for weakening predicates, something that
will be very hard to do without adding additional
structure to predicates.

### Caveat: Division Predicates

In order to at compile time create an even number (or another
number with a predicate based `Data.Subset.Predicates.divides`),
we have to go via `refine`:

```idris
eight : Even Int
eight = refine 8
```

The following, more direct way via `fromInteger`
fails with an error about
a call to non-covering function `prim__mod_Int`:

```
eight : Even Int
eight = 8
```

I'm not sure what's going on here. Probably, the call
to `fromInteger` is inlined while the call to `refine`
is not. Either way, Idris2 does not expect us to confirm
that `divides` is total, which seems to be a bug.

## What else to expect

At the moment I am experimenting with weakening subsets.
For instance, if we have an even positive integer `n`, and
a function expecting any positive integer, we should be
able to use `n` in this function by *weakening* the predicate.

## Comparison with Haskell's *Refined* Library

Idris2, being dependently typed, allows us to conveniently
define and combine all kinds of boolean predicates directly,
without the need for additional data types. On the
other hand, *Refined* provides nicely formatted error messages
about what exactly went wrong when refining a value failed,
something that is not supported by our actual design.

As an additional benefit, in many occasions Idris2 allows us
to automatically refine values at compile time without jumping
through any metaprogramming hoops.
