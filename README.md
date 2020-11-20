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
in this library could be used with other type-level predicates
as well.

## Modules

Module `Data.Subset.Predicates` defines a large set of
boolean predicates and related subset aliases plus some
data types for combining predicates.

For validating values at runtime, interface `Predicate` is provided in
module `Data.Subset.Interfaces`.

`Data.Subset` reexports the other two modules
and provides some utility functions for
refining values at compile time, including
`fromString` and `fromInteger` functions for `Subset`.

## Examples

Will follow shortly.

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
something that is not supported by the actual design.

As an additional benefit, in many occasions Idris2 allows us
to automatically refine values at compile time without jumping
through any metaprogramming hoops.
