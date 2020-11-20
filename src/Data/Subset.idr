||| Reexporting `Data.Subset.Interfaces` and `Data.Subset.Predicates`
||| plus some utility functions.
module Data.Subset

import public Data.Subset.Interfaces
import public Data.Subset.Predicates
import public Data.Maybe

||| Compile time refinement of values
||| If this does not work, the predicate in question
||| might contain a negation. If that's the case, try `refine'`.
public export
refine : (v : t) -> {auto 0 prf : p v} -> Subset t p
refine v = Element v prf

||| Like `Data.Subset.refine` but goes via a propsition's `Predicate`
||| instance. This is necessary for instance for
||| compiletime verification of negations, for which
||| Idris2 is to able to come up with a value otherwise.
public export
refine' :  {0 t : Type} -> {0 p : t -> Type}
        -> Predicate t p
        => (v : t)
        -> {auto prf : IsJust (refineMay {p = p} v)}
        -> Subset t p
refine' v = fromJust (refineMay {p = p} v)

public export
fromInteger :  Num t
            => (v : Integer)
            -> {auto 0 prf : p (fromInteger v)}
            -> Subset t p
fromInteger v = refine (fromInteger v)

public export
fromString :  FromString t
           => (v : String)
           -> {auto 0 prf : p (fromString v)}
           -> Subset t p
fromString v = refine (fromString v)
