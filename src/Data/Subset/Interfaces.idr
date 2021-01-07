module Data.Subset.Interfaces

import Data.Subset.Predicates
import Data.List
import public Decidable.Equality

%default total

||| In order to verify a predicate to hold for a given value
||| at runtime, it has to implement this interface.
public export
interface Predicate t (0 p : t -> Type) | p where
  ||| Validates a value against the given predicate.
  validate : (v : t) -> Dec (p v)

||| Runtime refinement of values.
public export
refineMay : Predicate t p => (v : t) -> Maybe (Subset t p)
refineMay v = case validate {p = p} v of
                   (Yes prf) => Just (Element v prf)
                   (No _)    => Nothing

public export
Predicate (List a) NonEmpty where
  validate []       = No absurd
  validate (_ :: _) = Yes IsNonEmpty


public export
Predicate k p => Predicate k (Neg p) where
  validate v with (validate { p = p } v)
    validate v | (Yes prf)   = No \(IsNeg c) => c prf
    validate v | (No contra) = Yes $ IsNeg contra


public export
{f : t -> Bool} -> Predicate t (Is f) where
  validate v = case decEq (f v) True of
                    (Yes prf)   => Yes $ ItIs prf
                    (No contra) => No \(ItIs prf) => contra prf


public export
{f : a -> b} -> Predicate b p => Predicate a (Via f p) where
  validate v = case validate {p = p} (f v) of
                    (Yes prf)   => Yes $ Go v prf
                    (No contra) => No \(Go _ prf) => contra prf




consInjective : And (p::ps) v -> (p v, And ps v)
consInjective (prf :: prfs) = (prf, prfs)

public export
Predicate t (And []) where
  validate v = Yes Nil

public export
Predicate t p => Predicate t (And ps) => Predicate t (And (p :: ps)) where
  validate v with (validate {p = p} v)
    validate v | No contra = No (contra . fst . consInjective)
    validate v | Yes phead with (validate {p = And ps} v)
      validate v | Yes phead | Yes ptail = Yes $ phead :: ptail
      validate v | Yes phead | No contra = No (contra . snd . consInjective)



public export
Uninhabited (Or [] v) where
  uninhabited _ impossible

public export
Predicate t (Or []) where
  validate v = No absurd

public export
Predicate t p => Predicate t (Or ps) => Predicate t (Or (p::ps)) where
  validate v with (validate {p = p} v)
    validate v | Yes prf = Yes $ Z prf
    validate v | No contra with (validate {p = Or ps} v)
      validate v | No contra | Yes prf = Yes $ S prf
      validate v | No contra | No contra2 =
        No $ \any => case any of
                          (Z p) => contra p
                          (S p) => contra2 p
