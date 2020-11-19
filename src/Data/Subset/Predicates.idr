||| A predicate p on a type t is a partial function from
||| t to Type. A refinement of t under p is the domain of p,
||| that is, the subset of values in t for which p is defined.
|||
||| Idris2 provides data type `Subset` for modelling invariants
||| about values, with the guarantee that these invariants
||| will be erased at runtime. We use this data type in this
||| library as a proof that a value has been properly validated
||| (refined) at runtime.
|||
||| The majority of predicates defined in this module are
||| boolean predicates: Proofs that a runtime check returned
||| `True` most of the time. However, some other combinators
||| exist, and these can be used with other typelevel
||| propositions as well.
|||
||| This module only provides a large set of predefined
||| predicates. For an interface to check these predicates
||| at runtime, see module `Data.Subset.Interfaces`.
|||
||| Note: With function names starting with a lowercase letter,
|||       Idris2 often fails to treat them as predicate functions
|||       and considers them as type paramters. This can lead
|||       to unexpected behavior. For instance, the following will
|||       not compile:
|||
|||       ```idris example
|||       alpha : Subset Char $ Is isAlpha
|||       alpha = refine 'z'
|||       ```
|||
|||       Whereas the following version compiles just fine:
|||
|||       ```idris example
|||       IsAlpha : Char -> Type
|||       IsAlpha = Is isAlpha
|||
|||       alpha : Subset Char IsAlpha
|||       alpha = refine 'z'
|||       ```
module Data.Subset.Predicates

import public Data.DPair

%default total

--------------------------------------------------------------------------------
--          Predicate Combinators
--------------------------------------------------------------------------------

||| Proof that the given boolean predicate `pred` holds for `v`
||| (that is, `pred v` returns `True`).
|||
||| Probably the workhorse of this module. Allows us to
||| conveniently specify short boolean predicates through
||| anonymous functions.
|||
||| ```idris example
||| IsShortString : String -> Type
||| IsShortString = Is \s => length s <= 20
||| ```
public export
data Is : (pred : t -> Bool) -> (v : t) -> Type where
  ItIs : (prf : pred v = True) -> Is {t = t} pred v

||| Proof that the given predicate `p` holds for the image
||| of value `v` under function `f`.
|||
||| This is especially useful if `p` is actually a list of predicates.
|||
||| ```idris example
||| IsShortNonEmptyString : String -> Type
||| IsShortNonEmptyString = Via {a = String} length $ All [GT 0, LEQ 20]
||| ```
public export
data Via : (0 f : a -> b) -> (0 p : b -> Type) -> (v : a) -> Type where
  Go : (v : a) -> (prf : p (f v)) -> Via f p v

||| Proof that all predicates in list `ps`
||| hold for the given value `v`
public export
data All : (0 ps : List (t -> Type)) -> (v : t) -> Type where
  Nil  : All [] v
  (::) : (prf : p v) -> All ps v -> All {t = t} (p :: ps) v 

||| Proof that at least one predicate in a list `ps`
||| of predicates holds for the given value `v`.
public export
data Any : (0 ps : List (t -> Type)) -> (v : t) -> Type where
  Z : (prf : p v) -> Any {t = t} (p :: ps) v
  S : Any ps v    -> Any {t = t} (p :: ps) v

||| Proof that the given predicate `p` does not hold for `v`.
public export
data Neg : (0 p : t -> Type) -> (v : t) -> Type where
  IsNeg : (contra : p v -> Void) -> Neg {t = t} p v

--------------------------------------------------------------------------------
--          EqOrd Predicates
--------------------------------------------------------------------------------

||| Alias for `Is (a ==)`
public export
EQ : Eq a => a -> a -> Type
EQ a = Is (a ==)

||| Alias for `Is (a /=)`
public export
NEQ : Eq a => a -> a -> Type
NEQ a = Is (a /=)

||| Alias for `Is (> a)`
public export
GT : Ord a => a -> a -> Type
GT a = Is (> a)

||| Alias for `Is (< a)`
public export
LT : Ord a => a -> a -> Type
LT a = Is (< a)

||| Alias for `Is (>= a)`
public export
GEQ : Ord a => a -> a -> Type
GEQ a = Is (>= a)

||| Alias for `Is (<= a)`
public export
LEQ : Ord a => a -> a -> Type
LEQ a = Is (<= a)

||| Inclusive interval of numbers
public export
FromTo : Ord a => a -> a -> a -> Type
FromTo mi ma = All [GEQ mi, LEQ ma]

--------------------------------------------------------------------------------
--          Numeric Predicates
--------------------------------------------------------------------------------

||| Alias for `GT 0`
public export
IsPositive : Ord a => Num a => a -> Type
IsPositive = GT 0

||| Alias for `LT 0`
public export
IsNegative : Ord a => Num a => a -> Type
IsNegative = LT 0

||| Alias for `GEQ 0`
public export
IsNonNegative : Ord a => Num a => a -> Type
IsNonNegative = GEQ 0

||| Alias for `LEQ 0`
public export
IsNonPositive : Ord a => Num a => a -> Type
IsNonPositive = LEQ 0

||| Values in the interval [0,1]
public export
IsUnit : Ord a => Num a => a -> Type
IsUnit = FromTo 0 1

infixl 9 `divides`

public export
divides : Eq a => Integral a => a -> a -> Bool
divides x y = x /= 0 && y `mod` x == 0

||| Alias for `Is (a `divides`)`
public export
IsDivisibleBy : Eq a => Integral a => a -> a -> Type
IsDivisibleBy a = Is (a `divides`)

||| Alias for `IsDivisibleBy 2`
public export
IsEven : Eq a => Integral a => a -> Type
IsEven = IsDivisibleBy 2

||| Alias for `Is (not $ a `divides`)`
public export
IsNotDivisibleBy : Eq a => Integral a => a -> a -> Type
IsNotDivisibleBy a = Is (\b => not $ a `divides` b)

||| Alias for `IsNotDivisibleBy 2`
public export
IsOdd : Eq a => Integral a => a -> Type
IsOdd = IsNotDivisibleBy 2

--------------------------------------------------------------------------------
--          Numeric Subsets
--------------------------------------------------------------------------------

||| Subset of positive numbers.
|||
||| ```idris example
||| anInt : Positive Int
||| anInt = 12
||| ```
public export
Positive : (t : Type) -> Ord t => Num t => Type
Positive t = Subset t IsPositive

||| Subset of non-negative numbers.
|||
||| ```idris example
||| zero : NonNegative Int
||| zero = 0
||| ```
public export
NonNegative : (t : Type) -> Ord t => Num t => Type
NonNegative t = Subset t IsNonNegative

||| Subset of negative numbers.
|||
||| ```idris example
||| minusOne : Negative Int
||| minusOne = -1
||| ```
public export
Negative : (t : Type) -> Ord t => Num t => Type
Negative t = Subset t IsNegative

||| Subset of non-positive numbers.
|||
||| ```idris example
||| zero : NonPositive Int
||| zero = 0
||| ```
public export
NonPositive : (t : Type) -> Ord t => Num t => Type
NonPositive t = Subset t IsNonPositive

||| Subset of numbers in the inclusive range [0,1].
|||
||| ```idris example
||| pointFive : Unit Double
||| pointFive = 0.5
||| ```
public export
Unit : (t : Type) -> Ord t => Num t => Type
Unit t = Subset t IsUnit

||| Subset of even integers.
|||
||| ```idris example
||| fourteen : Even Int
||| fourteen = 14
||| ```
public export
Even : (t : Type) -> Eq t => Integral t => Type
Even t = Subset t IsEven

||| Subset of odd integers.
|||
||| ```idris example
||| seven : Odd Int
||| seven = 7
||| ```
public export
Odd : (t : Type) -> Eq t => Integral t => Type
Odd t = Subset t IsOdd

--------------------------------------------------------------------------------
--          Char Predicates
--------------------------------------------------------------------------------

||| Alias fo `Is isUpper`.
public export
IsUpper : Char -> Type
IsUpper = Is isUpper

||| Alias fo `Is isLower`.
public export
IsLower : Char -> Type
IsLower = Is isLower

||| Alias fo `Is isAlpha`.
public export
IsAlpha : Char -> Type
IsAlpha = Is isAlpha

||| Alias fo `Is isDigit`.
public export
IsDigit : Char -> Type
IsDigit = Is isDigit

||| Alias fo `Is isAlphaNum`.
public export
IsAlphaNum : Char -> Type
IsAlphaNum = Is isAlphaNum

||| Alias fo `Is isSpace`.
public export
IsSpace : Char -> Type
IsSpace = Is isSpace

||| Alias fo `Is isNL`.
public export
IsNL : Char -> Type
IsNL = Is isNL

||| Alias fo `Is isHexDigit`.
public export
IsHexDigit : Char -> Type
IsHexDigit = Is isHexDigit

||| Alias fo `Is isHexDigit`.
public export
IsOctDigit : Char -> Type
IsOctDigit = Is isOctDigit

||| Alias fo `Is isControl`.
public export
IsControl : Char -> Type
IsControl = Is isControl

--------------------------------------------------------------------------------
--          Character Subsets
--------------------------------------------------------------------------------

||| Subset of upper case characters (range 'A'-'Z').
public export
Upper : Type
Upper = Subset Char IsUpper

||| Subset of lower case characters (range 'a'-'z').
public export
Lower : Type
Lower = Subset Char IsLower

||| Subset of characters in the ranges 'a'-'z' and 'A'-'Z'.
public export
Alpha : Type
Alpha = Subset Char IsAlpha

||| Subset of characters in the range '0'-'9'
public export
Digit : Type
Digit = Subset Char IsDigit

||| Subset of alphanumeric characters.
public export
AlphaNum : Type
AlphaNum = Subset Char IsAlphaNum

||| Subset of space characters.
public export
Space : Type
Space = Subset Char IsSpace

||| Subset of newline characters.
public export
NL : Type
NL = Subset Char IsNL

||| Subset of hexadecimal digits.
public export
HexDigit : Type
HexDigit = Subset Char IsHexDigit

||| Digits in the range '0'-'7'.
public export
OctDigit : Type
OctDigit = Subset Char IsOctDigit

||| Subset of control characters.
public export
Control : Type
Control = Subset Char IsControl

--------------------------------------------------------------------------------
--          String Predicates
--------------------------------------------------------------------------------

||| Proof that a String is actually the empty string.
||| This is often useful in combination with `Any`.
|||
||| As an example, consider a predicate `IsEmail` for valid
||| email addresses, and an optional "eMail" field in a GUI
||| that accepts either a valid email or an empty string.
|||
||| It's refinement type might be defined as follows:
|||
||| ```idris example
||| OptionalEmail : Type
||| OptionalEmail = Subset String $ Any [IsEmptyString, IsEmail]
||| ```
public export
IsEmptyString : String -> Type
IsEmptyString = Is \s => length s == 0

||| Proof that a String is non-empty.
public export
IsNonEmptyString : String -> Type
IsNonEmptyString = Is \s => length s > 0

||| Proof that a String's length does not
||| exceed the given value.
public export
MaxStringLength : Nat -> String -> Type
MaxStringLength n = Is \s => length s <= n

||| Proof that a String's length is at least
||| the given value.
public export
MinStringLength : Nat -> String -> Type
MinStringLength n = Is \s => length s >= n

||| Proof that the given boolean predicate holds for all
||| characters in a String
public export
AllChars : (pred : Char -> Bool) -> String -> Type
AllChars pred = Is $ all pred . unpack

||| Proof that the given boolean predicate holds for at least
||| one character in a String
public export
AnyChar : (pred : Char -> Bool) -> String -> Type
AnyChar pred = Is $ any pred . unpack

||| Proof that a string has no line breaks
public export
NoLinebreak : String -> Type
NoLinebreak = AllChars (not . isNL)

||| Proof that a string has no control characters
public export
NoControlChars : String -> Type
NoControlChars = AllChars (not . isControl)

--------------------------------------------------------------------------------
--          String Subsets
--------------------------------------------------------------------------------

||| Subset of non-empty Strings.
public export
NonEmptyString : Type
NonEmptyString = Subset String IsNonEmptyString

||| Subset of Strings consisting only of alphanumeric characters
||| in the ranges 'a'-'z', 'A'-'Z', '0'-'9'.
public export
AlphaNumString : Type
AlphaNumString = Subset String $ AllChars isAlphaNum

||| Subset of Strings without line breaks
public export
Line : Type
Line = Subset String NoLinebreak

||| Subset of Strings without control characters
public export
PlainString : Type
PlainString = Subset String NoControlChars

--------------------------------------------------------------------------------
--          Foldable Predicates
--------------------------------------------------------------------------------

||| Proof that the given predicate holds for all values
||| in a `Foldable` structure.
public export
Forall : Foldable f => (pred : a -> Bool) -> f a -> Type
Forall pred = Is $ all pred

||| Proof that the given predicate holds for at least one value
||| in a `Foldable` structure.
public export
Exists : Foldable f => (pred : a -> Bool) -> f a -> Type
Exists pred = Is $ any pred
