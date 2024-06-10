{-# OPTIONS --no-unicode #-}

module OneLive where

-- Bool
-- традиционен булев тип данни
-- can also write on the same line
-- живее в Lib.Two
data Two : Set where
  ff : Two
  tt : Two

_ : Two
_ = ff

not : Two -> Two
not ff = tt
not tt = ff

-- празен тип
-- изразява логическо противоречие/"лъжа"
-- живее в Lib.Zero
data Zero : Set where

-- id :: a -> a
-- id x = x

-- template <typename T> ... T ...

-- type signature:
-- dependent types
-- implicit params
zero-elim : {A : Set} -> Zero -> A
zero-elim ()

-- struct TwoTuple {bool fst; bool snd};
record TwoTuple : Set where
  field
    fstTwo : Two
    sndTwo : Two

-- TwoTuple.fstTwo
-- ->
-- fstTwo
-- using namespace TwoTuple;
open TwoTuple public

_ : TwoTuple
_ =
  record
    {
    fstTwo = tt ;
    sndTwo = ff
    }

swapTwoTuple : TwoTuple -> TwoTuple
swapTwoTuple
  record { fstTwo = pesho ; sndTwo = gosho } =
    record { fstTwo = gosho ; sndTwo = pesho }

record One : Set where
  constructor <>

_ : One
_ = <>

-- One
-- trivial truth
-- constructor
-- живее в Lib.One

-- ff и tt
-- 3 4 5
-- "asdf" "pesho"
--
-- Zero и One

-- Zero and One
-- vs
-- ff and tt

data DrinkType : Set where
  beer : DrinkType
  milk : DrinkType

data MilkType : Set where
  козе : MilkType
  краве : MilkType

data BeerType : Set where
  ipa : BeerType
  lager : BeerType

WhatIsSubtype : DrinkType -> Set
WhatIsSubtype beer = BeerType
WhatIsSubtype milk = MilkType

record Drink : Set where
  constructor mkDrink
  field
    drinkType : DrinkType
    subType : WhatIsSubtype drinkType

-- drinkType ~ beer
-- subType : WhatIsSubtype beer
-- subType : BeerType
overflow : Drink
overflow = mkDrink beer ipa


-- DrinkType
-- MilkType
-- BeerType
-- Drink

-- TwoEq x y
-- ==
-- доказателство за равни ли са x и y
TwoEq : Two -> Two -> Set
TwoEq ff ff = One
TwoEq ff tt = Zero
TwoEq tt ff = Zero
TwoEq tt tt = One

-- ==
-- False == True
-- false == true
--
decideEqualTwos : Two -> Two -> Two
decideEqualTwos ff ff = tt
decideEqualTwos ff tt = ff
decideEqualTwos tt ff = ff
decideEqualTwos tt tt = tt

-- IsTrue x
Is : Two -> Set
Is ff = Zero
Is tt = One

TwoEq' : Two -> Two -> Set
TwoEq' x y = Is (decideEqualTwos x y)

-- f : (x y : Bool) -> TwoEq x y -> TwoEq' x y
-- f^-1 : (x y : Bool) -> TwoEq' x y -> TwoEq x y


-- TwoEq (not (not ff)) ff
-- TwoEq (not tt) ff
-- TwoEq ff ff
-- One
--
not-not-eq :
  (x : Two) ->
  TwoEq (not (not x)) x
not-not-eq ff = <> -- ?0
not-not-eq tt = <> -- ?1

_&&_ : Two -> Two -> Two
ff && _ = ff
tt && y = y

-- (x && y) && z == x && (y && z)
-- TwoEq ((x && y) && z) (x && (y && z))
-- ((x && y) && z)
-- x && y
-- x
-- One
&&-assoc :
  (x y z : Two) ->
  TwoEq ((x && y) && z) (x && (y && z))
&&-assoc ff y z = <>
&&-assoc tt ff z = <>
&&-assoc tt tt ff = <>
&&-assoc tt tt tt = <>


-- TwoEq
-- examples
-- not-not-eq
-- explain with reductions
-- _&&_ assoc
-- explain stuckness

-- go back and change _&&_ to be lazier, show assoc again

-- Is
-- TwoEq via Is
-- TwoEq-implies-TwoEq'

-- prod
-- constructor
-- swap

-- template <typename A, typename B>
-- data Tuple a b = ....
-- |A * B| == |A| * |B|
record _*_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open _*_ public
infixr 90 _*_

_ : Two * Two
_ = ff , tt

-- |A + B| == |A| + |B|
data _+_ (A B : Set) : Set where
  inl : A -> A + B
  inr : B -> A + B

infixr 80 _+_

_ : Two + One
_ = inl tt

_ : Two + One
_ = inr <>

-- Either
-- union
+-swap : {A B : Set} -> A + B -> B + A
+-swap (inl x) = inr x
+-swap (inr y) = inl y

*-swap : {A B : Set} -> A * B -> B * A
*-swap x = snd x , fst x

-- _+_
-- sum
-- живее в Lib.Sum
-- swap

-- explain uncommenting


-- TASK
-- Prove assocativity of proposoitioanl "or"
+-assoc : {A B C : Set} -> A + (B + C) -> (A + B) + C
+-assoc (inl x) = inl (inl x)
+-assoc (inr (inl x)) = inl (inr x)
+-assoc (inr (inr x)) = inr x

-- TASK
-- Prove assocativity of proposoitioanl "and"
*-assoc : {A B C : Set} -> A * (B * C) -> (A * B) * C
*-assoc (fst1 , (fst2 , snd1)) = (fst1 , fst2) , snd1


-- TASK
-- Prove distributivity of * over +
*-distrib-+ : {A B C : Set} -> A * (B + C) -> A * B + A * C
*-distrib-+ (fst1 , inl x) = inl (fst1 , x)
*-distrib-+ (fst1 , inr x) = inr (fst1 , x)


-- TASK
-- Prove _&&_ commutative
&&-commut : (b1 b2 : Two) -> TwoEq (b1 && b2) (b2 && b1)
&&-commut ff ff = <>
&&-commut ff tt = <>
&&-commut tt ff = <>
&&-commut tt tt = <>


-- TASK
-- Implement "or" over boolean values
-- try to make the definition as "lazy" as possible, to make proofs easier!
_||_ : Two -> Two -> Two
tt || y = tt
ff || y = y


-- TASK
-- prove || commutative
||-commut : (b1 b2 : Two) -> TwoEq (b1 || b2) (b2 || b1)
||-commut ff ff = <>
||-commut ff tt = <>
||-commut tt ff = <>
||-commut tt tt = <>


-- TASK
-- State assocativity of || and prove it
||-assoc : (b1 b2 b3 : Two) -> TwoEq ((b1 || b2) || b3) (b1 || (b2 || b3))
||-assoc ff ff ff = <>
||-assoc ff ff tt = <>
||-assoc ff tt b3 = <>
||-assoc tt b2 b3 = <>

-- TASK
-- Define the NAND operation over bools
nandTwo : Two -> Two -> Two
nandTwo x y = not (x && y)

-- TASK
-- Define ff using tt and NAND
nandff : Two
nandff = nandTwo tt tt


-- TASK
-- Formulate and prove that nandff is the same thing as ff
_ : TwoEq nandff ff
_ = <>


-- TASK
-- Define negation using only nandTwo and any previously defined operations involving nand.
nandNot : Two -> Two
nandNot = nandTwo tt

-- TASK
-- Formulate and prove that nandNot behaves the same way as not
ffEqNandff : (x : Two) -> TwoEq (nandNot x) (not x)
ffEqNandff ff = <>
ffEqNandff tt = <>

-- TASK
-- Define _&&_ using only nandTwo and any previously defined operations involving nand.
nandAnd : Two -> Two -> Two
nandAnd x y = nandNot (nandTwo x y)

-- TASK
-- Formulate and prove that nandAnd beahves the same way as _&&_
nandAndEq&& : (x y : Two) -> TwoEq (nandAnd x y) (x && y)
nandAndEq&& ff y = <>
nandAndEq&& tt ff = <>
nandAndEq&& tt tt = <>


-- TASK
-- Define _||_ using only nandTwo and any previously defined operations involving nand.
nandOr : Two -> Two -> Two
nandOr x y = nandNot (nandAnd (nandNot x) (nandNot y))

-- TASK
-- Formulate and prove that nandAnd beahves the same way as _||_
nandOrEqOr : (x y : Two) -> TwoEq (nandOr x y) (x || y)
nandOrEqOr ff ff = <>
nandOrEqOr ff tt = <>
nandOrEqOr tt y = <>


-- TASK
-- Define the structure of simple propositional expressions.
-- We want to support
--  1. a "false" value
--  2. a "true" value
--  3. "negating" a PropExpr
--  4. "or-ing" two PropExprs
--  5. "and-ing" two PropExprs
data PropExpr : Set where
  false : PropExpr
  true : PropExpr
  neg : PropExpr -> PropExpr
  _or_ : PropExpr -> PropExpr -> PropExpr
  _and_ : PropExpr -> PropExpr -> PropExpr

-- TASK
-- You should be able to "convert" a boolean to a PropExpr
Two-to-PropExpr : Two -> PropExpr
Two-to-PropExpr ff = false
Two-to-PropExpr tt = true

-- TASK
-- Execute a PropExpr by using the boolean operations that the constructors are named after
interpProp : PropExpr -> Two
interpProp false = ff
interpProp true = tt
interpProp (neg x) = not (interpProp x)
interpProp (x or y) = (interpProp x) || (interpProp y)
interpProp (x and y) = (interpProp x) && (interpProp y)

-- TASK
-- Formulate and prove that if you take two Twos, Two-to-Propexpr them, combine them with your "and" constructor, and interpret them,
-- the result is the same as just simply _&&_-ing the original Twos
_ : (x y : Two) -> TwoEq (interpProp ((Two-to-PropExpr x) and (Two-to-PropExpr y))) (x && y)
_ = λ { ff y -> <>
      ; tt ff -> <>
      ; tt tt -> <>}

{-
-- TASK
-- Formulate and prove that TwoEq is
--  1. reflexive
--  2. symmetric
--  3. transitive
--  4. stable under function application, meaning TwoEq x y implies TwoEq (f x) (f y)
-}

twoEqReflexive : (x : Two) -> TwoEq x x
twoEqReflexive = λ { ff -> <>
                   ; tt -> <>}

twoEqSymmetric : {x y : Two} -> TwoEq x y -> TwoEq y x
twoEqSymmetric {ff} {ff} _ = <>
twoEqSymmetric {tt} {tt} _ = <>

twoEqTransitive : {x y z : Two} -> TwoEq x y -> TwoEq y z -> TwoEq x z
twoEqTransitive {ff} {ff} {ff} <> <> = <>
twoEqTransitive {tt} {tt} {tt} <> <> = <>

twoEqStable : (x y : Two) (f : Two -> Two) -> TwoEq x y -> TwoEq (f x) (f y)
twoEqStable ff ff f <> = twoEqReflexive (f ff)
twoEqStable tt tt f <> = twoEqReflexive (f tt)