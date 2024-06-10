{-# OPTIONS --no-unicode #-}

module Homework.PropCalc.PropCalc where

-- open import Lib.EqExplicitRefl
open import Lib.Two
open import Lib.Eq

-- TASK
-- Prove _&&_ commutative
&&-commut : (b1 b2 : Two) -> b1 && b2 == b2 && b1
&&-commut ff ff = refl
&&-commut ff tt = refl
&&-commut tt ff = refl
&&-commut tt tt = refl

-- TASK
-- Prove _&&_ associative
&&-assoc : (b1 b2 b3 : Two) -> (b1 && b2) && b3 == b1 && (b2 && b3)
&&-assoc ff b2 b3 = refl
&&-assoc tt b2 b3 = refl

-- LEMMA

-- TASK
-- Formulate and prove the fact that _||_ is commutative
||-commut : (b1 b2 : Two) -> (b1 || b2) == (b2 || b1)
||-commut ff ff = refl
||-commut ff tt = refl
||-commut tt ff = refl
||-commut tt tt = refl

-- TASK
-- State assocativity of || and prove it
||-assoc : (b1 b2 b3 : Two) -> ((b1 || b2) || b3) == (b1 || (b2 || b3))
||-assoc ff b2 b3 = refl
||-assoc tt b2 b3 = refl

-- TASK
-- Formulate and prove De Morgan's laws
DeMorgan1 : (b1 b2 : Two) -> not (b1 && b2) == not b1 || not b2
DeMorgan1 ff b2 = refl
DeMorgan1 tt b2 = refl

DeMorgan2 : (b1 b2 : Two) -> not (b1 || b2) == not b1 && not b2
DeMorgan2 ff b2 = refl
DeMorgan2 tt b2 = refl

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
_ : (b1 b2 : Two) -> interpProp (Two-to-PropExpr b1 and Two-to-PropExpr b2) == b1 && b2
_ = λ { ff _ → refl
      ; tt ff → refl
      ; tt tt → refl }

-- TASK
-- Define the NAND operation over bools
nandTwo : Two -> Two -> Two
nandTwo b1 b2  = not (b1 && b2)

-- TASK
-- Define ff using tt and NAND
nandff : Two
nandff = nandTwo tt tt

-- TASK
-- Formulate and prove that nandff is the same thing as ff
_ : nandff == ff
_ = refl

-- TASK
-- Define negation using only nandTwo and any previously defined operations involving nand.
nandNot : Two -> Two
nandNot b = nandTwo b b

-- TASK
-- Formulate and prove that nandNot behaves the same way as not
nandNot-eq-not : (b : Two) -> nandNot b == not b
nandNot-eq-not ff = refl
nandNot-eq-not tt = refl

-- TASK
-- Define _&&_ using only nandTwo and any previously defined operations involving nand.
nandAnd : Two -> Two -> Two
nandAnd b1 b2 = nandTwo (nandTwo b1 b2) (nandTwo b1 b2)

-- TASK
-- Formulate and prove that nandAnd beahves the same way as _&&_
nandAndEq&& : (b1 b2 : Two) -> nandAnd b1 b2 == b1 && b2
nandAndEq&& ff b2 = refl
nandAndEq&& tt ff = refl
nandAndEq&& tt tt = refl

-- TASK
-- Define _||_ using only nandTwo and any previously defined operations involving nand.
nandOr : Two -> Two -> Two
nandOr b1 b2 = nandTwo (nandNot b1) (nandNot b2)

-- TASK
-- Formulate and prove that nandAnd beahves the same way as _||_
nandOrEq|| : (b1 b2 : Two) -> nandOr b1 b2 == b1 || b2
nandOrEq|| ff ff = refl
nandOrEq|| ff tt = refl
nandOrEq|| tt _ = refl

-- TASK
-- Define the structure of "nand expressions", meaning minimal boolean expressions expresed purely via NAND.
-- We want to support
--   1. a "true" value
--   2. the NAND of two NandExprs
data NandExpr : Set where
  true : NandExpr
  _nand_ : NandExpr -> NandExpr -> NandExpr

-- TASK
-- Execute a NandExpr
interpNand : NandExpr -> Two
interpNand true = tt
interpNand (x nand y) = nandTwo (interpNand x) (interpNand y)

-- TASK
-- Transpile a PropExpr to a NandExpr
Prop-to-Nand : PropExpr -> NandExpr
Prop-to-Nand false = true nand true
Prop-to-Nand true = true
Prop-to-Nand (neg x) = (Prop-to-Nand x) nand (Prop-to-Nand x)
Prop-to-Nand (x or y) = ((Prop-to-Nand x) nand (Prop-to-Nand x)) nand ((Prop-to-Nand y) nand (Prop-to-Nand y))
Prop-to-Nand (x and y) = ((Prop-to-Nand x) nand (Prop-to-Nand y)) nand ((Prop-to-Nand x) nand (Prop-to-Nand y))

-- TASK
-- Formulate and prove that your Prop-to-Nand transpilation is correct in terms of interpProp and interpNand,
-- i.e. if you take a PropExpr, translate it to a NandExpr, and then interpNand it,
-- the result should be the same as interpProp-ing the original expression

-- LEMMA
x&&x==x : (x : Two) -> x && x == x
x&&x==x ff = refl
x&&x==x tt = refl

x||x==x : (x : Two) -> x || x == x
x||x==x ff = refl
x||x==x tt = refl

helper : (b1 b2 : Two) -> not (not b1 && not b2) == b1 || b2
helper ff ff = refl
helper ff tt = refl
helper tt _  = refl

-- an alternative for _$=_, but with two function arguments
_$=_,_ :
  {A B C : Set} ->
  {x x' : A}
  {y y' : B} ->
  (f : A -> B -> C) ->
  x == x' ->
  y == y' ->
  f x y == f x' y'
f $= refl , refl = refl
infixr 5 _$=_,_

yeswee : (p : PropExpr) -> interpNand (Prop-to-Nand p) == interpProp p
yeswee false = refl
yeswee true = refl
yeswee (neg p) =
  interpNand (Prop-to-Nand (neg p))
    =[]
  not (interpNand (Prop-to-Nand p) && interpNand (Prop-to-Nand p))
    =[ not $= x&&x==x (interpNand (Prop-to-Nand p)) ]
  not (interpNand (Prop-to-Nand p))
    =[ not $= yeswee p ]
  not (interpProp p)
    =[]
  interpProp (neg p)
    QED




-- My suffered through "better" implementation...
-- Pieces of code that were "shortened/optimized" are isolated in blocks with their commented out alternative below them :D
yeswee (p1 or p2) =
  not (
       not (interpNand (Prop-to-Nand p1) && interpNand (Prop-to-Nand p1))
    && not (interpNand (Prop-to-Nand p2) && interpNand (Prop-to-Nand p2)))

    =[ helper2 (interpNand (Prop-to-Nand p1)) (interpNand (Prop-to-Nand p2)) ]


  interpNand (Prop-to-Nand p1) || interpNand (Prop-to-Nand p2)

    =[ _||_ $= (yeswee p1) , (yeswee p2) ]


  interpProp p1 || interpProp p2
    QED
  where
    helper2 : (b1 b2 : Two) -> not (not (b1 && b1) && not (b2 && b2)) == b1 || b2
    helper2 ff ff = refl
    helper2 ff tt = refl
    helper2 tt _  = refl

yeswee (p1 and p2) =
  interpNand (Prop-to-Nand (p1 and p2))
    =[]
  not (not (interpNand (Prop-to-Nand p1) && interpNand (Prop-to-Nand p2)) &&
       not (interpNand (Prop-to-Nand p1) && interpNand (Prop-to-Nand p2)))

    =[ helper3 (interpNand (Prop-to-Nand p1)) (interpNand (Prop-to-Nand p2)) ]


  interpNand (Prop-to-Nand p1) && interpNand (Prop-to-Nand p2)



  interpProp p1 && interpProp p2
    QED
  where
    helper3 : (b1 b2 : Two) -> not (not (b1 && b2) && not (b1 && b2)) == b1 && b2
    helper3 ff _  = refl
    helper3 tt ff = refl
    helper3 tt tt = refl

nandAnd : Two -> Two -> Two
nandAnd b1 b2 = nandTwo (nandTwo b1 b2) (nandTwo b1 b2)

-- TASK
-- Formulate and prove that nandAnd beahves the same way as _&&_
nandAndEq&& : (b1 b2 : Two) -> nandAnd b1 b2 == b1 && b2
nandAndEq&& ff b2 = refl
nandAndEq&& tt ff = refl
nandAndEq&& tt tt = refl