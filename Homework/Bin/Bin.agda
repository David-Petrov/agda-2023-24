{-# OPTIONS --no-unicode #-}

module Homework.Bin.Bin where

import Lib.Nat as Nat
open Nat using (Nat; _+N_)
open import Lib.Eq
open import Lib.Zero
open import Lib.One

data Bin : Set where
  end : Bin
  _O : Bin -> Bin
  _I : Bin -> Bin

infixr 12 _O
infixr 12 _I

_ : Bin
_ = end I O I

suc : Bin -> Bin
suc end = end I
suc (n O) = n I
suc (n I) = (suc n) O

_ : suc end == end I
_ = refl

_ : suc (end I I) == end I O O
_ = refl

toNat : Bin -> Nat
toNat end = 0
toNat (n O) = (toNat n) +N (toNat n)
toNat (n I) = Nat.suc ((toNat n) +N (toNat n))

_ : toNat (end I I I) == 7
_ = refl

_ : toNat (end I I O) == 6
_ = refl

_ : toNat (end O) == 0
_ = refl

_ : toNat end == 0
_ = refl

fromNat : Nat -> Bin
fromNat Nat.zero = end
fromNat (Nat.suc x) = suc (fromNat x)

_ : fromNat 0 == end
_ = refl

_ : fromNat 1 == end I
_ = refl

_ : fromNat 8 == end I O O O
_ = refl

toNat-suc : (b : Bin) -> toNat (suc b) == Nat.suc (toNat b)
toNat-suc end = refl
toNat-suc (b O) = refl
toNat-suc (b I) = ==-symm (
  Nat.suc (Nat.suc (toNat b +N toNat b))
    =[ Nat.suc $= Nat.+N-right-suc (toNat b) (toNat b) ]
  Nat.suc (toNat b +N Nat.suc (toNat b))
    =[]
  Nat.suc (toNat b) +N Nat.suc (toNat b)
    =[ ((Nat.suc (toNat b) +N_) $= ==-symm (toNat-suc b)) ]
  Nat.suc (toNat b) +N toNat (suc b)
    =[ Nat.+N-commut (Nat.suc (toNat b)) (toNat (suc b)) ]
  toNat (suc b) +N Nat.suc (toNat b)
    =[ (toNat (suc b) +N_) $= ==-symm (toNat-suc b) ]
  toNat (suc b) +N toNat (suc b)
    QED)

-- or alternatively (without the `==-symm`s)
toNat-suc' : (b : Bin) -> toNat (suc b) == Nat.suc (toNat b)
toNat-suc' end = refl
toNat-suc' (b O) = refl
toNat-suc' (b I) =
  toNat (suc b) +N toNat (suc b)
    =[ (toNat (suc b) +N_) $= toNat-suc b ]
  toNat (suc b) +N Nat.suc (toNat b)
    =[ Nat.+N-commut (toNat (suc b)) (Nat.suc (toNat b)) ]
  Nat.suc (toNat b) +N toNat (suc b)
    =[ ((Nat.suc (toNat b) +N_) $= toNat-suc b) ]
  Nat.suc (toNat b) +N Nat.suc (toNat b)
    =[]
  Nat.suc (toNat b +N Nat.suc (toNat b))
    =[ Nat.suc $= ==-symm (Nat.+N-right-suc (toNat b) (toNat b)) ]
  Nat.suc (Nat.suc (toNat b +N toNat b))
    QED

to-from-id : (n : Nat) -> toNat (fromNat n) == n
to-from-id Nat.zero = refl
to-from-id (Nat.suc n) =
  toNat (suc (fromNat n))
    =[ toNat-suc (fromNat n) ]
  Nat.suc (toNat (fromNat n))
    =[ Nat.suc $= to-from-id n ]
  Nat.suc n
    QED

data LeadingOne : Bin -> Set where
  endI : LeadingOne (end I)
  _O : {b : Bin} -> LeadingOne b -> LeadingOne (b O)
  _I : {b : Bin} -> LeadingOne b -> LeadingOne (b I)

data Can : Bin -> Set where
  end : Can end
  leadingOne : {b : Bin} -> LeadingOne b -> Can b

suc-LeadingOne : {b : Bin} -> LeadingOne b -> LeadingOne (suc b)
suc-LeadingOne endI = endI O
suc-LeadingOne (l O) = l I
suc-LeadingOne (l I) = (suc-LeadingOne l) O

suc-Can : {b : Bin} -> Can b -> Can (suc b)
suc-Can end = leadingOne endI
suc-Can (leadingOne l) = leadingOne (suc-LeadingOne l)

fromNat-Can : (n : Nat) -> Can (fromNat n)
fromNat-Can Nat.zero = end
fromNat-Can (Nat.suc n) = suc-Can (fromNat-Can n)

_+B_ : Bin -> Bin -> Bin
end +B b2 = b2
b1 O +B end = b1 O
b1 O +B b2 O = (b1 +B b2) O
b1 O +B b2 I = (b1 +B b2) I
b1 I +B end = b1 I
b1 I +B b2 O = (b1 +B b2) I
b1 I +B b2 I = (suc (b1 +B b2)) O

infixr 11 _+B_

_ : end +B end I I I I == end I I I I
_ = refl

_ : end I O O +B end == end I O O
_ = refl

_ : end I I +B end I I I I == end I O O I O
_ = refl

_ : end I I I +B end I O I == end I I O O
_ = refl

+B-right-end : (b : Bin) -> b +B end == b
+B-right-end end = refl
+B-right-end (b O) = refl
+B-right-end (b I) = refl

+B-left-suc : (b v : Bin) -> suc b +B v == suc (b +B v)
+B-left-suc end end = refl
+B-left-suc end (v O) = refl
+B-left-suc end (v I) = refl
+B-left-suc (b O) end = refl
+B-left-suc (b O) (v O) = refl
+B-left-suc (b O) (v I) = refl
+B-left-suc (b I) end = refl
+B-left-suc (b I) (v O) = (_O $= +B-left-suc b v)
+B-left-suc (b I) (v I) = (_I $= +B-left-suc b v)

+B-right-suc : (b v : Bin) -> b +B suc v == suc (b +B v)
+B-right-suc end end = refl
+B-right-suc end (v O) = refl
+B-right-suc end (v I) = refl
+B-right-suc (b O) end = _I $= +B-right-end b
+B-right-suc (b O) (v O) = refl
+B-right-suc (b O) (v I) = _O $= +B-right-suc b v
+B-right-suc (b I) end = _O $= suc $= +B-right-end b
+B-right-suc (b I) (v O) = refl
+B-right-suc (b I) (v I) = _I $= +B-right-suc b v

fromNat-+N-+B-commutes : (n m : Nat) -> fromNat (n +N m) == fromNat n +B fromNat m
fromNat-+N-+B-commutes Nat.zero m = refl
fromNat-+N-+B-commutes (Nat.suc n) m =
  suc (fromNat (n +N m))
    =[ suc $= fromNat-+N-+B-commutes n m ]
  suc ((fromNat n) +B fromNat m)
    =[ ==-symm (+B-left-suc (fromNat n) (fromNat m)) ]
  (suc (fromNat n) +B fromNat m)
    QED

+B-same-shift : {b : Bin} -> LeadingOne b -> b +B b == b O
+B-same-shift endI = refl
+B-same-shift {b O} (l O) =
  (b +B b) O
    =[ _O $= +B-same-shift l ]
  (b O) O
    QED
+B-same-shift {b I} (l I) =
  (suc (b +B b)) O
    =[ _O $= suc $= +B-same-shift l ]
  (suc (b O)) O
    =[ _O $= refl ]
  (b I) O
    QED

from-to-id-Can : (b : Bin) -> Can b -> fromNat (toNat b) == b
from-to-id-Can end c = refl
from-to-id-Can (b O) (leadingOne (b2 O)) =
  fromNat (toNat b +N toNat b)
    =[ fromNat-+N-+B-commutes (toNat b) (toNat b) ]
  fromNat (toNat b) +B fromNat (toNat b)
    =[ _+B_ $= from-to-id-Can b (leadingOne b2) =$ fromNat (toNat b) ]
  b +B fromNat (toNat b)
    =[ b +B_ $= from-to-id-Can b (leadingOne b2) ]
  b +B b
    =[ +B-same-shift b2 ]
  b O
    QED
from-to-id-Can (.end I) (leadingOne endI) = refl
from-to-id-Can (b I) (leadingOne (b2 I)) =
  suc (fromNat (toNat b +N toNat b))
    =[ suc $= fromNat-+N-+B-commutes (toNat b) (toNat b) ]
  suc (fromNat (toNat b) +B fromNat (toNat b))
    =[ suc $= (_+B_ $= from-to-id-Can b (leadingOne b2) =$ fromNat (toNat b)) ]
  suc (b +B fromNat (toNat b))
    =[ suc $= b +B_ $= from-to-id-Can b (leadingOne b2) ]
  suc (b +B b)
    =[ suc $= +B-same-shift b2 ]
  b I
    QED
