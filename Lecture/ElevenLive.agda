{-# OPTIONS --type-in-type #-}
{-# OPTIONS --no-unicode #-}

module Lecture.ElevenLive where

open import Lib.Eq
open import Lib.List
open import Lib.Vec
open import Lib.Nat
open import Lib.One
open import Lib.Two
open import Lib.Zero
open import Lib.Sigma

-- TODO:
-- discuss levels briefly
-- example: list of types
-- example: record containing Sets
--
-- TODO: {-# OPTIONS --type-in-type #-}
--
-- TODO: postulate

-- "тип"
-- data Nat : Set where
-- data List (A : Set) : Set where
-- data List {l : Level} (A : Set l) : Set (l + 1) where
--
-- List : ?????
-- Set : ?????

-- Set : Set

-- Set0 : Set1
-- Set1 : Set2
-- Set2 : ...
-- Set_n : Set_(n+1)

-- Set : Set

--record Foo : Set where
--  field
--    bar : Set


-- TODO: categories as an abstraction for compositions
-- TODO: reminder on copatterns, going to be useful again
-- TODO: AGDA as an example
-- TODO: THREE as an example

-- TODO: monoids in general
-- TODO: monoids as single object categories
-- "all of the info is in the arrows"
-- TODO: +N as example

-- TODO: preorders
-- "all of the info is in the objects"/"it doesn't matter how you get from object A to object B"
-- TODO: _<=_ as example

-- TODO: functors as an abstraction for homomorphisms
-- TODO: Maybe as an example

-- TODO: extensionality
-- example: addNat defined on its two args
-- example: linear search vs binary search

record Category : Set where
  field
    Obj : Set
    Arr : (x : Obj) -> (y : Obj) -> Set
    idArr : {x : Obj} -> Arr x x
    comp :
      {x y z : Obj} ->
      (f : Arr x y) ->
      (g : Arr y z) ->
      Arr x z
    idArr-comp :
      {x y : Obj}
      (f : Arr x y) ->
      comp (idArr {x}) f == f
    comp-idArr :
      {x y : Obj}
      (f : Arr x y) ->
      comp f (idArr {y}) == f
    assoc :
      {x y z w : Obj}
      (f : Arr x y) (g : Arr y z) (h : Arr z w) ->
      comp (comp f g) h == comp f (comp g h)

open Category public

id : {A : Set} -> A -> A
id x = x

-- NOTE
-- Function composition
_>>_ : {S R T : Set} -> (S -> R) -> (R -> T) -> S -> T
_>>_ f g x = g (f x)

-- C-c C-c
AGDA : Category
Obj AGDA = Set
Arr AGDA A B = A -> B
idArr AGDA = id
comp AGDA = _>>_
idArr-comp AGDA f = refl
-- comp idArr f
-- _>>_ idArr f
-- _>>_ id f
-- _>>_ (\x -> x) f
-- (\y -> _>>_ (\x -> x) f y)
-- (\y -> f ((\x -> x) y))
-- (\y -> f y)
comp-idArr AGDA f = refl
assoc AGDA f g h = refl
-- comp (comp f g) h == comp f (comp g h)
-- (f >> g) >> h == f >> (g >> h)

-- * --> *
--  \    |
--   \   |
--    \  |
--     \ |
--      \|
--       v
--       *
module Three where
  data Three : Set where
    -- zero : Three
    -- one : Three
    -- two : Three
    zero one two : Three

  data Arrow : Three -> Three -> Set where
    idArrThree : {x : Three} -> Arrow x x
    zero-one : Arrow zero one
    one-two : Arrow one two
    zero-two : Arrow zero two


  THREE : Category
  Obj THREE = Three
  Arr THREE = Arrow
  idArr THREE = idArrThree
  comp THREE idArrThree g = g
  comp THREE f idArrThree = f
  comp THREE zero-one one-two = zero-two
  idArr-comp THREE f = refl
  comp-idArr THREE idArrThree = refl
  comp-idArr THREE zero-one = refl
  comp-idArr THREE one-two = refl
  comp-idArr THREE zero-two = refl
  assoc THREE idArrThree idArrThree idArrThree = refl
  assoc THREE idArrThree idArrThree zero-one = refl
  assoc THREE idArrThree idArrThree one-two = refl
  assoc THREE idArrThree idArrThree zero-two = refl
  assoc THREE idArrThree zero-one idArrThree = refl
  assoc THREE idArrThree zero-one one-two = refl
  assoc THREE idArrThree one-two idArrThree = refl
  assoc THREE idArrThree zero-two idArrThree = refl
  assoc THREE zero-one idArrThree idArrThree = refl
  assoc THREE zero-one idArrThree one-two = refl
  assoc THREE zero-one one-two idArrThree = refl
  assoc THREE one-two idArrThree idArrThree = refl
  assoc THREE zero-two idArrThree idArrThree = refl

-- NOTE
-- "All of the info is in the objects", since there's at most one arrow between any two objects.
-- Effectively this means that with preorders we don't care how exactly we get from an arrow A to B,
-- just that there is one
record Preorder : Set where
  field
    cat : Category
    one-arrow :
      {x y : Obj cat} ->
      (f g : Arr cat x y) ->
      f == g


<=-unique : {n m : Nat} (p q : n <= m) -> p == q
<=-unique ozero ozero = refl
<=-unique (osuc p) (osuc q) = ap osuc (<=-unique p q)

-- TASK
<=-Cat : Category
Obj <=-Cat = Nat
Arr <=-Cat = _<=_
idArr <=-Cat {x} = <=-refl x
comp <=-Cat = <=-trans
idArr-comp <=-Cat ozero = refl
idArr-comp <=-Cat (osuc f) = osuc $= idArr-comp <=-Cat f
comp-idArr <=-Cat ozero = refl
comp-idArr <=-Cat (osuc f) = osuc $= comp-idArr <=-Cat f
assoc <=-Cat f g h = <=-unique (<=-trans (<=-trans f g) h) (<=-trans f (<=-trans g h))

-- TASK
<=-Preorder : Preorder
Preorder.cat <=-Preorder = <=-Cat
Preorder.one-arrow <=-Preorder = <=-unique

-- NOTE
-- "All of the info is in the arrows", since we only have one object.
-- Effectively this means that we only care about the arrows, and the case is usually that we have some operations as arrows.
record Monoid : Set where
  field
    cat : Category
    Obj-is-One : Obj cat == One

-- TASK
Nat+N-Cat : Category
Obj Nat+N-Cat = One
Arr Nat+N-Cat _ _ = Nat
idArr Nat+N-Cat = zero
comp Nat+N-Cat = _+N_
idArr-comp Nat+N-Cat f = refl
comp-idArr Nat+N-Cat = +N-right-zero
assoc Nat+N-Cat = +N-assoc

Nat+N-Monoid : Monoid
Monoid.cat Nat+N-Monoid = Nat+N-Cat
Monoid.Obj-is-One Nat+N-Monoid = refl

-- f : G -> H
-- f (eps_G) == eps_H
-- f (x <G> y) == f (x) <H> f (y)
-- F ((f >> g)) == F f >> F g

-- Functor
record _=>_ (C D : Category) : Set where
  field
    F-Obj : Obj C -> Obj D
    F-map :
      {x y : Obj C} ->
      (f : Arr C x y) ->
      Arr D (F-Obj x) (F-Obj y)

    F-map-id :
      (x : Obj C) ->
      F-map (idArr C {x}) == idArr D {F-Obj x}

    F-map-comp :
      {x y z : Obj C}
      (f : Arr C x y) (g : Arr C y z) ->
      F-map (comp C f g) == comp D (F-map f) (F-map g)

open _=>_ public

data Maybe (A : Set) : Set where
  just : A -> Maybe A
  nothing : Maybe A

-- има аксиома ext
postulate
  ext :
    {A B : Set} {f g : A -> B} ->
    ((x : A) -> f x == g x) ->
    f == g

-- linear search
-- binary search

-- TASK
-- A category with one object
-- *
ONE : Category
Obj ONE = One
Arr ONE <> <> = One
idArr ONE = <>
comp ONE f g = <>
idArr-comp ONE <> = refl
comp-idArr ONE <> = refl
assoc ONE f g h = refl

-- TASK
-- A category with two objects, with an arrow between them
-- * --> *
module TwoCat where
  data ArrTwo : Two -> Two -> Set where
    idArrTwo : {x : Two} -> ArrTwo x x
    zero-one : ArrTwo ff tt

  TWO : Category
  Obj TWO = Two
  Arr TWO = ArrTwo
  idArr TWO = idArrTwo
  comp TWO idArrTwo f = f
  comp TWO zero-one idArrTwo = zero-one
  idArr-comp TWO f = refl
  comp-idArr TWO idArrTwo = refl
  comp-idArr TWO zero-one = refl
  assoc TWO idArrTwo g h = refl
  assoc TWO zero-one idArrTwo idArrTwo = refl

-- TASK
-- Similarly to Nat+N-Cat, +L induces a category which is also a monoid.
-- The objects will be One, since it's a monoid, and the arrows will be given by the
-- list append operation (_+L_).
List-+L-Cat : Set -> Category
Obj (List-+L-Cat A) = One
Arr (List-+L-Cat A) x y = List A
idArr (List-+L-Cat A) = []
comp (List-+L-Cat A) = _+L_
idArr-comp (List-+L-Cat A) f = refl
comp-idArr (List-+L-Cat A) f = +L-right-id f
assoc (List-+L-Cat A) = +L-assoc

-- TASK
List-+L-Monoid : Set -> Monoid
Monoid.cat (List-+L-Monoid A) = List-+L-Cat A
Monoid.Obj-is-One (List-+L-Monoid A) = refl

-- TASK
-- A Discrete category is one in which the only arrows are the identity arrows
-- An example of such a category is the one formed with an arbitrary type, and _==_ as arrows
-- Implement the discrete category where the objects are elements of the type X, and
-- the arrows are the equalities between those elements.
module DiscreteEq (X : Set) where
  Discrete== : Category
  Obj Discrete== = X
  Arr Discrete== = _==_
  idArr Discrete== = refl
  comp Discrete== f g = ==-trans f g
  idArr-comp Discrete== f = refl
  comp-idArr Discrete== refl = refl
  assoc Discrete== refl refl refl = refl

-- TASK
-- We can make a category with whatever arrows we like if our objects are Zero.
module EmptyCat (Arrows : Set) where
  EMPTY : Category
  Obj EMPTY = Zero
  Arr EMPTY ()
  idArr EMPTY {()}
  comp EMPTY {()}
  idArr-comp EMPTY {()}
  comp-idArr EMPTY {()}
  assoc EMPTY {()}

-- TASK
-- We can always flip the directions of arrows in a category to form the "opposite" category.
-- This actually turns out to be a very useful concept in general.
Op : Category -> Category
Obj (Op A) = Obj A
Arr (Op A) = \ e1 e2 -> Arr A e2 e1
idArr (Op A) = idArr A
comp (Op A) f g = comp A g f
idArr-comp (Op A) = comp-idArr A
comp-idArr (Op A) = idArr-comp A
assoc (Op A) f g h = ==-symm (assoc A h g f)

-- TASK
-- Given two categories, we can form their product, by having objects which are tuples of objects
-- of our original categories, and lifting everything from our original categories pointwise for those tuples.
-- _*_ is your friend.
Product : Category -> Category -> Category
Obj (Product A B) = Obj A * Obj B
Arr (Product A B) x y = Arr A (fst x) (fst y) * Arr B (snd x) (snd y)
idArr (Product A B) = idArr A , idArr B
comp (Product A B) f g = comp A (fst f) (fst g) , comp B (snd f) (snd g)
idArr-comp (Product A B) (f1 , f2) =
  comp A (idArr A) f1 , comp B (idArr B) f2
    =[ _, comp B (idArr B) f2 $= idArr-comp A f1 ]
  f1 , comp B (idArr B) f2
    =[ f1 ,_ $= idArr-comp B f2 ]
  f1 , f2
    QED
comp-idArr (Product A B) (f1 , f2) =
  comp A f1 (idArr A) , comp B f2 (idArr B)
    =[ comp A f1 (idArr A) ,_ $= comp-idArr B f2 ]
  comp A f1 (idArr A) , f2
    =[ _, f2 $= comp-idArr A f1 ]
  f1 , f2
    QED
assoc (Product A B) (f1 , f2) (g1 , g2) (h1 , h2) =
  comp A (comp A f1 g1) h1 , comp B (comp B f2 g2) h2
    =[ comp A (comp A f1 g1) h1 ,_ $= assoc B f2 g2 h2 ]
  comp A (comp A f1 g1) h1 , comp B f2 (comp B g2 h2)
    =[ _, comp B f2 (comp B g2 h2) $= assoc A f1 g1 h1 ]
  comp A f1 (comp A g1 h1) , comp B f2 (comp B g2 h2)
    QED

-- TASK
-- "Doing nothing" is a functor, i.e. we don't change the objects and we don't change the arrows.
ID : (C : Category) -> C => C
F-Obj (ID C) x = x
F-map (ID C) f = f
F-map-id (ID C) x = refl
F-map-comp (ID C) f g = refl

fmapMaybe :
  {A B : Set} ->
  (A -> B) ->
  Maybe A ->
  Maybe B
fmapMaybe f (just x) = just (f x)
fmapMaybe f nothing = nothing

fmapMaybe-id :
  {A : Set}
  (x : Maybe A) ->
  fmapMaybe id x == x
fmapMaybe-id (just x) = refl
fmapMaybe-id nothing = refl

-- TASK
MAYBE : AGDA => AGDA
F-Obj MAYBE A = Maybe A
F-map MAYBE = fmapMaybe
F-map-id MAYBE _ = ext fmapMaybe-id
F-map-comp MAYBE f g = ext \{ (just x) -> refl
                            ; nothing -> refl}

-- TASK
map : {A B : Set} -> (A -> B) -> List A -> List B
map f [] = []
map f (x ,- xs) = f x ,- map f xs

-- TASK
-- Mapping with the identity function does nothing
map-id : {A : Set} (xs : List A) -> map id xs == xs
map-id [] = refl
map-id (x ,- xs) =
  id x ,- map id xs
    =[]
  x ,- map id xs
    =[ x ,-_ $= map-id xs ]
  x ,- xs
    QED

-- TASK
-- Mapping with a composition of functions is the same as mapping with
-- one function, and then mapping with the other function.
map-compose :
  {A B C : Set} (f : A -> B) (g : B -> C) (xs : List A) ->
  map (f >> g) xs == map g (map f xs)
map-compose f g [] = refl
map-compose f g (x ,- xs) =
  map (f >> g) (x ,- xs)
    =[]
  g (f x) ,- map (f >> g) xs
    =[ g (f x) ,-_ $= map-compose f g xs ]
  g (f x) ,- map g (map f xs)
    =[]
  map g (map f (x ,- xs))
    QED

-- TASK
-- The List type constructor is a functor, in the same way that Maybe is a functor.
LIST : AGDA => AGDA
F-Obj LIST A = List A
F-map LIST f xs = map f xs
F-map-id LIST xs = ext map-id
F-map-comp LIST f g = ext (map-compose f g)

-- TASK
-- Addition with the constant k forms a functor over the preorder Nat category
ADD : Nat -> <=-Cat => <=-Cat
F-Obj (ADD k) = \x -> k +N x
F-map (ADD zero) f = f
F-map (ADD (suc k)) f = osuc (F-map (ADD k) f)
F-map-id (ADD zero) x = refl
F-map-id (ADD (suc k)) x = osuc $= F-map-id (ADD k) x
F-map-comp (ADD zero) f g = refl
F-map-comp (ADD (suc k)) f g = osuc $= F-map-comp (ADD k) f g

-- TASK
-- Mapping with a function (f : X -> Y) over a list induces a functor between the monoid
-- categories of lists over X and Y respectively.
LIST+L : {X Y : Set} (f : X -> Y) -> List-+L-Cat X => List-+L-Cat Y
F-Obj (LIST+L f) <> = <>
F-map (LIST+L f) xs = map f xs
F-map-id (LIST+L f) <> = refl
F-map-comp (LIST+L f) [] xs2 = refl
F-map-comp (LIST+L f) (x ,- xs1) xs2 = f x ,-_ $= F-map-comp (LIST+L f) xs1 xs2

-- TASK
-- Define the "is prefix of" relation between lists
data _<=L_ {A : Set} : List A -> List A -> Set where
  <=L-nil : {xs : List A} -> [] <=L xs
  <=L-cons : {x : A} {xs ys : List A} -> xs <=L ys -> x ,- xs <=L x ,- ys

infix 15 _<=L_

module <=L-Cats {A : Set} where
  -- TASK
  -- Prove that lists of A equipped with _<=L_ form a category
  <=L-Cat : Category
  Obj <=L-Cat = List A
  Arr <=L-Cat = _<=L_
  idArr <=L-Cat {[]} = <=L-nil
  idArr <=L-Cat {x ,- xs} = <=L-cons (idArr <=L-Cat)
  comp <=L-Cat <=L-nil g = <=L-nil
  comp <=L-Cat (<=L-cons f) (<=L-cons g) = <=L-cons (comp <=L-Cat f g)
  idArr-comp <=L-Cat <=L-nil = refl
  idArr-comp <=L-Cat (<=L-cons f) = <=L-cons $= idArr-comp <=L-Cat f
  comp-idArr <=L-Cat <=L-nil = refl
  comp-idArr <=L-Cat (<=L-cons f) = <=L-cons $= comp-idArr <=L-Cat f
  assoc <=L-Cat <=L-nil <=L-nil h = refl
  assoc <=L-Cat <=L-nil (<=L-cons g) (<=L-cons h) = refl
  assoc <=L-Cat (<=L-cons f) (<=L-cons g) (<=L-cons h) = <=L-cons $= assoc <=L-Cat f g h

  -- TASK
  -- Prove that that category is a preorder
  <=L-Preorder : Preorder
  Preorder.cat <=L-Preorder = <=L-Cat
  Preorder.one-arrow <=L-Preorder = hui
    where
      hui : {xs ys : List A} -> (f g : xs <=L ys) -> f == g
      hui <=L-nil <=L-nil = refl
      hui (<=L-cons f) (<=L-cons g) = <=L-cons $= hui f g

  -- TASK
  -- We can form a functor from list prefixes to _<=_.
  -- Implement it.
  Drop-Elems : <=L-Cat => <=-Cat
  F-Obj Drop-Elems = length
  F-map Drop-Elems <=L-nil = ozero
  F-map Drop-Elems (<=L-cons f) = osuc (F-map Drop-Elems f)
  F-map-id Drop-Elems [] = refl
  F-map-id Drop-Elems (x ,- xs) = osuc $= F-map-id Drop-Elems xs
  F-map-comp Drop-Elems <=L-nil g = refl
  F-map-comp Drop-Elems (<=L-cons f) (<=L-cons g) = osuc $= F-map-comp Drop-Elems f g

-- TASK
-- Implement the function which takes a prefix of n elements from a Vector of size m,
-- by using the proof that n <= m to allow us to do so
-- We've already implement this previously, so feel free to copy it if you'd like
vTake : {A : Set} {n m : Nat} -> n <= m -> Vec A m -> Vec A n
vTake ozero xs = []
vTake (osuc f) (x ,- xs) = x ,- vTake f xs

-- TASK
-- vTake gives rise to a functor, sending _<=_ functions over Vec A
-- If we look at vTakes signature, we'll notice that n <= m is transformed into (Vec A m -> Vec A n) -
-- note how the places of n and m are swapped.
-- As a consequence, we need to use the opposite cateogry of <=-Cat here, to make things line up.
{-# TERMINATING #-}
VTAKE : Set -> Op <=-Cat => AGDA
F-Obj (VTAKE A) n = Vec A n
F-map (VTAKE A) f xs = vTake f xs
F-map-id (VTAKE A) zero = ext \{ [] -> refl}
F-map-id (VTAKE A) (suc n) = ext \{ (x ,- xs) -> x ,-_ $= (F-map-id (VTAKE A) n =$ xs)}
F-map-comp (VTAKE A) f ozero = refl
F-map-comp (VTAKE A) (osuc f) (osuc g) = ext \{(x ,- xs) -> (x ,-_) $= (F-map-comp (VTAKE A) f g =$ xs)}

module FreeCat (X : Set) (R : X -> X -> Set) where
  -- TASK
  -- Given a type X and a binary relation R over X, we can form a "free category" based on X and R in the usual sense of "free algebraic structure".
  -- That is, we will force all the properties required of a category to hold synthetically, by introducing a new relation Free R : X -> X -> Set,
  -- such that X and Free R form a category.
  --
  -- Essentially, this means that we want to add some additional properties to R to get Free R, so that we can then prove our Category laws
  --
  -- Implement the datatype Free which adds those properties to R. It might be helpful to first try implementing the FREE
  -- category, to figure out what exactly you need.
  data Free : X -> X -> Set where
    f-id : {x : X} -> Free x x
    f-trans : {x y z : X} -> R x y -> Free y z -> Free x z

  -- TASK
  -- Since Free will form the arrows for our category, we will of course also need a way to compose Frees
  compFree : {x y z : X} -> Free x y -> Free y z -> Free x z
  compFree f-id r = r
  compFree (f-trans p q) r = f-trans p (compFree q r)

  -- TASK
  -- Implement hte free category over X and R by using Free and compFree
  FREE : Category
  Obj FREE = X
  Arr FREE = Free
  idArr FREE {x} = f-id
  comp FREE = compFree
  idArr-comp FREE f = refl
  comp-idArr FREE f-id = refl
  comp-idArr FREE (f-trans r f) = f-trans r $= comp-idArr FREE f
  assoc FREE f-id _ _ = refl
  assoc FREE (f-trans r f) g h = f-trans r $= assoc FREE f g h

module NatF where
  open FreeCat One (λ _ _ -> One)

  NatF' : Set
  NatF' = Free <> <>

  zero' : NatF'
  zero' = f-id

  suc' : NatF' -> NatF'
  suc' n = f-trans <> n

  _+N'_ : NatF' -> NatF' -> NatF'
  _+N'_ = compFree

  NatToNatF' : Nat -> NatF'
  NatToNatF' zero = f-id
  NatToNatF' (suc n) = suc' (NatToNatF' n)

  NatF'ToNat : NatF' -> Nat
  NatF'ToNat f-id = zero
  NatF'ToNat (f-trans <> n') = suc (NatF'ToNat n')

  khk : (n m : Nat) -> (NatToNatF' n) +N' (NatToNatF' m) == NatToNatF' (n +N m)
  khk zero _ = refl
  khk (suc n) m = suc' $= khk n m

module ListF' (A : Set) where
  open FreeCat One (\ _ _ -> A)

module VecsF' (A : Set) where
  IxType : Set
  IxType = Nat
  data R : IxType -> IxType -> Set where
    bla : {n : Nat} -> A -> R n (suc n)
  open FreeCat IxType R

  vnil : Free zero zero
  vnil = f-id

  vcons : {n : Nat} -> A -> Free n n -> Free (suc n) (suc n)
  vcons x xs = f-trans (bla x) xs

  -- TODO: Implement vnil and vcons, and then do the same as the above khk

module Finite where
  data Fin : Nat -> Set where
    zero : {n : Nat} -> Fin (suc n)
    suc : {n : Nat} -> Fin n -> Fin (suc n)

  -- TASK
  -- We've seen a few finite categories - ZERO, TWO, THREE
  -- We can take advantage of Fin n to define a generalised finite category, mimicking THREE.
  -- If we want a category "of size n", we'll take Fin n to be the objects.
  --
  -- The arrows will roughly be defined as
  -- n ~> m iff n <= m
  --
  -- Think about how to define all of these and implement the FINITE category.

  fin-to-nat : {n : Nat} -> Fin n -> Nat
  fin-to-nat zero = zero
  fin-to-nat (suc x) = suc (fin-to-nat x)

  FINITE : Nat -> Category
  Obj (FINITE n) = Fin n
  Arr (FINITE n) x y = (fin-to-nat x) <= (fin-to-nat y)
  idArr (FINITE n) {x} = <=-refl (fin-to-nat x)
  comp (FINITE n) f g = <=-trans f g
  idArr-comp (FINITE .(suc _)) {zero} {zero} ozero = refl
  idArr-comp (FINITE .(suc _)) {zero} {suc y} ozero = refl
  idArr-comp (FINITE (suc n)) {suc x} {suc y} (osuc f) = osuc $= idArr-comp (FINITE n) f
  comp-idArr (FINITE .(suc _)) {zero} {zero} ozero = refl
  comp-idArr (FINITE .(suc _)) {zero} {suc y} ozero = refl
  comp-idArr (FINITE (suc n)) {suc x} {suc y} (osuc f) = osuc $= comp-idArr (FINITE n) f
  assoc (FINITE zero) {()} {y} {z} {w} f g h
  assoc (FINITE (suc n)) {zero} {zero} {zero} {zero} ozero ozero ozero = refl
  assoc (FINITE (suc n)) {zero} {zero} {zero} {suc w} ozero ozero ozero = refl
  assoc (FINITE (suc n)) {zero} {zero} {suc z} {suc w} ozero ozero (osuc h) = refl
  assoc (FINITE (suc n)) {zero} {suc y} {suc z} {suc w} ozero (osuc g) (osuc h) = refl
  assoc (FINITE (suc n)) {suc x} {suc y} {suc z} {suc w} (osuc f) (osuc g) (osuc h) = osuc $= assoc (FINITE n) f g h
