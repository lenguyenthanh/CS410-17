{-# OPTIONS --type-in-type #-}  -- yes, there will be some cheating in this lecture

module L3 where

open import L1
open import L2

postulate
  extensionality : {S : Set}{T : S -> Set}
                   (f g : (x : S) -> T x) ->
                   ((x : S) -> f x == g x) ->
                   f == g

record Category : Set where
  field

    -- two types of thing
    Obj  : Set                  -- "objects"
    _~>_ : Obj -> Obj -> Set    -- "arrows" or "morphisms"
                                -- or "homomorphisms"
                
    -- two operations
    id~>        : {T : Obj} ->      T ~> T
    _>~>_       : {R S T : Obj} ->  R ~> S  ->  S ~> T  ->  R ~> T

    -- three laws
    law-id~>>~> : {S T : Obj}     (f : S ~> T) ->
                    (id~> >~> f) == f

    law->~>id~> : {S T : Obj}     (f : S ~> T) ->
                    (f >~> id~>) == f

    law->~>>~>  : {Q R S T : Obj} (f : Q ~> R)(g : R ~> S)(h : S ~> T) ->
                    ((f >~> g) >~> h) == (f >~> (g >~> h))

-- Sets and functions are the classic example of a category.
{--}
SET : Category
SET = record
  { Obj = Set
  ; _~>_ = \ S T -> S -> T
  ; id~> = id
  ; _>~>_ = _>>_
  ; law-id~>>~> = \ f -> refl f
  ; law->~>id~> = \ f -> refl f
  ; law->~>>~> = \ f g h -> refl ((f >> g) >> h)
  }

-- A PREORDER is a category where there is at most one arrow between
-- any two objects. (So arrows are unique.)

NAT->= : Category
NAT->= = record
  { Obj = Nat
  ; _~>_ = _>=_
  ; id~> = \ {n} -> refl->= n
  ; _>~>_ = \ { m n p} m>=n n>=p -> trans->= m n p m>=n n>=p
  ; law-id~>>~> = \ { S } { T }  s>=t -> unique  S T (trans->= S S T (refl->= S) s>=t) s>=t
  ; law->~>id~> = \ { S } { T } s>=t -> unique S T (trans->= S T T s>=t (refl->= T)) s>=t
  ; law->~>>~> = λ { m n p q } f g h → unique m q (trans->= m p q (trans->= m n p f g) h) (trans->= m n q f (trans->= n p q g h))
  } where
  unique : (m n : Nat)(p q : m >= n) -> p == q
  unique m zero p q = refl <>
  unique (suc m) (suc n) p q = unique m n p q 

-- A MONOID is a category with Obj = One.
-- The values in the monoid are the *arrows*.
ONE-Nat : Category
ONE-Nat = record
  { Obj = One
  ; _~>_ = \ _ _ -> Nat
  ; id~> = 0
  ; _>~>_ = _+N_
  ; law-id~>>~> = zero-+N
  ; law->~>id~> = +N-zero
  ; law->~>>~> = assocLR-+N
  }

eqUnique : {X : Set}{x y : X}{p q : x == y} -> p == q
eqUnique {p = refl _} {q = refl _} = refl (refl _)

-- A DISCRETE category is one where the only arrows are the identities.
DISCRETE : (X : Set) -> Category
DISCRETE X = record
  { Obj = X
  ; _~>_ = _==_
  ; id~> = \ {x} -> refl x 
  ; _>~>_ = \  { (refl R) (refl .R) → refl R }
  ; law-id~>>~> = \ {S T : X} (f : S == T) -> eqUnique
  ; law->~>id~> = \ {S T : X} (f : S == T) -> eqUnique
  ; law->~>>~> = \ {Q R S T : X} (f : Q == R) (g : R == S) (h : S == T) -> eqUnique
  }



module FUNCTOR where
  open Category
  
  record _=>_ (C D : Category) : Set where  -- "Functor from C to D"
    field
      -- two actions
      F-Obj : Obj C -> Obj D
      F-map : {S T : Obj C} -> _~>_ C S T -> _~>_ D (F-Obj S) (F-Obj T)

      -- two laws
      F-map-id~> : {T : Obj C} -> F-map (id~> C {T}) == id~> D {F-Obj T}
      F-map->~>  : {R S T : Obj C}(f : _~>_ C R S)(g : _~>_ C S T) ->
                     F-map (_>~>_ C f g) == _>~>_ D (F-map f) (F-map g)

open FUNCTOR

VEC : Nat -> SET => SET
VEC n = record 
    { F-Obj = λ Set → Vec Set n
    ; F-map = {!   !} 
    ; F-map-id~> = {!   !} 
    ; F-map->~> = {!   !}
    }

{-+}
VTAKE : Set -> NAT->= => SET
VTAKE X = {!!}
{+-}

{-+}
ADD : Nat -> NAT->= => NAT->=
ADD d = {!!}
{+-}

{-+}
CATEGORY : Category
CATEGORY = {!!}
{+-}