{-# OPTIONS --allow-unsolved-metas #-}
------------------------------------------------------------------------------
------------------------------------------------------------------------------
-- CS410 2017/18 Exercise 1  VECTORS AND FRIENDS (worth 25%)
------------------------------------------------------------------------------
------------------------------------------------------------------------------

-- NOTE (19/9/17) This file is currently incomplete: more will arrive on
-- GitHub.

-- MARK SCHEME (transcribed from paper): the (m) numbers add up to slightly
-- more than 25, so should be taken as the maximum number of marks losable on
-- the exercise. In fact, I did mark it negatively, but mostly because it was
-- done so well (with Agda's help) that it was easier to find the errors.


------------------------------------------------------------------------------
-- Dependencies
------------------------------------------------------------------------------

open import CS410-Prelude


------------------------------------------------------------------------------
-- Vectors
------------------------------------------------------------------------------

data Vec (X : Set) : Nat -> Set where  -- like lists, but length-indexed
  []   :                              Vec X zero
  _,-_ : {n : Nat} -> X -> Vec X n -> Vec X (suc n)
infixr 4 _,-_   -- the "cons" operator associates to the right

-- I like to use the asymmetric ,- to remind myself that the element is to
-- the left and the rest of the list is to the right.

-- Vectors are useful when there are important length-related safety
-- properties.


------------------------------------------------------------------------------
-- Heads and Tails
------------------------------------------------------------------------------

-- We can rule out nasty head and tail errors by insisting on nonemptiness!

--??--1.1-(2)-----------------------------------------------------------------

vHead : {X : Set}{n : Nat} -> Vec X (suc n) -> X
vHead (x ,- xs) = x

vTail : {X : Set}{n : Nat} -> Vec X (suc n) -> Vec X n
vTail (x ,- xs) = xs

vHeadTailFact :  {X : Set}{n : Nat}(xs : Vec X (suc n)) ->
                 (vHead xs ,- vTail xs) == xs
vHeadTailFact (x ,- xs) = refl (vHead (x ,- xs) ,- vTail (x ,- xs))                 

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Concatenation and its Inverse
------------------------------------------------------------------------------

--??--1.2-(2)-----------------------------------------------------------------

_+V_ : {X : Set}{m n : Nat} -> Vec X m -> Vec X n -> Vec X (m +N n)
[] +V ys = ys
(x ,- xs) +V ys = x ,- xs +V ys
infixr 4 _+V_

vChop : {X : Set}(m : Nat){n : Nat} -> Vec X (m +N n) -> Vec X m * Vec X n
vChop zero xs = [] , xs
vChop (suc m) (x ,- xs) with vChop m xs 
... | xm , xn = (x ,- xm) , xn

vChopAppendFact : {X : Set}{m n : Nat}(xs : Vec X m)(ys : Vec X n) ->
                  vChop m (xs +V ys) == (xs , ys)
vChopAppendFact {X} {zero} {n} [] ys = refl $ vChop zero ys
vChopAppendFact {X} {suc m} {n} (x ,- xs) ys with vChop m (xs +V ys) | vChopAppendFact xs ys
... | xm , yn | refl .(xs , ys) = refl $ (x ,- xs) , ys


------------------------------------------------------------------------------
-- Map, take I
------------------------------------------------------------------------------

-- Implement the higher-order function that takes an operation on
-- elements and does it to each element of a vector. Use recursion
-- on the vector.
-- Note that the type tells you the size remains the same.

-- Show that if the elementwise function "does nothing", neither does
-- its vMap. "map of identity is identity"

-- Show that two vMaps in a row can be collapsed to just one, or
-- "composition of maps is map of compositions"

--??--1.3-(2)-----------------------------------------------------------------

vMap : {X Y : Set} -> (X -> Y) -> {n : Nat} -> Vec X n -> Vec Y n
vMap f [] = []
vMap f (x ,- xs) = f x ,- vMap f xs

vMapIdFact : {X : Set}{f : X -> X}(feq : (x : X) -> f x == x) ->
             {n : Nat}(xs : Vec X n) -> vMap f xs == xs
vMapIdFact feq [] = refl []
vMapIdFact feq (x ,- xs) rewrite vMapIdFact feq xs | feq x = refl (x ,- xs)

-- vMapIdFact {X} {f} feq (x ,- xs) with vMap f xs | vMapIdFact feq xs | f x | feq x
-- ... | fxs | refl .xs | fx | refl .x = refl (x ,- xs)

vMapCpFact : {X Y Z : Set}{f : Y -> Z}{g : X -> Y}{h : X -> Z}
               (heq : (x : X) -> f (g x) == h x) ->
             {n : Nat}(xs : Vec X n) ->
               vMap f (vMap g xs) == vMap h xs
vMapCpFact heq [] = refl []
vMapCpFact  {X} {Y} {Z} {f} {g} {h} heq (x ,- xs) rewrite heq x | vMapCpFact {X} {Y} {Z} {f} {g} {h} heq xs = refl (h x ,- vMap h xs)

-- vMapCpFact {X} {Y} {Z} {f} {g} {h} heq (x ,- xs) with f (g x) | h x | heq x
--     | vMap f (vMap g xs) | vMap h xs | vMapCpFact {X} {Y} {Z} {f} {g} {h} heq xs
-- ... | fgx | hx | refl .fgx | mapfgxs | maphxs | refl .mapfgxs = refl $ fgx ,- mapfgxs


--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- vMap and +V
------------------------------------------------------------------------------

-- Show that if you've got two vectors of Xs and a function from X to Y,
-- and you want to concatenate and map, it doesn't matter which you do
-- first.

--??--1.4-(1)-----------------------------------------------------------------

vMap+VFact : {X Y : Set}(f : X -> Y) ->
             {m n : Nat}(xs : Vec X m)(xs' : Vec X n) ->
             vMap f (xs +V xs') == (vMap f xs +V vMap f xs')
vMap+VFact f [] xs' = refl $ vMap f  xs'
vMap+VFact {X} {Y} f (x ,- xs) xs' rewrite vMap+VFact {X} {Y} f xs xs' = refl (f x ,- vMap f xs +V vMap f xs')

-- vMap+VFact f (x ,- xs) xs' with vMap f $ xs +V xs' | vMap f xs +V vMap f xs' | vMap+VFact f xs xs'
-- ... | vm | mv | refl .vm = refl $ f x ,- vm

--??--------------------------------------------------------------------------

-- Think about what you could prove, relating vMap with vHead, vTail, vChop...
-- Now google "Philip Wadler" "Theorems for Free"


------------------------------------------------------------------------------
-- Applicative Structure (giving mapping and zipping cheaply)
------------------------------------------------------------------------------

--??--1.5-(2)-----------------------------------------------------------------

-- HINT: you will need to override the default invisibility of n to do this.
vPure : {X : Set} -> X -> {n : Nat} -> Vec X n
vPure x {zero} = []
vPure x {suc n} = x ,- vPure x

_$V_ : {X Y : Set}{n : Nat} -> Vec (X -> Y) n -> Vec X n -> Vec Y n
[] $V xs = []
f ,- fs $V x ,- xs = f x ,- (fs $V xs)
infixl 3 _$V_  -- "Application associates to the left,
               --  rather as we all did in the sixties." (Roger Hindley)

-- Pattern matching and recursion are forbidden for the next two tasks.

-- implement vMap again, but as a one-liner
vec : {X Y : Set} -> (X -> Y) -> {n : Nat} -> Vec X n -> Vec Y n
vec f xs = vPure f $V xs

-- implement the operation which pairs up corresponding elements
vZip : {X Y : Set}{n : Nat} -> Vec X n -> Vec Y n -> Vec (X * Y) n
vZip xs ys = vec _,_ xs $V ys

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Applicative Laws
------------------------------------------------------------------------------

-- According to "Applicative programming with effects" by
--   Conor McBride and Ross Paterson
-- some laws should hold for applicative functors.
-- Check that this is the case.

--??--1.6-(2)-----------------------------------------------------------------

vIdentity : {X : Set}{f : X -> X}(feq : (x : X) -> f x == x) ->
            {n : Nat}(xs : Vec X n) -> (vPure f $V xs) == xs
vIdentity feq [] = refl []
vIdentity feq (x ,- xs) rewrite vIdentity feq xs | feq x = refl (x ,- xs)

vHomomorphism : {X Y : Set}(f : X -> Y)(x : X) ->
                {n : Nat} -> (vPure f $V vPure x) == vPure (f x) {n}
vHomomorphism f x {zero} = refl []
vHomomorphism f x {suc n} rewrite vHomomorphism f x {n} = refl (f x ,- vPure (f x))

vInterchange : {X Y : Set}{n : Nat}(fs : Vec (X -> Y) n)(x : X) ->
               (fs $V vPure x) == (vPure (_$ x) $V fs)
vInterchange [] x = refl []
vInterchange (f ,- fs) x rewrite vInterchange fs x = refl (f x ,- (vPure (λ section → section x) $V fs))

vComposition : {X Y Z : Set}{n : Nat}
               (fs : Vec (Y -> Z) n)(gs : Vec (X -> Y) n)(xs : Vec X n) ->
               (vPure _<<_ $V fs $V gs $V xs) == (fs $V (gs $V xs))
vComposition [] [] [] = refl []
vComposition (f ,- fs) (g ,- gs) (x ,- xs) rewrite vComposition fs gs xs = refl (f (g x) ,- (fs $V (gs $V xs)))

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Order-Preserving Embeddings (also known in the business as "thinnings")
------------------------------------------------------------------------------

-- What have these to do with Pascal's Triangle?

data _<=_ : Nat -> Nat -> Set where
  oz :                          zero  <= zero
  os : {n m : Nat} -> n <= m -> suc n <= suc m
  o' : {n m : Nat} -> n <= m ->     n <= suc m

-- Find all the values in each of the following <= types.
-- This is a good opportunity to learn to use C-c C-a with the -l option
--   (a.k.a. "google the type" without "I feel lucky")
-- The -s n option also helps.

--??--1.7-(1)-----------------------------------------------------------------

all0<=4 : Vec (0 <= 4) 1
all0<=4 = o' (o' (o' (o' oz))) ,- []

all1<=4 : Vec (1 <= 4) 2
all1<=4 = o' (o' (o' (os oz))) ,- o' (o' (os (o' oz))) ,- []

all2<=4 : Vec (2 <= 4) 1
all2<=4 = o' (os (o' (os oz))) ,- []
       
all3<=4 : Vec (3 <= 4) 1
all3<=4 = os (os (o' (os oz))) ,- []

all4<=4 : Vec (4 <= 4) 1
all4<=4 = os (os (os (os oz))) ,- []

-- Prove the following. A massive case analysis "rant" is fine.

no5<=4 : 5 <= 4 -> Zero
no5<=4 (os (os (os (os ()))))
no5<=4 (os (os (os (o' ()))))
no5<=4 (os (os (o' (os ()))))
no5<=4 (os (os (o' (o' ()))))
no5<=4 (os (o' (os (os ()))))
no5<=4 (os (o' (os (o' ()))))
no5<=4 (os (o' (o' (os ()))))
no5<=4 (os (o' (o' (o' ()))))
no5<=4 (o' (os (os (os ()))))
no5<=4 (o' (os (os (o' ()))))
no5<=4 (o' (os (o' (os ()))))
no5<=4 (o' (o' (os (o' ()))))
no5<=4 (o' (o' (o' (os ()))))
no5<=4 (o' (o' (o' (o' ()))))

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Order-Preserving Embeddings Select From Vectors
------------------------------------------------------------------------------

-- Use n <= m to encode the choice of n elements from an m-Vector.
-- The os constructor tells you to take the next element of the vector;
-- the o' constructor tells you to omit the next element of the vector.

--??--1.8-(2)-----------------------------------------------------------------

_<?=_ : {X : Set}{n m : Nat} -> n <= m -> Vec X m
                     -> Vec X n
oz <?= [] = []
os th <?= (x ,- xs) = x ,- th <?= xs
o' th <?= (_ ,- xs) = th <?= xs

-- it shouldn't matter whether you map then select or select then map

vMap<?=Fact : {X Y : Set}(f : X -> Y)
              {n m : Nat}(th : n <= m)(xs : Vec X m) ->
              vMap f (th <?= xs) == (th <?= vMap f xs)
vMap<?=Fact f oz [] = refl []
vMap<?=Fact f (os th) (x ,- xs) rewrite vMap<?=Fact f th xs = refl (f x ,- (th <?= vMap f xs))
vMap<?=Fact f (o' th) (_ ,- xs) rewrite vMap<?=Fact f th xs = refl (th <?= vMap f xs)

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Our Favourite Thinnings
------------------------------------------------------------------------------

-- Construct the identity thinning and the empty thinning.

--??--1.9-(1)-----------------------------------------------------------------

oi : {n : Nat} -> n <= n
oi {zero} = oz
oi {suc n} = os oi

oe : {n : Nat} -> 0 <= n
oe {zero} = oz
oe {suc n} = o' oe

--??--------------------------------------------------------------------------


-- Show that all empty thinnings are equal to yours.

--??--1.10-(1)----------------------------------------------------------------

oeUnique : {n : Nat}(th : 0 <= n) -> th == oe
oeUnique oz = refl oz
oeUnique (o' i) rewrite oeUnique i = refl (o' oe)

--??--------------------------------------------------------------------------


-- Show that there are no thinnings of form big <= small  (TRICKY)
-- Then show that all the identity thinnings are equal to yours.
-- Note that you can try the second even if you haven't finished the first.
-- HINT: you WILL need to expose the invisible numbers.
-- HINT: check CS410-Prelude for a reminder of >=

--??--1.11-(3)----------------------------------------------------------------

-- induction lemma for oTooBig
-- https://discord.com/channels/954089080197611551/966602283351703562/1316883677183086683
-- p for predecessor
op : {n m : Nat} -> suc n <= suc m -> n <= m
op (os sn<=sm) = sn<=sm
op {n} {suc m} (o' sn<=sm) = o' (op sn<=sm)

-- oInduction : {n m : Nat} -> suc n <= suc m -> n <= m
-- oInduction {zero} {zero} sn<=sm = oz
-- oInduction {zero} {suc m} (os sn<=sm) = sn<=sm
-- oInduction {zero} {suc m} (o' sn<=sm) = o' (oInduction sn<=sm)
-- oInduction {suc n} {zero} (os sn<=sm) = sn<=sm
-- oInduction {suc n} {zero} (o' ())
-- oInduction {suc n} {suc m} (os sn<=sm) = sn<=sm
-- oInduction {suc n} {suc m} (o' sn<=sm) = o' (oInduction sn<=sm)

oTooBig : {n m : Nat} -> n >= m -> suc n <= m -> Zero
oTooBig {zero} {zero} <> ()
oTooBig {zero} {suc m} n>=m th = n>=m
oTooBig {suc n} {suc m} n>=m th with op th
... | l = oTooBig n>=m l

oiUnique : {n : Nat}(th : n <= n) -> th == oi
oiUnique {zero} oz = refl oz
oiUnique {suc n} (os th) rewrite oiUnique th = refl (os oi)
oiUnique {suc n} (o' th) with oTooBig (refl->= n) th
... | ()

--??--------------------------------------------------------------------------


-- Show that the identity thinning selects the whole vector

--??--1.12-(1)----------------------------------------------------------------

id-<?= : {X : Set}{n : Nat}(xs : Vec X n) -> (oi <?= xs) == xs
id-<?= [] = refl []
id-<?= (x ,- xs) rewrite id-<?= xs = refl (x ,- xs)

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Composition of Thinnings
------------------------------------------------------------------------------

-- Define the composition of thinnings and show that selecting by a
-- composite thinning is like selecting then selecting again.
-- A small bonus applies to minimizing the length of the proof.
-- To collect the bonus, you will need to think carefully about
-- how to make the composition as *lazy* as possible.

--??--1.13-(3)----------------------------------------------------------------

_o>>_ : {p n m : Nat} -> p <= n -> n <= m -> p <= m
oz o>> th' = th'
os th o>> os th' = os (th o>> th')
os th o>> o' th' = o' (os th o>> th')
o' th o>> os th' = o' (th o>> th')
o' th o>> o' th' = o' (o' th o>> th')

cp-<?= : {p n m : Nat}(th : p <= n)(th' : n <= m) ->
         {X : Set}(xs : Vec X m) ->
         ((th o>> th') <?= xs) == (th <?= (th' <?= xs))
cp-<?= oz th' xs with th' <?= xs
... | [] = refl []
cp-<?= (os th) (os th') (x ,- xs) rewrite cp-<?= th th' xs = refl (x ,- (th <?= (th' <?= xs)))
cp-<?= (os th) (o' th') (x ,- xs) rewrite cp-<?= (os th) th' xs = refl (os th <?= (th' <?= xs))
cp-<?= (o' th) (os th') (x ,- xs) rewrite cp-<?= th th' xs = refl (th <?= (th' <?= xs))
cp-<?= (o' th) (o' th') (x ,- xs) rewrite cp-<?=  (o' th) th' xs = refl (o' th <?= (th' <?= xs))

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Thinning Dominoes
------------------------------------------------------------------------------

--??--1.14-(3)----------------------------------------------------------------

idThen-o>> : {n m : Nat}(th : n <= m) -> (oi o>> th) == th
idThen-o>> oz = refl oz
idThen-o>> (os th) rewrite idThen-o>> th = refl (os th)
idThen-o>> {zero} {m} (o' th) = refl (oi o>> o' th)
idThen-o>> {suc n} {m} (o' th) rewrite idThen-o>> th = refl (o' th)

idAfter-o>> : {n m : Nat}(th : n <= m) -> (th o>> oi) == th
idAfter-o>> oz = refl oz
idAfter-o>> (os th) rewrite idAfter-o>> th = refl (os th)
idAfter-o>> (o' th) rewrite idAfter-o>> th = refl (o' th)

assoc-o>> : {q p n m : Nat}(th0 : q <= p)(th1 : p <= n)(th2 : n <= m) ->
            ((th0 o>> th1) o>> th2) == (th0 o>> (th1 o>> th2))
assoc-o>> oz th1 th2 = refl ((oz o>> th1) o>> th2)
assoc-o>> (os th0) th1 th2 = {!   !}
assoc-o>> (o' th0) th1 th2 = {!   !}

--??--------------------------------------------------------------------------


------------------------------------------------------------------------------
-- Vectors as Arrays
------------------------------------------------------------------------------

-- We can use 1 <= n as the type of bounded indices into a vector and do
-- a kind of "array projection". First we select a 1-element vector from
-- the n-element vector, then we take its head to get the element out.

vProject : {n : Nat}{X : Set} -> Vec X n -> 1 <= n -> X
vProject xs i = vHead (i <?= xs)

-- Your (TRICKY) mission is to reverse the process, tabulating a function
-- from indices as a vector. Then show that these operations are inverses.

--??--1.15-(3)----------------------------------------------------------------

-- HINT: composition of functions
vTabulate : {n : Nat}{X : Set} -> (1 <= n -> X) -> Vec X n
vTabulate {n} f = {!  !}

-- This should be easy if vTabulate is correct.
vTabulateProjections : {n : Nat}{X : Set}(xs : Vec X n) ->
                       vTabulate (vProject xs) == xs
vTabulateProjections xs = {!  !}

-- HINT: oeUnique
vProjectFromTable : {n : Nat}{X : Set}(f : 1 <= n -> X)(i : 1 <= n) ->
                    vProject (vTabulate f) i == f i 
vProjectFromTable f i = {!  !}       
                                                              
--??--------------------------------------------------------------------------(x ,- xxs