module L2 where

open import L1

------------------------------------------------------------------------------
-- Vectors  -- the star of exercise 1
------------------------------------------------------------------------------

data Vec (X : Set) : Nat -> Set where  -- like lists, but length-indexed
  []   :                              Vec X zero
  _,-_ : {n : Nat} -> X -> Vec X n -> Vec X (suc n)
infixr 4 _,-_   -- the "cons" operator associates to the right


------------------------------------------------------------------------------
-- Taking a Prefix of a Vector
------------------------------------------------------------------------------

{--}
vTake : (m n : Nat) -> m >= n -> {X : Set} -> Vec X m -> Vec X n
vTake m zero m>=n xs = []
vTake (suc m) (suc n) m>=n (x ,- xs) = x ,- vTake m n m>=n xs
{--}

------------------------------------------------------------------------------
-- Things to Prove
------------------------------------------------------------------------------

vTakeIdFact : (n : Nat){X : Set}(xs : Vec X n) ->
              vTake n n (refl->= n) xs == xs
vTakeIdFact zero [] = refl []
vTakeIdFact (suc n) (x ,- xs) with vTake n n (refl->= n) xs | vTakeIdFact n xs
... | z | refl .xs = refl (x ,- xs)
-- vTakeIdFact (suc n) (x ,- xs) rewrite vTakeIdFact n xs = refl (x ,- xs)
-- vTakeIdFact (suc n) (x ,- xs) = refl (x ,-_) =$= vTakeIdFact n xs

{--}
vTakeCpFact : (m n p : Nat)(m>=n : m >= n)(n>=p : n >= p)
              {X : Set}(xs : Vec X m) ->
              vTake m p (trans->= m n p m>=n n>=p) xs ==
                vTake n p n>=p (vTake m n m>=n xs)
{- hit p first: why? -}                
vTakeCpFact m n zero m>=n n>=p xs = refl []
vTakeCpFact (suc m) (suc n) (suc p) m>=n n>=p (x ,- xs) = refl (x ,-_) =$= vTakeCpFact m n p m>=n n>=p xs
{--}

------------------------------------------------------------------------------
-- Splittings (which bear some relationship to <= from ex1)
------------------------------------------------------------------------------

data _<[_]>_ : Nat -> Nat -> Nat -> Set where
  zzz : zero <[ zero ]> zero
  lll : {l m r : Nat} ->      l <[     m ]> r
                      ->  suc l <[ suc m ]> r
  rrr : {l m r : Nat} ->      l <[     m ]>     r
                      ->      l <[ suc m ]> suc r

_>[_]<_ : {X : Set}{l m r : Nat} ->
          Vec X l -> l <[ m ]> r -> Vec X r ->
          Vec X m
xl >[ rrr nnn ]< (x ,- xr) = x ,- (xl >[ nnn ]< xr)
(x ,- xl) >[ lll nnn ]< xr = x ,- (xl >[ nnn ]< xr)
[] >[ zzz ]< [] = []

data FindSplit {X : Set}{l m r : Nat}(nnn : l <[ m ]> r)
     : (xs : Vec X m) -> Set where
  splitBits : (xl : Vec X l)(xr : Vec X r) -> FindSplit nnn (xl >[ nnn ]< xr)

findSplit : {X : Set}{l m r : Nat}(nnn : l <[ m ]> r)(xs : Vec X m) ->
            FindSplit nnn xs
findSplit (rrr nnn) (x ,- xs) with findSplit nnn xs
... | splitBits xl xr = splitBits xl (x ,- xr)
findSplit (lll nnn) (x ,- xs) with findSplit nnn xs
... | splitBits xl xr = splitBits (x ,- xl) xr
findSplit zzz [] = splitBits [] []

------------------------------------------------------------------------------
-- what I should remember to say
------------------------------------------------------------------------------

-- What's the difference between m>=n and m >= n ?
   {- m>=n (without spaces) is just an identifier; it could be anything,
      but it has been chosen to be suggestive of its *type* which is
      m >= n (with spaces) which is the proposition that m is at least n.
      By "proposition", I mean "type with at most one inhabitant", where
      we care more about whether there is an inhabitant or not than which
      one (because there's never a choice). Finished code does not show
      us the types of its components, and that's not always a good thing.
      Here, by picking nice names, we get something of an aide-memoire. -}

-- What does (x ,-_) mean?
   {- It's a "left section". Right sections (_,- xs) also exist sometimes.
      Why only sometimes? -}

-- "Why is it stuck?"
   {- Proof by induction isn't just flailing about, you know? The trick is
      to pick the case analysis that provokes the "stuck" programs to do a
      step of computation. Then the same reasoning that justifies the
      termination of the program will justify the induction in a proof
      about it. -}
      