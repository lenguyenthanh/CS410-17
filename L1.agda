-- https://github.com/pigworker/CS410-17/blob/master/lectures/Lec1.agda

module L1 where

    data Zero : Set where
        -- to give a value in a data, choose one constructor
        -- there are no constructors
        -- so that's impossible

    record One : Set where
        constructor <>
        -- to give a value in a record type, fill all its fields
        -- there are no fields
        -- so that's trivial
        --   (can we have a constructor, for convenience?)

    {-# COMPILE GHC One = data () (()) #-}

    data _+_ (S : Set)(T : Set) : Set where -- "where" wants an indented block
        -- to offer a choice of constructors, list them with their types
        inl : S -> S + T     -- constructors can pack up stuff
        inr : T -> S + T
        -- in Haskell, this was called "Either S T"

    record Sg (S : Set)(T : S -> Set) : Set where  -- Sg is short for "Sigma"
        constructor _,_
        field
            fst : S  
            snd : T fst

    _*_ : (S : Set)(T : Set) -> Set
    S * T = Sg S \ _ -> T

    comm-* : {A B : Set} -> A * B -> B * A
    comm-* (a , b) = b , a

    assocLR-+ : {A B C : Set} -> (A + B) + C -> A + (B + C)
    assocLR-+ (inl (inl a)) = inl a
    assocLR-+ (inl (inr b)) = inr (inl b)
    assocLR-+ (inr c) = inr (inr c)

    naughtE : {X : Set} -> Zero -> X
    naughtE ()

    _$*_ : {A A' B B' : Set} -> (A -> A') -> (B -> B') -> A * B -> A' * B'
    (f $* g) (a , b) = f a , g b


    _$+_ : {A A' B B' : Set} -> (A -> A') -> (B -> B') -> A + B -> A' + B'
    (f $+ g) (inl a) = inl (f a)
    (f $+ g) (inr b) = inr (g b)

    combinatorK : {A E : Set} -> A -> E -> A
    combinatorK = λ a _ -> a
    -- combinatorK a e = a

    combinatorS : { S T E : Set } -> (E -> S -> T) -> (E -> S) -> E -> T
    combinatorS = λ est es e → est e (es e)
    -- combinatorS f g = λ e → f e (g e)

    -- underscore and Zero for helping Agda realize the type in runtime
    id : { X : Set } -> X -> X
    -- id x = x
    id = combinatorS combinatorK (combinatorK {_} {Zero})

    -- diagrammatic composition: f >> g is "f then g"
    _>>_ : {X Y Z : Set} -> (X -> Y) -> (Y -> Z) -> (X -> Z)
    (f >> g) x = g (f x)
    -- f >> g = \ x -> g (f x)

    -- infix application
    _$_ : {S : Set}{T : S -> Set}(f : (x : S) -> T x)(s : S) -> T s
    f $ x = f x
    infixl 2 _$_

    ------------------------------------------------------------------------------
    -- from logic to data
    ------------------------------------------------------------------------------

    data Nat : Set where
        zero : Nat
        suc : Nat -> Nat

    {-# BUILTIN NATURAL Nat #-}
    --  ^^^^^^^^^^^^^^^^^^^       this pragma lets us use decimal notation

    _+N_ : Nat -> Nat -> Nat
    zero +N y = y
    suc x +N y = suc (x +N y)

    four : Nat
    four = 2 +N 2
    {-(-}


    ------------------------------------------------------------------------------
    -- and back to logic
    ------------------------------------------------------------------------------

    data _==_ {X : Set} : X -> X -> Set where
        refl : (x : X) -> x == x           -- the relation that's "only reflexive"

    {-# BUILTIN EQUALITY _==_ #-}  -- we'll see what that's for, later

    see4 : (2 +N 2) == 4
    see4 = refl 4

    _=$=_ : {X Y : Set}{f f' : X -> Y}{x x' : X} ->
        f == f' -> x == x' -> f x == f' x'
    refl f =$= refl x = refl (f x)  

    zero-+N : (n : Nat) -> (zero +N n) == n
    zero-+N n = refl n

    +N-zero : (n : Nat) -> (n +N zero) == n
    +N-zero zero = refl zero 
    +N-zero (suc n) = refl suc =$= +N-zero n

    assocLR-+N : (x y z : Nat) -> ((x +N y) +N z) == (x +N (y +N z))
    assocLR-+N zero y z = refl (y +N z)
    assocLR-+N (suc x) y z rewrite assocLR-+N x y z = refl (suc (x +N (y +N z)))
    -- assocLR-+N (suc x) y z = refl suc =$= assocLR-+N x y z

    _>=_ : Nat -> Nat -> Set
    x >= zero = One
    zero >= suc x = Zero
    suc x >= suc y = x >= y

    refl->= : (n : Nat) -> n >= n
    refl->= zero = <>
    refl->= (suc n) = refl->= n

    nzero : (n : Nat) -> n >= zero
    nzero zero = <> 
    nzero (suc n) = <>

    -- I have to use nzero here as agda cannot derive it automatically
    -- One !=< x >= zero
    -- when checking that the expression <> has type x >= zero
    -- mm, I don't have to anymore
    trans->= : (x y z : Nat) -> x >= y -> y >= z -> x >=  z
    trans->= x y zero x>=y y>=z = <>
    trans->= (suc x) (suc y) (suc z) x>=y y>=z = trans->= x y z x>=y y>=z

    possible : 2 >= 1
    possible = <>

    -- No solution found
    -- impossible : 1 >= 2
    -- impossible = ?

    ------------------------------------------------------------------------------
    -- construction by proof
    ------------------------------------------------------------------------------

    {-(-}

    difference : (m n : Nat) -> m >= n -> Sg Nat \ d -> m == (n +N d)
    difference m zero m>=n = m , refl m
    difference (suc m) (suc n) m>=n with difference m n m>=n 
    ... | d , q = d , (refl suc =$= q)

    -- difference m zero p = m , refl m
    -- difference (suc m) (suc n) p with difference m n p
    -- ... | d , q = d , (refl suc =$= q)

    tryMe      = difference 42 37 _  
    -- don'tTryMe = difference 37 42 {! !}