{- This file is an automatically postprocessed compilable version of BrutalDepTypes module.

   See %src% for a Literate Agda version.
   See http://oxij.org/note/BrutalDepTypes/ for a rendered web article version.
   See %htmlsrc% for a browsable source code.

  Author : Jan Malakhovski
  Date   : June 2013
-}

module OXIj.BrutalDepTypes where


--module Level where
--  -- Universe levels
--  postulate Level : Set
--  postulate lzero : Level
--  postulate lsucc : Level → Level
--  -- input for ⊔ is \sqcup
--  postulate _⊔_   : Level → Level → Level
--
--  infixl 5 _⊔_

  -- Make them work
--  {-# BUILTIN LEVEL     Level #-}
--  {-# BUILTIN LEVELZERO lzero #-}
--  {-# BUILTIN LEVELSUC  lsucc #-}
--  {-# BUILTIN LEVELMAX  _⊔_   #-}

--open Level public
open import Agda.Primitive

module Function where
  -- Dependent application
  infixl 0 _$_
  _$_ : ∀ {α β}
      → {A : Set α} {B : A → Set β}
      → (f : (x : A) → B x)
      → ((x : A) → B x)
  f $ x = f x

  -- Simple application
  infixl 0 _$′_
  _$′_ : ∀ {α β}
      → {A : Set α} {B : Set β}
      → (A → B) → (A → B)
  f $′ x = f $ x

  -- input for ∘ is \o
  -- Dependent composition
  _∘_ : ∀ {α β γ}
      → {A : Set α} {B : A → Set β} {C : {x : A} → B x → Set γ}
      → (f : {x : A} → (y : B x) → C y)
      → (g : (x : A) → B x)
      → ((x : A) → C (g x))
  f ∘ g = λ x → f (g x)

  -- Simple composition
  _∘′_ : ∀ {α β γ}
      → {A : Set α} {B : Set β} {C : Set γ}
      → (B → C) → (A → B) → (A → C)
  f ∘′ g = f ∘ g

  -- Flip
  flip : ∀ {α β γ}
       → {A : Set α} {B : Set β} {C : A → B → Set γ}
       → ((x : A) → (y : B) → C x y)
       → ((y : B) → (x : A) → C x y)
  flip f x y = f y x

  -- Identity
  id : ∀ {α} {A : Set α} → A → A
  id x = x

  -- Constant function
  const : ∀ {α β}
       → {A : Set α} {B : Set β}
       → (A → B → A)
  const x y = x

open Function public

module Logic where
  -- input for ⊥ is \bot
  -- False proposition
  data ⊥ : Set where

  -- input for ⊤ is \top
  -- True proposition
  record ⊤ : Set where

  -- ⊥ implies anything at any universe level
  ⊥-elim : ∀ {α} {A : Set α} → ⊥ → A
  ⊥-elim ()

  -- input for ¬ is \lnot
  ¬ : ∀ {α} → Set α → Set α
  ¬ P = P → ⊥


  private
   module DummyAB {α β} {A : Set α} {B : Set β} where
    contradiction : A → ¬ A → B
    contradiction a ¬a = ⊥-elim (¬a a)

    contraposition : (A → B) → (¬ B → ¬ A)
    contraposition = flip _∘′_

    contraposition¬ : (A → ¬ B) → (B → ¬ A)
    contraposition¬ = flip

  open DummyAB public

  private
   module DummyA {α} {A : Set α} where
    →¬² : A → ¬ (¬ A)
    →¬² = contradiction

    ¬³→¬ : ¬ (¬ (¬ A)) → ¬ A
    ¬³→¬ ¬³a = ¬³a ∘′ →¬²

  open DummyA public

  -- input for ∧ is \and
  infixr 6 _∧_ _,_
  record _∧_ {α β} (A : Set α) (B : Set β) : Set (α ⊔ β) where
    constructor _,_
    field
      fst : A
      snd : B

  open _∧_ public

  -- input for ∨ is \or
  data _∨_ {α β} (A : Set α) (B : Set β) : Set (α ⊔ β) where
    inl : A → A ∨ B
    inr : B → A ∨ B

  -- input for ↔ is \<->
  _↔_ : ∀ {α β} (A : Set α) (B : Set β) → Set (α ⊔ β)
  A ↔ B = (A → B) ∧ (B → A)

open Logic public

module MLTT where
  -- input for ≡ is \==
  -- Propositional equality
  infix 4 _≡_
  data _≡_ {α} {A : Set α} (x : A) : A → Set α where
    refl : x ≡ x

  _≠_ : ∀ {α} {A : Set α} (x : A) → A → Set α
  x ≠ y = ¬ (x ≡ y)

  -- input for Σ is \Sigma
  -- Dependent pair
  infixr 6 _,_
  record Σ {α β} (A : Set α) (B : A → Set β) : Set (α ⊔ β) where
    constructor _,_
    field
      projl : A
      projr : B projl

  open Σ public

  -- Make rewrite syntax work
  {-# BUILTIN EQUALITY _≡_ #-}
  {-# BUILTIN REFL    refl #-}

  -- input for × is \x
  _×_ : ∀ {α β} (A : Set α) (B : Set β) → Set (α ⊔ β)
  A × B = Σ A (λ _ → B)

  ×↔∧ : ∀ {α β} {A : Set α} {B : Set β} → (A × B) ↔ (A ∧ B)
  ×↔∧ = (λ z → projl z , projr z) , (λ z → fst z , snd z)

  module ≡-Prop where
   private
    module DummyA {α} {A : Set α} where
      -- _≡_ is symmetric
      sym : {x y : A} → x ≡ y → y ≡ x
      sym refl = refl

      -- _≡_ is transitive
      trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
      trans refl refl = refl

      -- _≡_ is substitutive
      subst : ∀ {γ} (P : A → Set γ) {x y} → x ≡ y → P x → P y
      subst P refl p = p

    private
     module DummyAB {α β} {A : Set α} {B : Set β} where
      -- _≡_ is congruent
      cong : ∀ (f : A → B) {x y} → x ≡ y → f x ≡ f y
      cong f refl = refl

      subst₂ : ∀ {ℓ} {P : A → B → Set ℓ} {x y u v} → x ≡ y → u ≡ v → P x u → P y v
      subst₂ refl refl p = p

    private
     module DummyABC {α β γ} {A : Set α} {B : Set β} {C : Set γ} where
      cong₂ : ∀ (f : A → B → C) {x y u v} → x ≡ y → u ≡ v → f x u ≡ f y v
      cong₂ f refl refl = refl

    open DummyA public
    open DummyAB public
    open DummyABC public

open MLTT public

module Decidable where

  data Dec {α} (A : Set α) : Set α where
    yes : ( a :   A) → Dec A
    no  : (¬a : ¬ A) → Dec A


  data Di {α β} (A : Set α) (B : Set β) : Set (α ⊔ β) where
    diyes : ( a :   A) (¬b : ¬ B) → Di A B
    dino  : (¬a : ¬ A) ( b :   B) → Di A B

  data Tri {α β γ} (A : Set α) (B : Set β) (C : Set γ) : Set (α ⊔ (β ⊔ γ)) where
    tri< : ( a :   A) (¬b : ¬ B) (¬c : ¬ C) → Tri A B C
    tri≈ : (¬a : ¬ A) ( b :   B) (¬c : ¬ C) → Tri A B C
    tri> : (¬a : ¬ A) (¬b : ¬ B) ( c :   C) → Tri A B C

open Decidable public

module Data-ℕ where
  -- Natural numbers (positive integers)
  data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

  module ℕ-Rel where
    infix 4 _≤_ _<_ _>_

    data _≤_ : ℕ → ℕ → Set where
      z≤n : ∀ {n}           → zero ≤ n
      s≤s : ∀ {n m} → n ≤ m → succ n ≤ succ m

    _<_ : ℕ → ℕ → Set
    n < m = succ n ≤ m

    _>_ : ℕ → ℕ → Set
    n > m = m < n

    ≤-unsucc : ∀ {n m} → succ n ≤ succ m → n ≤ m
    ≤-unsucc (s≤s a) = a

    <-¬refl : ∀ n → ¬ (n < n)
    <-¬refl zero ()
    <-¬refl (succ n) (s≤s p) = <-¬refl n p

    ≡→≤ : ∀ {n m} → n ≡ m → n ≤ m
    ≡→≤ {zero}   refl = z≤n
    ≡→≤ {succ n} refl = s≤s (≡→≤ {n} refl) -- Note this

    ≡→¬< : ∀ {n m} → n ≡ m → ¬ (n < m)
    ≡→¬< refl = <-¬refl _

    ≡→¬> : ∀ {n m} → n ≡ m → ¬ (n > m)
    ≡→¬> refl = <-¬refl _

    <→¬≡ : ∀ {n m} → n < m → ¬ (n ≡ m)
    <→¬≡ = contraposition¬ ≡→¬<

    >→¬≡ : ∀ {n m} → n > m → ¬ (n ≡ m)
    >→¬≡ = contraposition¬ ≡→¬>

    <→¬> : ∀ {n m} → n < m → ¬ (n > m)
    <→¬> {zero} (s≤s z≤n) ()
    <→¬> {succ n} (s≤s p<) p> = <→¬> p< (≤-unsucc p>)

    >→¬< : ∀ {n m} → n > m → ¬ (n < m)
    >→¬< = contraposition¬ <→¬>

  module ℕ-Op where
    open ≡-Prop

    pred : ℕ → ℕ
    pred zero = zero
    pred (succ n) = n

    infixl 6 _+_
    _+_ : ℕ → ℕ → ℕ
    zero   + n = n
    succ n + m = succ (n + m)

    infixl 6 _-_
    _-_ : ℕ → ℕ → ℕ
    zero   - n      = zero
    n      - zero   = n
    succ n - succ m = n - m

    infixr 7 _*_
    _*_ : ℕ → ℕ → ℕ
    zero   * m = zero
    succ n * m = m + (n * m)

    private
     module Dummy₀ where
      lemma-+zero : ∀ a → a + zero ≡ a
      lemma-+zero zero = refl
      lemma-+zero (succ a) rewrite lemma-+zero a = refl

      lemma-+succ : ∀ a b → succ a + b ≡ a + succ b
      lemma-+succ zero b = refl
      lemma-+succ (succ a) b rewrite lemma-+succ a b = refl

    open Dummy₀

    -- + is associative
    +-assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
    +-assoc zero b c = refl
    +-assoc (succ a) b c rewrite (+-assoc a b c) = refl

    -- + is commutative
    +-comm : ∀ a b → a + b ≡ b + a
    +-comm zero b = sym $ lemma-+zero b
    +-comm (succ a) b rewrite +-comm a b | lemma-+succ b a = refl

    -- * is distributive by +
    *+-dist : ∀ a b c → (a + b) * c ≡ a * c + b * c
    *+-dist zero b c = refl
    *+-dist (succ a) b c rewrite *+-dist a b c | +-assoc c (a * c) (b * c) = refl

    -- * is associative
    *-assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)
    *-assoc zero b c = refl
    *-assoc (succ a) b c rewrite *+-dist b (a * b) c | *-assoc a b c = refl

    private
     module Dummy₁ where
      lemma-*zero : ∀ a → a * zero ≡ zero
      lemma-*zero zero = refl
      lemma-*zero (succ a) = lemma-*zero a

      lemma-+swap : ∀ a b c → a + (b + c) ≡ b + (a + c)
      lemma-+swap a b c rewrite sym (+-assoc a b c) | +-comm a b | +-assoc b a c = refl

      lemma-*succ : ∀ a b → a + a * b ≡ a * succ b
      lemma-*succ zero b = refl
      lemma-*succ (succ a) b rewrite lemma-+swap a b (a * b) | lemma-*succ a b = refl

    open Dummy₁

    -- * is commutative
    *-comm : ∀ a b → a * b ≡ b * a
    *-comm zero b = sym $ lemma-*zero b
    *-comm (succ a) b rewrite *-comm a b | lemma-*succ b a = refl

  module ℕ-RelOp where
    open ℕ-Rel
    open ℕ-Op
    open ≡-Prop

    infix 4 _≡?_ _≤?_ _<?_

    _≡?_ : (n m : ℕ) → Dec (n ≡ m)
    zero    ≡? zero   = yes refl
    zero    ≡? succ m = no (λ ())
    succ n  ≡? zero   = no (λ ())
    succ n  ≡? succ m with n ≡? m
    succ .m ≡? succ m | yes refl = yes refl
    succ n  ≡? succ m | no ¬a    = no (¬a ∘ cong pred) -- Note this

    _≤?_ : (n m : ℕ) → Dec (n ≤ m)
    zero ≤? m = yes z≤n
    succ n ≤? zero = no (λ ())
    succ n ≤? succ m with n ≤? m
    ... | yes a = yes (s≤s a)
    ... | no ¬a = no (¬a ∘ ≤-unsucc)

    _<?_ : (n m : ℕ) → Dec (n < m)
    n <? m = succ n ≤? m

    cmp : (n m : ℕ) → Tri (n < m) (n ≡ m) (n > m)
    cmp zero zero     = tri≈ (λ ()) refl (λ ())
    cmp zero (succ m) = tri< (s≤s z≤n) (λ ()) (λ ())
    cmp (succ n) zero = tri> (λ ()) (λ ()) (s≤s z≤n)
    cmp (succ n) (succ m) with cmp n m
    cmp (succ n) (succ m) | tri< a ¬b ¬c = tri< (s≤s a) (¬b ∘ cong pred) (¬c ∘ ≤-unsucc)
    cmp (succ n) (succ m) | tri≈ ¬a b ¬c = tri≈ (¬a ∘ ≤-unsucc) (cong succ b) (¬c ∘ ≤-unsucc)
    cmp (succ n) (succ m) | tri> ¬a ¬b c = tri> (¬a ∘ ≤-unsucc) (¬b ∘ cong pred) (s≤s c)

open Data-ℕ public

module Data-List where
  -- List
  infixr 10 _∷_
  data List {α} (A : Set α) : Set α where
    []  : List A
    _∷_ : A → List A → List A

  module List-Op where
  private
   module DummyA {α} {A : Set α} where
    -- Singleton `List`
    [_] : A → List A
    [ a ] = a ∷ []

    -- Concatenation for `List`s
    infixr 10 _++_
    _++_ : List A → List A → List A
    []       ++ bs = bs
    (a ∷ as) ++ bs = a ∷ (as ++ bs)

    -- Filtering with decidable propositions
    filter : ∀ {β} {P : A → Set β} → (∀ a → Dec (P a)) → List A → List A
    filter p [] = []
    filter p (a ∷ as) with p a
    ... | yes _ = a ∷ (filter p as)
    ... | no  _ = filter p as

  open DummyA public

module Data-Vec where
  -- Vector
  infixr 5 _∷_
  data Vec {α} (A : Set α) : ℕ → Set α where
    []  : Vec A zero
    _∷_ : ∀ {n} → A → Vec A n → Vec A (succ n)

  module Vec-Op where
    open ℕ-Op

    private
     module DummyA {α} {A : Set α} where
      -- Singleton `Vec`
      [_] : A → Vec A (succ zero)
      [ a ] = a ∷ []

      -- Concatenation for `Vec`s
      infixr 5 _++_
      _++_ : ∀ {n m} → Vec A n → Vec A m → Vec A (n + m)
      []       ++ bs = bs
      (a ∷ as) ++ bs = a ∷ (as ++ bs)

      head : ∀ {n} → Vec A (succ n) → A
      head (a ∷ as) = a

      tail : ∀ {n} → Vec A (succ n) → Vec A n
      tail (a ∷ as) = as

    open DummyA public

{-
Work in progress. TODO.

I find the following definition quite amusing:

module VecLists where
  open Data-Vec

  private
   module DummyA {α} {A : Set α} where
     VecList = Σ ℕ (Vec A)
-}


module Data-Any where
  open Data-List
  open List-Op

  -- Some element of a `List` satisfies `P`
  data Any {α γ} {A : Set α} (P : A → Set γ) : List A → Set (α ⊔ γ) where
    here  : ∀ {a as} → (pa  : P a)      → Any P (a ∷ as)
    there : ∀ {a as} → (pas : Any P as) → Any P (a ∷ as)

  module Membership {α β γ} {A : Set α} {B : Set β} (P : B → A → Set γ) where
    -- input for ∈ is \in
    -- `P b a` holds for some element `a` from the `List`
    -- when P is `_≡_` this becomes the usual "is in" relation
    _∈_ : B → List A → Set (α ⊔ γ)
    b ∈ as = Any (P b) as

    -- input for ∉ is \notin
    _∉_ : B → List A → Set (α ⊔ γ)
    b ∉ as = ¬ (b ∈ as)

    -- input for ⊆ is \sub=
    _⊆_ : List A → List A → Set (α ⊔ β ⊔ γ)
    as ⊆ bs = ∀ {x} → x ∈ as → x ∈ bs

    -- input for ⊈ is \sub=n
    _⊈_ : List A → List A → Set (α ⊔ β ⊔ γ)
    as ⊈ bs = ¬ (as ⊆ bs)

    -- input for ⊇ is \sup=
    _⊆⊇_ : List A → List A → Set (α ⊔ β ⊔ γ)
    as ⊆⊇ bs = (as ⊆ bs) ∧ (bs ⊆ as)

    ⊆-refl : ∀ {as} → as ⊆ as
    ⊆-refl = id

    ⊆-trans : ∀ {as bs cs} → as ⊆ bs → bs ⊆ cs → as ⊆ cs
    ⊆-trans f g = g ∘ f

    ⊆⊇-refl : ∀ {as} → as ⊆⊇ as
    ⊆⊇-refl = id , id

    ⊆⊇-sym : ∀ {as bs} → as ⊆⊇ bs → bs ⊆⊇ as
    ⊆⊇-sym (f , g) = g , f

    ⊆⊇-trans : ∀ {as bs cs} → as ⊆⊇ bs → bs ⊆⊇ cs → as ⊆⊇ cs
    ⊆⊇-trans f g = (fst g ∘ fst f) , (snd f ∘ snd g)

    ∉[] : ∀ {b} → b ∉ []
    ∉[]()

    -- When P is `_≡_` this becomes `b ∈ [ a ] → b ≡ a`
    ∈singleton→P : ∀ {a b} → b ∈ [ a ] → P b a
    ∈singleton→P (here pba) = pba
    ∈singleton→P (there ())

    P→∈singleton : ∀ {a b} → P b a → b ∈ [ a ]
    P→∈singleton pba = here pba

    ⊆-++-left : ∀ as bs → as ⊆ (bs ++ as)
    ⊆-++-left as [] n = n
    ⊆-++-left as (b ∷ bs) n = there (⊆-++-left as bs n)

    ⊆-++-right : ∀ as bs → as ⊆ (as ++ bs)
    ⊆-++-right [] bs ()
    ⊆-++-right (x ∷ as) bs (here pa) = here pa
    ⊆-++-right (x ∷ as) bs (there n) = there (⊆-++-right as bs n)

    ⊆-++-both-left : ∀ {as bs} cs → as ⊆ bs → (cs ++ as) ⊆ (cs ++ bs)
    ⊆-++-both-left [] as⊆bs n = as⊆bs n
    ⊆-++-both-left (x ∷ cs) as⊆bs (here pa) = here pa
    ⊆-++-both-left (x ∷ cs) as⊆bs (there n) = there (⊆-++-both-left cs as⊆bs n)

    ⊆-filter : ∀ {σ} {Q : A → Set σ} → (q : ∀ x → Dec (Q x)) → (as : List A) → filter q as ⊆ as
    ⊆-filter q [] ()
    ⊆-filter q (a ∷ as) n with q a
    ⊆-filter q (a ∷ as) (here pa) | yes qa = here pa
    ⊆-filter q (a ∷ as) (there n) | yes qa = there (⊆-filter q as n)
    ⊆-filter q (a ∷ as) n         | no ¬qa = there (⊆-filter q as n)


{-
Work in progress. TODO.

I didn't have a chance to use `All` yet (and I'm too lazy to implement this module right now),
but here is the definition:

module Data-All where
  open Data-List
  -- All elements of a `List` satisfy `P`
  data All {α β} {A : Set α} (P : A → Set β) : List A → Set (α ⊔ β) where
    []∀  : All P []
    _∷∀_ : ∀ {a as} → P a → All P as → All P (a ∷ as)
-}

module Data-Bool where
  -- Booleans
  data Bool : Set where
    true false : Bool

  module Bool-Op where
    if_then_else_ : ∀ {α} {A : Set α} → Bool → A → A → A
    if true  then a else _ = a
    if false then _ else b = b

    not : Bool → Bool
    not true  = false
    not false = true

    and : Bool → Bool → Bool
    and true  x = x
    and false _ = false

    or : Bool → Bool → Bool
    or false x = x
    or true  x = true

open Data-Bool public



