module Instructions where

open import OXIj.BrutalDepTypes
open Data-List

data Type : Set

RegFileTypes = List Type
HeapTypes    = List Type

data Type where
  blk : (Γ : RegFileTypes) → Type
  _✴  : Type → Type
  any : Type


open Data-Any.Membership {A = Type} _≡_
postulate ⊆-++ : ∀ {Γ Δ Γ' Δ'} → Γ' ⊆ Γ → Δ' ⊆ Δ → (Γ' ++ Δ') ⊆ (Γ ++ Δ)

module FixedHeap (Ψ : HeapTypes) where
  ISType = RegFileTypes

  -- `Block` starts with registers Γ, all of them are
  -- considered as free registers. Some of these
  -- registers are bounded, so they are removed from
  -- list of free registers. Result list of free
  -- registers is Δ, which is obviously must be subset
  -- of Γ. `Block` also can introduce some new registers.
  data Block {Γ : RegFileTypes} : {Δ : RegFileTypes}
    → (free : Δ ⊆ Γ) → (new : RegFileTypes) → Set

  RFT = RegFileTypes

  data ControlInstr (Γ : RegFileTypes) : Set
    where
    call : (f : blk Γ ∈ Ψ)
         → ControlInstr Γ
    jmp[_] : (f : (blk Γ) ✴ ∈ Ψ)
           → ControlInstr Γ
    jmp  : (f : blk Γ ∈ Ψ)
         → ControlInstr Γ

  data Instr {free : RFT} : {free' : RFT} → free' ⊆ free → (new : RFT) → Set where
    any  : ∀ {Γ} Δ → (ss : Γ ⊆ free) → Instr ss Δ
    -- proof of concept
    --rch  : (Γ : RegFileTypes) → {τ σ : Type} → (f : Value τ → Value σ) → Instr (τ ∷ Γ) (σ ∷ Γ)

  data Block {Γ : RFT} where
    halt : Block id []
    ↝    : ControlInstr Γ → Block id []
    _∙_  : ∀ {new new' Δ Δ' Δ''}
         → {ss   : Δ ⊆ Γ}           → Instr ss new
         → {new-ss : Δ' ⊆ new} {old-ss : Δ'' ⊆ Δ} → Block (⊆-++ new-ss old-ss) new'
         → Block (⊆-trans old-ss ss) (Δ' ++ new')

  NewBlk = Σ RegFileTypes (λ Γ → Σ RegFileTypes (λ Δ → Σ (Δ ⊆ Γ) (λ free → Σ RegFileTypes (Block free))))

  data Value : Type → Set where
    function : {free ss-free new : RFT} → {ss : ss-free ⊆ free} → Block ss new → Value (blk free)
    ptr      : ∀ {τ} → τ ∈ Ψ → Value (τ ✴)

  postulate deref : ∀ {l} → l ✴ ∈ Ψ → l ∈ Ψ
  postulate load : ∀ {l} → l ∈ Ψ → Value l

  loadblk : ∀ {Γ} → blk Γ ∈ Ψ → NewBlk
  loadblk f with load f
  loadblk f | function x = _ , _ , _ , _ , x

  postulate loadblk-≡ : ∀ {Γ A} → (f : blk Γ ∈ Ψ) → loadblk f ≡ Γ , A

  CallStack = List NewBlk
  CallCtx = CallStack × NewBlk
  
  exec-control : ∀ {Γ} → CallCtx → ControlInstr Γ → CallCtx
  exec-control (cs , ret) (call f) = ret ∷ cs , loadblk f
  exec-control (cs , ret) jmp[ f ] = cs , loadblk (deref f)
  exec-control (cs , ret) (jmp f)  = cs , loadblk f

  exec-blk : ∀ {Γ Δ Δ'} → {ss : Δ ⊆ Δ'} → CallCtx → Block ss Γ → CallCtx
  exec-blk {Δ' = Γ} (cs , ret) halt = cs , Γ , _ , _ , _ , halt
  exec-blk cc (↝ x) = exec-control cc x
  exec-blk cc (i ∙ b) = exec-blk cc b
  
  data BlockEq (CC : CallCtx) :
    {Γ₁ Γ₂ Δ₁ Δ₂ new₁ new₂ : RegFileTypes} →
    {free₁ : Δ₁ ⊆ Γ₁} {free₂ : Δ₂ ⊆ Γ₂} →
    Block free₁ new₁ → Block free₂ new₂ → Set where
    eq : ∀ {Γ Δ new} → {free : Δ ⊆ Γ} → {B : Block free new} → BlockEq CC B B
    nr : ∀ {Δ₁ Δ₂ Δ₃ Γ₁ Γ₂ Γ₃ new₁ new₂ new₃} → {free₁ : Δ₁ ⊆ Γ₁} {free₂ : Δ₂ ⊆ Γ₂} {free₃ : Δ₃ ⊆ Γ₃} → {A : Block free₁ new₁} → {B : Block free₂ new₂} → {C : Block free₃ new₃} → projr (exec-blk CC C) ≡ _ , _ , _ , _ , A → BlockEq CC A B → BlockEq CC C B
    nl : ∀ {Δ₁ Δ₂ Δ₃ Γ₁ Γ₂ Γ₃ new₁ new₂ new₃} → {free₁ : Δ₁ ⊆ Γ₁} {free₂ : Δ₂ ⊆ Γ₂} {free₃ : Δ₃ ⊆ Γ₃} → {A : Block free₁ new₁} → {B : Block free₂ new₂} → {C : Block free₃ new₃} → projr (exec-blk CC C) ≡ _ , _ , _ , _ , B → BlockEq CC A B → BlockEq CC A C
    cc : ∀ {Δ₁ Δ₂ Δ₁' Δ₂' Γ₁ Γ₂ Γ₁' Γ₂' new₁ new₂ new₁' new₂'} → {free₁ : Δ₁ ⊆ Γ₁} {free₂ : Δ₂ ⊆ Γ₂} {free₁' : Δ₁' ⊆ Γ₁'} {free₂' : Δ₂' ⊆ Γ₂'} → {B' : Block free₂' new₂'} → {A : Block free₁ new₁} → {B : Block free₂ new₂} {A' : Block free₁' new₁'} → {CC' : CallCtx} → (exec-blk CC A) ≡ projl CC' , _ , _ , _ , _ , A' → exec-blk CC B ≡ projl CC' , _ , _ , _ , _ , B' → BlockEq CC' A' B' → BlockEq CC A B

open FixedHeap public
