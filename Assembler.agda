module Assembler where

open import OXIj.BrutalDepTypes
open Data-List
open Data-Any

data Type : Set

RegFileTypes = List Type
HeapTypes    = List Type

data Type where
  blk : RegFileTypes → Type
  _✴  : Type → Type
  int : Type

open Membership {A = Type} _≡_

module Meta where
  record State : Set where
    constructor state
    field
      heap : HeapTypes
      regs : RegFileTypes
  open State public

  module Diffs where
    data Chg (Γ : List Type) : Set where
      chg : ∀ {τ} → τ ∈ Γ → Type → Chg Γ

    chgapply : (Γ : List Type) → Chg Γ → List Type
    chgapply (_ ∷ Γ) (chg (here refl) σ) = σ ∷ Γ
    chgapply (τ ∷ Γ) (chg (there p)   σ) = τ ∷ chgapply Γ (chg p σ)

    data Diff (Γ : List Type) : Set where
      dempty : Diff Γ
      dchg   : (c : Chg Γ) → Diff (chgapply Γ c) → Diff Γ

    dapply : (Γ : List Type) → Diff Γ → List Type
    dapply Γ dempty = Γ
    dapply Γ (dchg c d) = dapply (chgapply Γ c) d

    dappend : ∀ {Γ} → (d : Diff Γ) → Diff (dapply Γ d) → Diff Γ
    dappend dempty d' = d'
    dappend (dchg c d) d' = dchg c (dappend d d')

    record SDiff (S : State) : Set where
      constructor sdiff
      field
        heapDiff : Diff (heap S)
        regsDiff : Diff (regs S)

    sdempty : ∀ {S} → SDiff S
    sdempty = sdiff dempty dempty

    sdapply : (S : State) → SDiff S → State
    sdapply (state h r) (sdiff hd rd) = state (dapply h hd) (dapply r rd)

    sdappend : ∀ {S} → (d : SDiff S) → SDiff (sdapply S d) → SDiff S
    sdappend (sdiff hd rd) (sdiff hd' rd') = sdiff (dappend hd hd') (dappend rd rd')
  open Diffs

  module Blocks
    (ControlInstr : State → Set)
    (Instr : (S : State) → SDiff S → Set)
    where
    data Block {S : State} : SDiff S → Set where
      halt : Block sdempty
      bjmp : ControlInstr S → Block sdempty
      bnxt : ∀ {d d'} → Instr S d → Block d' → Block (sdappend d d')

    NewBlock : HeapTypes → Set
    NewBlock Ψ = Σ RegFileTypes $ λ Γ → Σ (SDiff (state Ψ Γ)) (λ d → Block d)

  module Exec-Context (Ψ : HeapTypes) where
    IPRFT = λ Γ → blk Γ ✴ ∈ Ψ
    IP = Σ RegFileTypes IPRFT
    CallStack = List IP
    CallCtx = IP × CallStack
  open Exec-Context

  module Values
    (Block : {S : State} → SDiff S → Set)
    where
    data Value (Ψ : HeapTypes) : Type → Set where
      ptr : ∀ {τ} → τ ∈ Ψ → Value Ψ (τ ✴)
      fun : ∀ {Γ} → {d : SDiff (state Ψ Γ)} → Block d → Value Ψ (blk Γ) 
  
    data IHeap (Ψ : HeapTypes) : HeapTypes → Set where
      []  : IHeap Ψ []
      _∷_ : ∀ {τ Δ} → Value Ψ τ → IHeap Ψ Δ → IHeap Ψ (τ ∷ Δ)

    lemma : {A : Set} (a : A) (as bs : List A) → as ++ a ∷ bs ≡ (as ++ [ a ]) ++ bs
    lemma a [] bs = refl
    lemma a (x ∷ as) bs rewrite lemma a as bs = refl

    iload : ∀ {Ψ τ} ψs → τ ∈ Ψ → IHeap (ψs ++ Ψ) Ψ → Value (ψs ++ Ψ) τ
    iload ψs (here refl) (x ∷ _) = x
    iload {ψ ∷ Ψ} ψs (there p) (x ∷ h)
      rewrite lemma ψ ψs Ψ = iload (ψs ++ [ ψ ]) p h

    Heap : HeapTypes → Set
    Heap Ψ = IHeap Ψ Ψ

    data IRegisters (Ψ : HeapTypes) : RegFileTypes → Set where
      []  : IRegisters Ψ []
      _∷_ : ∀ {τ τs} → Value Ψ τ → IRegisters Ψ τs → IRegisters Ψ (τ ∷ τs)

    Registers : State → Set
    Registers S = IRegisters (heap S) (regs S)

    load : ∀ {Ψ τ} → τ ∈ Ψ → Heap Ψ → Value Ψ τ
    load p heap = iload [] p heap

    unptr : ∀ {Ψ τ} → Value Ψ (τ ✴) → τ ∈ Ψ
    unptr (ptr x) = x

    unfun : ∀ {Ψ Γ} → Value Ψ (blk Γ) → Σ (SDiff (state Ψ Γ)) Block
    unfun (fun x) = _ , x
  open Values

  module Eq
    (Block : {S : State} → SDiff S → Set)
    (exec-blk : {S : State} {d : SDiff S} → Block d
              → Heap Block (heap S) → Registers Block S → CallStack (heap S)
              → (Σ (SDiff $ sdapply S d) Block)
              × (Heap Block (heap $ sdapply S d)
              × (Registers Block (sdapply S d)
              × CallStack (heap $ sdapply S d))))
    where
    module InState (S : State) where
      SHeap = Heap Block (heap S)
      SCallStack = CallStack (heap S)
    open InState

    data BlockEq :
      {S₁ S₂ : State} → {d₁ : SDiff S₁} {d₂ : SDiff S₂} →
      (Ψ₁ : SHeap S₁) (Ψ₂ : SHeap S₂) →
      (Γ₁ : Registers Block S₁) (Γ₂ : Registers Block S₂) →
      (CC₁ : SCallStack S₁) (CC₂ : SCallStack S₂) →
      Block d₁ → Block d₂ → Set
      where
      equal : ∀ {S} {d : SDiff S}
            → {Ψ : SHeap S} {CC : SCallStack S} {B : Block d} {Γ : Registers Block S}
            → BlockEq Ψ Ψ Γ Γ CC CC B B
      left  : ∀ {S₁ S} {d₁ : SDiff S₁} {d₂ : SDiff (sdapply S₁ d₁)} {d : SDiff S}
            → (A₁ : Block d₁) (A₂ : Block d₂) (B : Block d)
            → (Ψ₁ : SHeap S₁) (Ψ₂ : SHeap (sdapply S₁ d₁)) (Ψ : SHeap S)
            → (Γ₁ : Registers Block S₁) (Γ₂ : Registers Block (sdapply S₁ d₁)) (Γ : Registers Block S)
            → (CC₁ : SCallStack S₁) (CC₂ : SCallStack (sdapply S₁ d₁)) (CC : SCallStack S)
            → exec-blk A₁ Ψ₁ Γ₁ CC₁ ≡ (_ , A₂) , Ψ₂ , Γ₂ , CC₂
            → BlockEq Ψ₁ Ψ Γ₁ Γ CC₁ CC A₁ B
            → BlockEq Ψ₂ Ψ Γ₂ Γ CC₂ CC A₂ B
      right : ∀ {S₁ S} {d₁ : SDiff S₁} {d₂ : SDiff (sdapply S₁ d₁)} {d : SDiff S}
            → (A₁ : Block d₁) (A₂ : Block d₂) (B : Block d)
            → (Ψ₁ : SHeap S₁) (Ψ₂ : SHeap (sdapply S₁ d₁)) (Ψ : SHeap S)
            → (Γ₁ : Registers Block S₁) (Γ₂ : Registers Block (sdapply S₁ d₁)) (Γ : Registers Block S)
            → (CC₁ : SCallStack S₁) (CC₂ : SCallStack (sdapply S₁ d₁)) (CC : SCallStack S)
            → exec-blk A₁ Ψ₁ Γ₁ CC₁ ≡ (_ , A₂) , Ψ₂ , Γ₂ , CC₂
            → BlockEq Ψ Ψ₁ Γ Γ₁ CC CC₁ B A₁
            → BlockEq Ψ Ψ₂ Γ Γ₂ CC CC₂ B A₂
  open Eq

  module Exec
    (ControlInstr : State → Set)
    (Instr : (S : State) → SDiff S → Set)
    (exec-instr : {S : State}
                → {d : SDiff S} → Instr S d
                → Heap (Blocks.Block ControlInstr Instr) (heap S)
                → Registers (Blocks.Block ControlInstr Instr) S
                → Heap (Blocks.Block ControlInstr Instr) (heap $ sdapply S d)
                × Registers (Blocks.Block ControlInstr Instr) (sdapply S d))
    (exec-control : {S : State}
                  → ControlInstr S
                  → CallStack (heap S)
                  → CallStack (heap S) × IPRFT (heap S) (regs S))
    where
    open Blocks ControlInstr Instr public

    exec-blk : {S : State} {d : SDiff S} → Block d
             → Heap Block (heap S) → Registers Block S → CallStack (heap S)
             → (Σ (SDiff $ sdapply S d) Block)
             × (Heap Block (heap $ sdapply S d)
             × (Registers Block (sdapply S d)
             × CallStack (heap $ sdapply S d)))
    exec-blk Blocks.halt Ψ Γ cs = (_ , halt) , (Ψ , Γ , cs)
    exec-blk {S} (Blocks.bjmp i) Ψ Γ cs = next-block , Ψ , Γ , next-cs
      where
      next-state : CallStack (heap S) × IPRFT (heap S) (regs S)
      next-state = exec-control i cs
      next-cs : CallStack (heap S)
      next-cs = projl next-state
      next-ip : blk (regs S) ✴ ∈ (heap S)
      next-ip = projr next-state
      next-block : Σ (SDiff (state (heap S) (regs S))) Block
      next-block = unfun Block $ load Block (unptr Block (load Block next-ip Ψ)) Ψ
    exec-blk {S} (Blocks.bnxt {d} {d'} i b) Ψ Γ cs = {!exec-blk b!}
      where
      next-state : Heap Block (heap $ sdapply S d) × Registers Block (sdapply S d)
      next-state = exec-instr i Ψ Γ
      res : Σ (SDiff $ sdapply (sdapply S d) d') Block
            × (Heap Block (heap $ sdapply (sdapply S d) d')
            × (Registers Block (sdapply (sdapply S d) d')
            × CallStack (heap $ sdapply (sdapply S d) d')))
      res = exec-blk b (projl next-state) (projr next-state) {!cs!}


    open Eq Block exec-blk public
  open Exec
open Meta
