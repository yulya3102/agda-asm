module Functions where

open import OXIj.BrutalDepTypes
open Data-List
open Data-Any

data RegType : Set
data Type : Set

RegTypes      = List RegType
DataType      = List Type
DataStackType = List RegType
CallStackType = List RegTypes

record StateType : Set where
  constructor statetype
  field
    registers : RegTypes
    memory    : DataType
    datastack : DataStackType
    callstack : CallStackType

data RegType where
  _✴  : Type → RegType
  int : RegType

data Type where
  atom : RegType → Type
  func : RegTypes → Type

open Membership {A = Type} _≡_
_∈R_ = Membership._∈_ {A = RegType} _≡_

module Meta where
  module Diffs where
    module RegDiff where
      data Chg (Γ : RegTypes) : Set where
        chg : ∀ {τ} → τ ∈R Γ → RegType → Chg Γ
  
      chgapply : (Γ : RegTypes) → Chg Γ → RegTypes
      chgapply (_ ∷ Γ) (chg (here refl) σ) = σ ∷ Γ
      chgapply (τ ∷ Γ) (chg (there p)   σ) = τ ∷ chgapply Γ (chg p σ)
  
      data Diff (Γ : RegTypes) : Set where
        dempty : Diff Γ
        dchg   : (c : Chg Γ) → Diff (chgapply Γ c) → Diff Γ

      dc : ∀ {Γ} → Chg Γ → Diff Γ
      dc c = dchg c dempty
  
      dapply : (Γ : RegTypes) → Diff Γ → RegTypes
      dapply Γ dempty = Γ
      dapply Γ (dchg c d) = dapply (chgapply Γ c) d
  
      dappend : ∀ {Γ} → (d : Diff Γ) → Diff (dapply Γ d) → Diff Γ
      dappend dempty d' = d'
      dappend (dchg c d) d' = dchg c (dappend d d')

      dappend-dempty-lemma : ∀ {Γ} → (d : Diff Γ) → dappend d dempty ≡ d
      dappend-dempty-lemma dempty = refl
      dappend-dempty-lemma (dchg c d) rewrite dappend-dempty-lemma d = refl

    module StackDiff (A : Set) where
      data Chg (S : List A) : Set where
        push : (i : A) → Chg S
        pop  : ∀ {Γ S'} → S ≡ Γ ∷ S' → Chg S

      chgapply : (S : List A) → Chg S → List A
      chgapply cs (push x) = x ∷ cs
      chgapply (._ ∷ S') (pop refl) = S'

      data Diff (S : List A) : Set where
        dempty : Diff S
        dchg   : (c : Chg S) → Diff (chgapply S c) → Diff S

      dc : ∀ {S} → Chg S → Diff S
      dc c = dchg c dempty
  
      dapply : (S : List A) → Diff S → List A
      dapply S dempty = S
      dapply S (dchg c d) = dapply (chgapply S c) d

      dappend : ∀ {S} → (d : Diff S) → Diff (dapply S d) → Diff S
      dappend dempty d' = d'
      dappend (dchg c d) d' = dchg c (dappend d d')

    record Diff (S : StateType) : Set where
      constructor diff
      field
        rdiff  : RegDiff.Diff (StateType.registers S)
        dsdiff : StackDiff.Diff RegType (StateType.datastack S)
        csdiff : StackDiff.Diff RegTypes (StateType.callstack S)
    open Diff public

    dempty : ∀ {S} → Diff S
    dempty = diff (RegDiff.dempty) (StackDiff.dempty) StackDiff.dempty

    dapply : (S : StateType) → Diff S → StateType
    dapply (statetype r m d c) (diff rd dd cd) =
        statetype
        (RegDiff.dapply r rd)
        m
        (StackDiff.dapply RegType d dd)
        (StackDiff.dapply RegTypes c cd)

    dappend : ∀ {S} → (d : Diff S) → Diff (dapply S d) → Diff S
    dappend (diff rd dd cd) (diff rd' dd' cd') =
        diff
        (RegDiff.dappend rd rd')
        (StackDiff.dappend RegType dd dd')
        (StackDiff.dappend RegTypes cd cd')

    DataStackChg : StateType → Set
    DataStackChg S = StackDiff.Chg (RegType) (StateType.datastack S)

    CallStackChg : StateType → Set
    CallStackChg S = StackDiff.Chg (RegTypes) (StateType.callstack S)

    RegChg : StateType → Set
    RegChg S = RegDiff.Chg (StateType.registers S)

    SmallChg : StateType → Set
    SmallChg S = RegChg S ∨ DataStackChg S

    regChg : ∀ {S} → RegChg S → Diff S
    regChg c =
        diff
        (RegDiff.dchg c RegDiff.dempty)
        StackDiff.dempty
        StackDiff.dempty

    dsChg : ∀ {S} → DataStackChg S → Diff S
    dsChg c =
      diff
      RegDiff.dempty
      (StackDiff.dchg c StackDiff.dempty)
      StackDiff.dempty

    sChg : ∀ {S} → SmallChg S → Diff S
    sChg (inl r) = regChg r
    sChg (inr d) = dsChg d

    csChg : ∀ {S} → CallStackChg S → Diff S
    csChg c =
        diff
        RegDiff.dempty
        StackDiff.dempty
        (StackDiff.dchg c StackDiff.dempty)
  open Diffs

  module Blocks
    -- вообще-то, стек может и не меняться (например, при jump)
    (ControlInstr : (S : StateType) → CallStackChg S → Set)
    (Instr : (S : StateType) → SmallChg S → Set)
    where
    data Block (S : StateType) : Diff S → Set where
      jump : ∀ {c} → ControlInstr S c → Block S (csChg c)
      next : ∀ {c d} → Instr S c → Block (dapply S (sChg c)) d → Block S (dappend (sChg c) d)

  module Values
    (Block : (S : StateType) → Diff S → Set)
    where
    data RegValue (Ψ : DataType) : RegType → Set where
      ptr : ∀ {τ} → τ ∈ Ψ → RegValue Ψ (τ ✴)
      int : ℕ → RegValue Ψ int

    data Value (Ψ : DataType) : Type → Set where
      atom : ∀ {τ} → RegValue Ψ τ → Value Ψ (atom τ)
      func : ∀ {Γ DS CS d} → Block (statetype Γ Ψ DS CS) d → Value Ψ (func Γ)
      
    data Registers (Ψ : DataType) : RegTypes → Set where
      []  : Registers Ψ []
      _∷_ : ∀ {τ τs} → RegValue Ψ τ → Registers Ψ τs → Registers Ψ (τ ∷ τs)

    data IData (Ψ : DataType) : DataType → Set where
      []  : IData Ψ []
      _∷_ : ∀ {τ τs} → Value Ψ τ → IData Ψ τs → IData Ψ (τ ∷ τs)

    Data : DataType → Set
    Data Ψ = IData Ψ Ψ

    data Stack {I : Set} {A : I → Set} (Ψ : DataType) : List I → Set where
      []   : Stack Ψ []
      _∷_  : ∀ {τ S} → A τ → Stack {A = A} Ψ S → Stack Ψ (τ ∷ S)

    IPRT : DataType → RegTypes → Set
    IPRT Ψ Γ = func Γ ∈ Ψ

    DataStack = λ Ψ → Stack {A = RegValue Ψ} Ψ
    CallStack = λ Ψ → Stack {A = IPRT Ψ} Ψ

    record State (S : StateType) : Set where
      constructor state
      field
        registers : Registers (StateType.memory S) (StateType.registers S)
        memory    : Data (StateType.memory S)
        datastack : DataStack (StateType.memory S) (StateType.datastack S)
        callstack : CallStack (StateType.memory S) (StateType.callstack S)

  module Eq
    (Block : (S : StateType) → Diff S → Set)
    (exec-block : ∀ {ST d} → Values.State Block ST → Block ST d
                → Values.State Block (dapply ST d)
                × Σ (Diff (dapply ST d)) (Block (dapply ST d)))
    where
    open Values Block

    data BlockEq (Ψ : DataType)
      : {ST₁ ST₂ : StateType}
      → {d₁ : Diff ST₁} {d₂ : Diff ST₂}
      → (S₁ : State ST₁) (S₂ : State ST₂)
      → Block ST₁ d₁ → Block ST₂ d₂
      → Set
      where
      equal : ∀ {ST} → {S : State ST} {d : Diff ST} {A : Block ST d}
            → BlockEq Ψ S S A A
      left  : ∀ {ST₁ ST}
            → {d₁ : Diff ST₁} {d₂ : Diff (dapply ST₁ d₁)} {d : Diff ST}
            → {S₁ : State ST₁} {S₂ : State (dapply ST₁ d₁)} {S : State ST}
            → {A₁ : Block ST₁ d₁} {A₂ : Block (dapply ST₁ d₁) d₂} {B : Block ST d}
            → exec-block S₁ A₁ ≡ S₂ , d₂ , A₂
            → BlockEq Ψ S₂ S A₂ B
            → BlockEq Ψ S₁ S A₁ B
      right : ∀ {ST₁ ST}
            → {d₁ : Diff ST₁} {d₂ : Diff (dapply ST₁ d₁)} {d : Diff ST}
            → {S₁ : State ST₁} {S₂ : State (dapply ST₁ d₁)} {S : State ST}
            → {A₁ : Block ST₁ d₁} {A₂ : Block (dapply ST₁ d₁) d₂} {B : Block ST d}
            → exec-block S₁ A₁ ≡ S₂ , d₂ , A₂
            → BlockEq Ψ S S₂ B A₂
            → BlockEq Ψ S S₁ B A₁

module 2Meta
  (ControlInstr : (S : StateType) → Meta.Diffs.CallStackChg S → Set)
  (Instr : (S : StateType) → Meta.Diffs.SmallChg S → Set)
  -- АБСОЛЮТНО НЕЧИТАЕМЫЙ ТИП, ААААА
  (exec-control : ∀ {S c}
                → Meta.Values.CallStack
                 (Meta.Blocks.Block ControlInstr Instr)
                 (StateType.memory S)
                 (StateType.callstack S)
                → ControlInstr S c
                → Meta.Values.CallStack
                 (Meta.Blocks.Block ControlInstr Instr)
                 (StateType.memory S)
                 (Meta.Diffs.StackDiff.chgapply RegTypes
                   (StateType.callstack S) c)
                × Σ
                  (Meta.Diffs.Diff
                    (Meta.Diffs.dapply S (Meta.Diffs.csChg c)))
                  (Meta.Blocks.Block ControlInstr Instr
                    (Meta.Diffs.dapply S (Meta.Diffs.csChg c))))
  (exec-instr : ∀ {S c}
              → Meta.Values.Registers
               (Meta.Blocks.Block ControlInstr Instr)
               (StateType.memory S)
               (StateType.registers S)
              → Meta.Values.DataStack
               (Meta.Blocks.Block ControlInstr Instr)
               (StateType.memory S)
               (StateType.datastack S)
              → Instr S c
              → Meta.Values.Registers
               (Meta.Blocks.Block ControlInstr Instr)
               (StateType.memory {!!})
               (StateType.registers {!!})
              × Meta.Values.DataStack
               (Meta.Blocks.Block ControlInstr Instr)
               (StateType.memory {!!})
               (StateType.datastack {!!}))
  where
  open Meta
  open Diffs
  open Blocks ControlInstr Instr
  open Values Block

  exec-block : ∀ {ST d} → State ST → Block ST d
             → State (dapply ST d)
             × Σ (Diff (dapply ST d)) (Block (dapply ST d))
  exec-block (state Γ Ψ D CS) (Blocks.jump ci) =
    state Γ Ψ D (projl ec) , projr ec
    where
    ec = exec-control CS ci
  exec-block {statetype registers memory datastack callstack} {diff ._ ._ ._} s (Blocks.next i b) = {!!}

  open Eq Block exec-block

module AMD64 where
  open Meta
  open Diffs
  
  data ControlInstr (S : StateType) : CallStackChg S → Set where
    -- везде, где требуется сакральное знание о том, что расположено в памяти
    -- за этой инструкцией, я принимаю дополнительный аргумент
    -- это сделано для упрощения себе жизни
    -- в реальный ассемблер это отобразится одним лишним jump
    call : (f : func (StateType.registers S) ∈ StateType.memory S)
         -- по-хорошему, ниже должно быть не memory S, а что-то другое
         -- но мне плевать, потому что память неизменна
         → {Γ : RegTypes} → (cont : func Γ ∈ StateType.memory S)
         → ControlInstr S (StackDiff.push Γ)
    ijmp : (f : func (StateType.registers S) ∈ StateType.memory S)
         → ControlInstr S {!!}
  
  open 2Meta ControlInstr {!!} {!!} {!!}
