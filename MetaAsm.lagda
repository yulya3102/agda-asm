\ignore{
\begin{code}
module MetaAsm where

open import Data.Nat
open import Data.List
open import Data.List.Any
open Membership-≡
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Function

open import Core
import Diffs

module Meta where
  open Diffs

  module Blocks
    (ControlInstr : (S : StateType)
                  → Maybe (CallStackChg S)
                  → Set)
    (Instr : (S : StateType) → SmallChg S → Set)
    where
    infixr 10 _∙_
\end{code}
}

\labeledfigure{fig:block}{Recursive definition of code block}{
\begin{code}
    data Block (S : StateType) : Diff S → Set
      where
      ↝ : ∀ {c} → ControlInstr S c
        → Block S (csChg S c)
      _∙_ : ∀ {c d}
           → (i : Instr S c)
           → (b : Block (dapply S (sChg c)) d)
           → Block S (dappend (sChg c) d)
\end{code}
}

\ignore{
\begin{code}
  module Values
    (Block : (S : StateType) → Diff S → Set)
    where

    data RegValue (Ψ : HeapTypes) : RegType → Set where
      ptr : ∀ {τ} → τ ∈ Ψ → RegValue Ψ (τ *)
      int : ℕ → RegValue Ψ int

    data Value (Ψ : HeapTypes) : Type → Set where
      atom : ∀ {τ} → RegValue Ψ τ → Value Ψ (atom τ)
      block : ∀ {Γ DS CS d}
            → Block (sttype Γ Ψ DS CS) d
            → Value Ψ (code Γ DS CS)

    unblock : ∀ {Ψ Γ DS CS} → Value Ψ (code Γ DS CS)
            → Σ (Diff (sttype Γ Ψ DS CS))
                (Block (sttype Γ Ψ DS CS))
    unblock (block b) = _ , b

    unint : ∀ {Ψ} → RegValue Ψ int → ℕ
    unint (int x) = x

    unptr : ∀ {Ψ τ} → Value Ψ (atom (τ *)) → τ ∈ Ψ
    unptr (atom (ptr x)) = x

    atom-ptr-unptr : ∀ {Ψ τ} → (v : Value Ψ (atom (τ *)))
                   → atom (ptr (unptr v)) ≡ v
    atom-ptr-unptr (atom (ptr x)) = refl

    data Registers (Ψ : HeapTypes) : RegFileTypes → Set where
      []  : Registers Ψ []
      _∷_ : ∀ {τ τs}
          → RegValue Ψ τ
          → Registers Ψ τs
          → Registers Ψ (τ ∷ τs)

    fromreg : ∀ {Ψ Γ τ} → Registers Ψ Γ → τ ∈ Γ → RegValue Ψ τ
    fromreg (x ∷ Γ) (here refl) = x
    fromreg (x ∷ Γ) (there p) = fromreg Γ p

    toreg : ∀ {Ψ Γ σ τ}
          → Registers Ψ Γ
          → (r : σ ∈ Γ)
          → RegValue Ψ τ
          → Registers Ψ (RegDiff.chgapply Γ (RegDiff.chg r τ))
    toreg (x ∷ Γ) (here refl) v = v ∷ Γ
    toreg (x ∷ Γ) (there r) v = x ∷ (toreg Γ r v)

    data IData (Ψ : HeapTypes) : HeapTypes → Set where
      []  : IData Ψ []
      _∷_ : ∀ {τ τs} → Value Ψ τ → IData Ψ τs → IData Ψ (τ ∷ τs)

    Data : HeapTypes → Set
    Data Ψ = IData Ψ Ψ

    private
      istore : ∀ {Ψ Γ τ} → τ ∈ Γ → IData Ψ Γ → Value Ψ τ → IData Ψ Γ
      istore (here refl) (x ∷ M) v = v ∷ M
      istore (there p) (x ∷ M) v = x ∷ istore p M v

      iload : ∀ {Ψ Γ τ} → IData Ψ Γ → τ ∈ Γ → Value Ψ τ
      iload [] ()
      iload (x ∷ H) (here refl) = x
      iload (x ∷ H) (there p) = iload H p

    load : ∀ {Ψ τ} → Data Ψ → τ ∈ Ψ → Value Ψ τ
    load {Ψ} {τ} = iload

    store : ∀ {Ψ τ} → τ ∈ Ψ → Data Ψ → Value Ψ τ → Data Ψ
    store {Ψ} {τ} = istore

    loadblock : ∀ {Ψ Γ CS DS} → Data Ψ → code Γ DS CS ∈ Ψ
             → Σ (Diff (sttype Γ Ψ DS CS))
                 (Block (sttype Γ Ψ DS CS))
    loadblock Ψ f = unblock $ load Ψ f

    loadptr : ∀ {Ψ τ} → Data Ψ → atom (τ *) ∈ Ψ → τ ∈ Ψ
    loadptr Ψ p = unptr $ load Ψ p

    store-loaded : ∀ {Ψ τ} → (v : τ ∈ Ψ) → (M : Data Ψ)
                 → store v M (load M v) ≡ M
    store-loaded = istore-iloaded
      where
      istore-iloaded : ∀ {Ψ Γ τ} → (v : τ ∈ Γ) → (M : IData Ψ Γ)
                     → istore v M (iload M v) ≡ M
      istore-iloaded (here refl) (x ∷ M) = refl
      istore-iloaded (there v) (x ∷ M) rewrite istore-iloaded v M = refl

    store-loaded-ptr : ∀ {Ψ τ} → (M : Data Ψ)
                     → (p : atom (τ *) ∈ Ψ)
                     → {x : τ ∈ Ψ} → loadptr M p ≡ x
                     → store p M (atom (ptr x)) ≡ M
    store-loaded-ptr M p px
      rewrite sym px | atom-ptr-unptr (load M p)
      = store-loaded p M

    data DataStack (Ψ : HeapTypes) : List RegType → Set
      where
      []   : DataStack Ψ []
      _∷_  : ∀ {τ DS} → RegValue Ψ τ
           → DataStack Ψ DS
           → DataStack Ψ (τ ∷ DS)

    peek : ∀ {M τ DS} → DataStack M (τ ∷ DS) → RegValue M τ
    peek (x ∷ ds) = x

    dspop : ∀ {M τ DS} → DataStack M (τ ∷ DS) → DataStack M DS
    dspop (x ∷ ds) = ds

    IPRT : HeapTypes
         → RegFileTypes
         → DataStackType
         → CallStackType
         → Set
    IPRT Ψ Γ DS CS = code Γ DS CS ∈ Ψ

    IPST : StateType → Set
    IPST (sttype Γ Ψ DS CS) = IPRT Ψ Γ DS CS

    data CallStack (Ψ : HeapTypes) : CallStackType → Set where
      []  : CallStack Ψ []
      _∷_ : ∀ {Γ DS CS} → IPRT Ψ Γ DS CS → CallStack Ψ CS
          → CallStack Ψ ((Γ , DS) ∷ CS)

    record State (S : StateType) : Set where
      constructor state
      field
        registers : Registers
                    (StateType.memory S)
                    (StateType.registers S)
        memory    : Data (StateType.memory S)
        datastack : DataStack
                    (StateType.memory S)
                    (StateType.datastack S)
        callstack : CallStack
                    (StateType.memory S)
                    (StateType.callstack S)

  module ExecBlk
    (Instr : (S : StateType) → Diffs.SmallChg S → Set)
    (ControlInstr : (S : StateType)
                  → Maybe (Diffs.CallStackChg S)
                  → Set)
    (exec-instr : ∀ {S c}
                → Values.State
                  (Blocks.Block ControlInstr Instr)
                  S
                → Instr S c
                → Values.Registers
                 (Blocks.Block ControlInstr Instr)
                 (StateType.memory S)
                 (StateType.registers
                   (Diffs.dapply S (Diffs.sChg c)))
                × (Values.Data
                  (Blocks.Block ControlInstr Instr)
                  (StateType.memory S)
                × Values.DataStack
                 (Blocks.Block ControlInstr Instr)
                 (StateType.memory S)
                 (StateType.datastack
                   (Diffs.dapply S (Diffs.sChg c)))))
    (exec-control : ∀ {S c}
                 → Values.State
                   (Blocks.Block ControlInstr Instr)
                   S
                 → ControlInstr S c
                 → Values.CallStack
                  (Blocks.Block ControlInstr Instr)
                  (StateType.memory S)
                  (StateType.callstack
                    (Diffs.dapply S (Diffs.csChg S c)))
                 × Σ (Diffs.Diff
                       (Diffs.dapply S (Diffs.csChg S c)))
                     (Blocks.Block ControlInstr Instr
                       (Diffs.dapply S (Diffs.csChg S c))))
    where
    open Diffs
    open Blocks ControlInstr Instr
    open Values Block

    module DiffLemmas where
      dapply-csChg : ∀ S → (c : Maybe (CallStackChg S))
                   → dapply S (csChg S c)
                   ≡ record S {
                     callstack = maybe′
                       (StackDiff.chgapply _ (StateType.callstack S))
                       (StateType.callstack S)
                       c
                   }
      dapply-csChg S (just x) = refl
      dapply-csChg S nothing = refl

      sChg-csdiff : ∀ S → (c : SmallChg S)
                  → StateType.callstack S
                  ≡ StateType.callstack (dapply S (sChg c))
      sChg-csdiff S (onlyreg x) = refl
      sChg-csdiff S (onlystack x) = refl
      sChg-csdiff S (regstack x x₁) = refl

      mem-chg : ∀ S → (c : StateDiff.Chg S)
              → StateType.memory S
              ≡ StateType.memory (StateDiff.chgapply S c)
      mem-chg S (rchg x) = refl
      mem-chg S (dschg x) = refl
      mem-chg S (cschg x) = refl

      mem-diff : ∀ S → (d : Diff S)
               → StateType.memory S
               ≡ StateType.memory (dapply S d)
      mem-diff S DiffDefinition.dempty = refl
      mem-diff S (DiffDefinition.dchg c d)
        rewrite mem-chg S c = mem-diff _ d

      dapply-dappend-sChg : ∀ {S} → (c : SmallChg S)
                          → (d : Diff (dapply S (sChg c)))
                          → dapply S (dappend (sChg c) d)
                          ≡ dapply (dapply S (sChg c)) d
      dapply-dappend-sChg (onlyreg x) d = refl
      dapply-dappend-sChg (onlystack x) d = refl
      dapply-dappend-sChg (regstack c x) d = refl

    open DiffLemmas

    exec-block : ∀ {ST d} → State ST → Block ST d
               → State (dapply ST d)
               × Σ (Diff (dapply ST d)) (Block (dapply ST d))
    exec-block {S} (state Γ Ψ DS CS) (Blocks.↝ {c} ci)
      with exec-control (state Γ Ψ DS CS) ci
    ... | CS' , next-block
      rewrite dapply-csChg S c
      = state Γ Ψ DS CS' , next-block
    exec-block {S} (state Γ Ψ DS CS) (Blocks._∙_ {c} {d} i b)
      with exec-instr (state Γ Ψ DS CS) i
    ... | Γ' , Ψ' , DS'
      rewrite sChg-csdiff S c | mem-diff S (sChg c)
            | dapply-dappend-sChg c d
      = exec-block (state Γ' Ψ' DS' CS) b
\end{code}
}
