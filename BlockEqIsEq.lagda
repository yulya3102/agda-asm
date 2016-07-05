\ignore{
\begin{code}
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Binary
open import Function

open import MetaAsm
open Diffs
open Meta

module BlockEqIsEq
  (Block : (S : StateType) → Diff S → Set)
  (exec-block : ∀ {ST d} → Values.State Block ST → Block ST d
              → Values.State Block (dapply ST d)
              × Σ (Diff (dapply ST d)) (Block (dapply ST d)))
  where

open import BlockEq Block exec-block
\end{code}
}

# Доказательство свойств эквивалентности для эквивалентности исполняемых блоков

\label{sec:is-equivalence}

\begin{code}
isEquivalence : ∀ {ST} → IsEquivalence (ExBlockEq {ST})
isEquivalence = record
  { refl = equal
  ; sym = exblock-eq-sym
  ; trans = exblock-eq-trans
  }
  where
  exblock-eq-sym : ∀ {ST₁ ST₂}
                 → {A : ExecutableBlock ST₁}
                 → {B : ExecutableBlock ST₂}
                 → ExBlockEq A B → ExBlockEq B A
  exblock-eq-sym equal = equal
  exblock-eq-sym (left p eq) = right p (exblock-eq-sym eq)
  exblock-eq-sym (right p eq) = left p (exblock-eq-sym eq)

  exblock-eq-trans : ∀ {ST₁ ST₂ ST₃}
                   → {A : ExecutableBlock ST₁}
                   → {B : ExecutableBlock ST₂}
                   → {C : ExecutableBlock ST₃}
                   → ExBlockEq A B → ExBlockEq B C → ExBlockEq A C
  exblock-eq-trans equal bc = bc
  exblock-eq-trans ab equal = ab
  exblock-eq-trans ab (right p bc)
    = right p (exblock-eq-trans ab bc)
  exblock-eq-trans (left p ab) bc
    = left p (exblock-eq-trans ab bc)
  exblock-eq-trans (right refl ab) (left refl bc)
    = exblock-eq-trans ab bc
\end{code}
