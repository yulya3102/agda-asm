\iftoggle{russian-draft}{
\section{Доказательство свойств эквивалентности для эквивалентности исполняемых блоков}
}{
\section{Properties of equivalence relation for the executable blocks equivalence}
}

\label{sec:is-equivalence}

\ignore{
\begin{code}
open import Data.Product
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Binary
open import Function

open import Core
open import MetaAsm
open import Diffs
open Meta

module BlockEqIsEq
  (Block : (S : StateType) → TypeDiff S → Set)
  (exec-block : ∀ {ST d} → Values.State Block ST → Block ST d
              → Values.State Block (dapply ST d)
              × Σ (TypeDiff (dapply ST d)) (Block (dapply ST d)))
  where

open import BlockEq Block exec-block
\end{code}
}

\begin{code}
isEquivalence : ∀ {ST}
  → IsEquivalence (ExBlockEq {ST})
isEquivalence = record
  { refl = equal
  ; sym = is-sym
  ; trans = is-trans
  }
  where
  is-sym : ∀ {ST₁ ST₂}
         → {A : ExecutableBlock ST₁}
         → {B : ExecutableBlock ST₂}
         → ExBlockEq A B → ExBlockEq B A
  is-sym equal = equal
  is-sym (left p eq) = right p (is-sym eq)
  is-sym (right p eq) = left p (is-sym eq)

  is-trans : ∀ {ST₁ ST₂ ST₃}
           → {A : ExecutableBlock ST₁}
           → {B : ExecutableBlock ST₂}
           → {C : ExecutableBlock ST₃}
           → ExBlockEq A B → ExBlockEq B C
           → ExBlockEq A C
  is-trans equal bc = bc
  is-trans ab equal = ab
  is-trans ab (right p bc)
    = right p (is-trans ab bc)
  is-trans (left p ab) bc
    = left p (is-trans ab bc)
  is-trans (right refl ab) (left refl bc)
    = is-trans ab bc
\end{code}
