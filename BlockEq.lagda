## Program equivalence as block equivalence

TODO: block equivalence definition
TODO: why it can be considered as program equivalence

\ignore{

### Модуль Eq

Эквивалентность блоков определяется аналогично приведенному выше.

\begin{code}
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import MetaAsm
open Diffs
open Meta
\end{code}

\begin{code}
module BlockEq
  (Block : (S : StateType) → Diff S → Set)
  (exec-block : ∀ {ST d} → Values.State Block ST → Block ST d
              → Values.State Block (dapply ST d)
              × Σ (Diff (dapply ST d)) (Block (dapply ST d)))
  where
  open Values Block

  data BlockEq
    : {ST₁ ST₂ : StateType}
    → {d₁ : Diff ST₁} {d₂ : Diff ST₂}
    → (S₁ : State ST₁) (S₂ : State ST₂)
    → Block ST₁ d₁ → Block ST₂ d₂
    → Set
    where
    equal : ∀ {ST}
          → {S : State ST} {d : Diff ST} {A : Block ST d}
          → BlockEq S S A A
    left  : ∀ {ST₁ ST}
          → {d₁ : Diff ST₁} {d₂ : Diff (dapply ST₁ d₁)}
          → {d : Diff ST}
          → {S₁ : State ST₁} {S₂ : State (dapply ST₁ d₁)}
          → {S : State ST}
          → {A₁ : Block ST₁ d₁} {A₂ : Block (dapply ST₁ d₁) d₂}
          → {B : Block ST d}
          → exec-block S₁ A₁ ≡ S₂ , d₂ , A₂
          → BlockEq S₂ S A₂ B
          → BlockEq S₁ S A₁ B
    right : ∀ {ST₁ ST}
          → {d₁ : Diff ST₁} {d₂ : Diff (dapply ST₁ d₁)}
          → {d : Diff ST}
          → {S₁ : State ST₁} {S₂ : State (dapply ST₁ d₁)}
          → {S : State ST}
          → {A₁ : Block ST₁ d₁} {A₂ : Block (dapply ST₁ d₁) d₂}
          → {B : Block ST d}
          → exec-block S₁ A₁ ≡ S₂ , d₂ , A₂
          → BlockEq S S₂ B A₂
          → BlockEq S S₁ B A₁
\end{code}

}
