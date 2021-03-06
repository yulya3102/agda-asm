\ignore{
\begin{code}
open import Data.Product
open import Data.List.Any
open Membership-≡
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Binary
open import Function

open import Core
open import MetaAsm
open import Diffs
open Meta
\end{code}

\begin{code}
module BlockEq
  (Block : (S : StateType) → TypeDiff S → Set)
  (exec-block : ∀ {ST d} → Values.State Block ST → Block ST d
              → Values.State Block (dapply ST d)
              × Σ (TypeDiff (dapply ST d)) (Block (dapply ST d)))
  where
\end{code}
\begin{code}
  open Values Block
\end{code}
}

\labeledfigure{fig:ExecutableBlock}{Executable block definition}{
\begin{code}
  record ExecutableBlock (ST : StateType) : Set
    where
    constructor block
    field
      {exdiff} : TypeDiff ST
      exblock  : Block ST exdiff
      exstate  : State ST
\end{code}
}

\ignore{
\begin{code}
    exec-exblock : ExecutableBlock (dapply ST exdiff)
    exec-exblock = record { exblock = next-block ; exstate = next-state }
      where
      r : State (dapply ST exdiff) ×
          Σ (TypeDiff (dapply ST exdiff)) (Block (dapply ST exdiff))
      r = exec-block exstate exblock
      next-state = proj₁ r
      next-block = proj₂ (proj₂ r)
  open ExecutableBlock

  exec-block-≡ : ∀ {ST}
               → {d₁ : TypeDiff ST}     → {d₂ : TypeDiff (dapply ST d₁)}
               → (b₁ : Block ST d₁)
               → (S₁ : State ST)
               → (b₂ : Block (dapply ST d₁) d₂)
               → (S₂ : State (dapply ST d₁))
               → exec-block S₁ b₁ ≡ (S₂ , d₂ , b₂)
               → exec-exblock (block b₁ S₁) ≡ block b₂ S₂
  exec-block-≡ _ _ _ _ refl = refl

  construct-exblock : ∀ {ST} → IPST ST → State ST → ExecutableBlock ST
  construct-exblock B S = block (proj₂ $ loadblock (State.memory S) B) S
\end{code}
}

\labeledfigure{fig:ExBlockEq}{Executable blocks equivalence definition}{
\begin{code}
  data ExBlockEq
    : {ST₁ ST₂ : StateType}
    → ExecutableBlock ST₁
    → ExecutableBlock ST₂
    → Set
    where
    equal : ∀ {ST}
          → {A : ExecutableBlock ST}
          → ExBlockEq A A
    left  : ∀ {ST₁ ST}
          → {A₁ : ExecutableBlock ST₁}
          → {A₂ : ExecutableBlock
                    (dapply ST₁ (exdiff A₁))}
          → {B : ExecutableBlock ST}
          → exec-exblock A₁ ≡ A₂
          → ExBlockEq A₂ B
          → ExBlockEq A₁ B
    right : ∀ {ST₁ ST}
          → {A₁ : ExecutableBlock ST₁}
          → {A₂ : ExecutableBlock
                    (dapply ST₁ (exdiff A₁))}
          → {B : ExecutableBlock ST}
          → exec-exblock A₁ ≡ A₂
          → ExBlockEq B A₂
          → ExBlockEq B A₁
\end{code}
}

\labeledfigure{fig:BlockEqAssuming}{Blocks equivalence definition}{
\begin{code}
  record BlockEq
    {Γ : RegFileTypes}
    {Ψ : HeapTypes}
    {DS : DataStackType}
    {CS : CallStackType}
    (assumption
        : State (sttype Γ Ψ DS CS) → Set)
    (A : code Γ DS CS ∈ Ψ)
    (B : code Γ DS CS ∈ Ψ)
    : Set₁
    where
    constructor block-eq
    field
      eq : (S : State (sttype Γ Ψ DS CS))
         → assumption S
         → ExBlockEq
            (construct-exblock A S)
            (construct-exblock B S)
\end{code}
}

\ignore{
\begin{code}
  open BlockEq public
\end{code}
}
