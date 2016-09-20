\iftoggle{russian-draft}{
\section{Доказательство эквивалентности динамически и статически слинкованных функций}
}{
\section{TODO}
}

\label{sec:proof}

\ignore{
\begin{code}
module RuntimeEq where

open import Function
open import Data.Product
open import Data.List.Any
open Membership-≡
open import Relation.Binary.PropositionalEquality

open import MetaAsm
open import Asm
open import Linkers
open import Loader
\end{code}
}

\begin{code}
exec-ijmp : ∀ {ST} → (S : State ST)
          → (p : atom (code
               (StateType.registers ST)
               (StateType.datastack ST)
               (StateType.callstack ST)
             *) ∈ StateType.memory ST)
          → exec-block S (↝ jmp[ p ])
          ≡ (S
          , loadblock
            (State.memory S)
            (loadptr (State.memory S) p))
exec-ijmp (state Γ Ψ DS CS) p = refl

exec-plt : ∀ {Γ Ψ DS CS}
         → (f : code Γ DS CS ∈ Ψ)
         → (S : State (sttype Γ (pltize Ψ) DS CS))
         → GOT[ f ]-correctness (State.memory S)
         → exec-block S (plt-stub (got f))
         ≡ (S , loadblock (State.memory S) (linked-symbol f))
exec-plt f S p rewrite sym p = exec-ijmp S (got f)

exblock-eq-proof : ∀ {Γ Ψ DS CS}
                 → (f : code Γ DS CS ∈ Ψ)
                 → (S : State
                        (sttype Γ (pltize Ψ) DS CS))
                 → GOT[ f ]-correctness
                    (State.memory S)
                 → ExBlockEq
                   (block (plt-stub (got f)) S)
                   (block
                     (proj₂ $ loadblock (State.memory S)
                                        (linked-symbol f))
                     S)
exblock-eq-proof f S p
  = left (exec-block-≡ (plt-stub (got f)) _ S S
                       (exec-plt f S p))
         equal

block-eq-proof : ∀ {Γ Ψ DS CS}
               → (f : code Γ DS CS ∈ Ψ)
               → BlockEqAssuming
                 (λ S → (GOT[ f ]-correctness
                            (State.memory S))
                      × (PLT[ f ]-correctness
                            (State.memory S)))
                 (plt f)
                 (linked-symbol f)
block-eq-proof {Γ} {Ψ} {DS} {CS} f
  = block-eq-assuming lemma
  where
    ST = sttype Γ Ψ DS CS
    lemma : (S : State $ pltize-state ST)
          → (GOT[ f ]-correctness $ State.memory S)
          × (PLT[ f ]-correctness $ State.memory S)
          → ExBlockEq
            (construct-exblock (plt f) S)
            (construct-exblock (linked-symbol f) S)
    lemma S (got-correctness , plt-correctness)
      rewrite plt-correctness
      = exblock-eq-proof f S got-correctness
\end{code}
