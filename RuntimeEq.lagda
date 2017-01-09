\iftoggle{russian-draft}{
\section{Доказательство эквивалентности динамически и статически слинкованных функций}
}{
\section{Proof of the equivalence of dynamically and statically linked functions}
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
exec-plt : ∀ {Γ Ψ DS CS}
         → (f : code Γ DS CS ∈ Ψ)
         → (S : State (sttype Γ (pltize Ψ) DS CS))
         → GOT[ f ]-correctness (State.memory S)
         → exec-block S (plt-stub (got f))
         ≡ (S , loadblock (State.memory S) (linked-symbol f))
exec-plt f (state R H D C) p rewrite sym p = refl


exblock-eq-proof : ∀ {Γ Ψ DS CS}
                 → (f : code Γ DS CS ∈ Ψ)
                 → (S : State (sttype Γ (pltize Ψ) DS CS))
                 → GOT[ f ]-correctness (State.memory S)
                 → ExBlockEq
                   (block (plt-stub (got f)) S)
                   (block
                     (proj₂ $ loadblock (State.memory S)
                                        (linked-symbol f))
                     S)
exblock-eq-proof f S p
  = left
    (exec-block-≡
      plt-block S
      f-block S
      (exec-plt f S p))
    equal
  where
  plt-block = plt-stub (got f)
  f-block = proj₂ $ loadblock (State.memory S)
                              (linked-symbol f)

block-eq-proof : ∀ {Γ Ψ DS CS}
               → (f : code Γ DS CS ∈ Ψ)
               → BlockEq (LoaderCorrectness f)
                 (plt f)
                 (linked-symbol f)
block-eq-proof {Γ} {Ψ} {DS} {CS} f
  = block-eq lemma
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
