\ignore{
\begin{code}
module Linkers where

open import Function
open import Data.Product
open import Data.List
open import Data.List.Any
open Membership-≡
open import Data.List.Any.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import MetaAsm
open import Asm
\end{code}
}

\labeledfigure{fig:changeABI}{Object file ABI changes performed by linker}{
\begin{code}
pltize : HeapTypes → HeapTypes
pltize [] = []
pltize (atom x ∷ Ψ) = atom x ∷ pltize Ψ
pltize ((code Γ DS CS) ∷ Ψ)
  = plt-f ∷ (got-f ∷ (f ∷ pltize Ψ))
  where
    f = code Γ DS CS
    plt-f = f
    got-f = atom (f *)

plt : ∀ {Γ Ψ DS CS} → code Γ DS CS ∈ Ψ
    → code Γ DS CS ∈ pltize Ψ
plt (here refl) = here refl
plt {Ψ = atom x ∷ Ψ} (there f) = there $ plt f
plt {Ψ = code Γ DS CS ∷ Ψ} (there f)
  = there (there (there (plt f)))

got : ∀ {Γ Ψ DS CS} → code Γ DS CS ∈ Ψ
    → atom (code Γ DS CS *) ∈ pltize Ψ
got (here refl) = there (here refl)
got {Ψ = atom x ∷ Ψ} (there f) = there $ got f
got {Ψ = code Γ DS CS ∷ Ψ} (there f)
  = there (there (there (got f)))

linked-symbol : ∀ {Γ Ψ DS CS}
    → code Γ DS CS ∈ Ψ
    → code Γ DS CS ∈ pltize Ψ
linked-symbol (here refl) = there (there (here refl))
linked-symbol {Ψ = atom x ∷ Ψ} (there f)
  = there $ linked-symbol f
linked-symbol {Ψ = code Γ DS CS ∷ Ψ} (there f)
  = there (there (there (linked-symbol f)))
\end{code}
}

\ignore{
\begin{code}
pltize-state : StateType → StateType
pltize-state ST = record ST { memory = pltize $ StateType.memory ST }
\end{code}
}

\labeledfigure{fig:plt-stub}{PLT block definition}{
\begin{code}
plt-stub : ∀ {Γ Ψ DS CS}
         → atom (code Γ DS CS *) ∈ Ψ
         → Block (sttype Γ Ψ DS CS) dempty
plt-stub got = ↝ jmp[ got ]
\end{code}
}
