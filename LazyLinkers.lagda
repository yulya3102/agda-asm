# Ленивая линковка

\ignore{
\begin{code}
module LazyLinkers where
\end{code}

**TODO: натырить сюда кода из написанного после бакалаврской**

\begin{code}
open import Function
open import Data.Product
open import Data.List
open import Data.List.Any
open Membership-≡
open import Data.List.Any.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import MetaAsm
open import Asm
open import Programs
\end{code}
}

\begin{code}
pltize : DataType → DataType
pltize [] = []
pltize (atom x ∷ Ψ) = atom x ∷ pltize Ψ
pltize (block Γ DS CS ∷ Ψ)
  = block Γ DS CS
  ∷ (block Γ DS CS
  ∷ (atom (block Γ DS CS *)
  ∷ (block Γ DS CS
  ∷ pltize Ψ)))
\end{code}

\begin{code}
plt : ∀ {Γ Ψ DS CS} → block Γ DS CS ∈ Ψ
    → block Γ DS CS ∈ pltize Ψ
plt (here refl) = here refl
plt {Ψ = atom x ∷ Ψ} (there f) = there $ plt f
plt {Ψ = block Γ DS CS ∷ Ψ} (there f)
  = there $ there (there (there (plt f)))
\end{code}

\begin{code}
got : ∀ {Γ Ψ DS CS} → block Γ DS CS ∈ Ψ
    → atom (block Γ DS CS *) ∈ pltize Ψ
got (here refl) = there $ there (here refl)
got {Ψ = atom x ∷ Ψ} (there f) = there $ got f
got {Ψ = block Γ DS CS ∷ Ψ} (there f)
  = there $ there (there (there (got f)))
\end{code}

\begin{code}
func : ∀ {Γ Ψ DS CS} → block Γ DS CS ∈ Ψ
    → block Γ DS CS ∈ pltize Ψ
func (here refl) = there $ there (there (here refl))
func {Ψ = atom x ∷ Ψ} (there f) = there $ func f
func {Ψ = block Γ DS CS ∷ Ψ} (there f)
  = there $ there (there (there (func f)))
\end{code}

\begin{code}
plt-stub : ∀ {Γ Ψ DS CS}
         → atom (block Γ DS CS *) ∈ Ψ
         → Block (statetype Γ Ψ DS CS) dempty
plt-stub got = ↝ jmp[ got ]
\end{code}

\begin{code}
GOT[_]-correctness : ∀ {Γ Ψ DS CS}
                   → (f : block Γ DS CS ∈ Ψ)
                   → (H : Data (pltize Ψ))
                   → Set
GOT[ f ]-correctness H
    = loadptr H (got f) ≡ func f

PLT[_]-correctness : ∀ {Γ Ψ DS CS}
                   → (f : block Γ DS CS ∈ Ψ)
                   → (H : Data (pltize Ψ))
                   → Set
PLT[ f ]-correctness H
    = loadblock H (plt f) ≡ (dempty , plt-stub (got f))
\end{code}

TODO

\ignore{
\begin{code}
exec-ijmp : ∀ {ST} → (S : State ST)
          → (p : atom (block
               (StateType.registers ST)
               (StateType.datastack ST)
               (StateType.callstack ST)
             *) ∈ StateType.memory ST)
          → exec-block S (↝ jmp[ p ])
          ≡ (S
          , loadblock
            (State.memory S)
            (loadptr (State.memory S) p))
exec-ijmp S p = refl
\end{code}

*   состояние исполнителя в момент непосредственного вызова функции
    эквивалентно состоянию исполнителя после исполнения соответствующего
    этой функции элемента PLT при условии корректно заполненного GOT;

\begin{code}
exec-plt : ∀ {Γ Ψ DS CS}
         → (f : block Γ DS CS ∈ Ψ)
         → (S : State (statetype Γ (pltize Ψ) DS CS))
         → GOT[ f ]-correctness (State.memory S)
         → exec-block S (plt-stub (got f))
         ≡ (S , loadblock (State.memory S) (func f))
exec-plt f S p rewrite sym p = exec-ijmp S (got f)
\end{code}

Используя эти леммы, можно доказать, что если GOT заполнен корректно,
то верна внешняя эквивалентность блока PLT, использующего соответствующий
функции элемент GOT, и самой функции:

\begin{code}
exblock-eq-proof : ∀ {Γ Ψ DS CS}
                 → (f : block Γ DS CS ∈ Ψ)
                 → (S : State (statetype Γ (pltize Ψ) DS CS))
                 → GOT[ f ]-correctness (State.memory S)
                 → ExBlockEq
                   (block (plt-stub (got f)) S)
                   (block (proj₂ $ loadblock (State.memory S) (func f)) S)
exblock-eq-proof f S p = left (exec-block-≡ (plt-stub (got f)) _ S S (exec-plt f S p)) equal
\end{code}
}

\begin{code}
pltize-state : StateType → StateType
pltize-state ST = record ST { memory = pltize $ StateType.memory ST }

block-eq-proof : ∀ {Γ Ψ DS CS}
               → (f : block Γ DS CS ∈ Ψ)
               → BlockEqAssuming
                 (λ S → (GOT[ f ]-correctness $ State.memory S)
                      × (PLT[ f ]-correctness $ State.memory S))
                 (plt f)
                 (func f)
block-eq-proof {Γ} {Ψ} {DS} {CS} f = block-eq-assuming lemma
  where
    ST = statetype Γ Ψ DS CS
    lemma : (S : State $ pltize-state ST)
          → (GOT[ f ]-correctness $ State.memory S)
          × (PLT[ f ]-correctness $ State.memory S)
          → ExBlockEq
            (construct-exblock (plt f) S)
            (construct-exblock (func f) S)
    lemma S (got-correctness , plt-correctness)
      rewrite plt-correctness = exblock-eq-proof f S got-correctness
\end{code}
