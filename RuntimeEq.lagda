# Эквивалентность в рантайме

Доказательство эквивалентности блоков PLT и соответствующих им функций
опирается на предположения о том, что динамический загрузчик добросовестно
выполняет свою работу. Предположение \F{GOT[ f ]-correctness} утверждает, что
в элементе GOT, соответстующем функции f, находится адрес f, а
предположение \F{PLT[ f ]-correctness} утверждает, что по адресу,
соответствующему нужному блоку PLT, действительно находится блок PLT.

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
\end{code}
}

\labeledfigure{fig:correctness}{Свойства динамического загрузчика}{
\begin{code}
GOT[_]-correctness : ∀ {Γ Ψ DS CS}
                   → (f : code Γ DS CS ∈ Ψ)
                   → (H : Data (pltize Ψ))
                   → Set
GOT[ f ]-correctness H
    = loadptr H (got f) ≡ func f

PLT[_]-correctness : ∀ {Γ Ψ DS CS}
                   → (f : code Γ DS CS ∈ Ψ)
                   → (H : Data (pltize Ψ))
                   → Set
PLT[ f ]-correctness H
    = loadblock H (plt f) ≡ (dempty , plt-stub (got f))
\end{code}
}

Дальше, используя определенную семантику инструкции \C{jmp[\_]}, можно
доказать, что в результате исполнения блока с этой инструкцией
состояние исполнителя не изменится, а исполнение передастся на блок, адрес
которого записан в ячейке памяти, переданной аргументом в \C{jmp[\_]}.

Используя предположение о корректности GOT и предыдущую лемму,
доказываем, что исполнение блока PLT некоторой функции $f$ приводит к
исполнению функции $f$ в том же состоянии исполнителя.

Дальше легким движением руки это все заворачивается в эквивалентность
исполняемых блоков $(plt f, S)$ и $(func f, S)$.

Ну и дальше заворачиваем это все в желаемую эквивалентность блоков,
используя дополнительное предположение о том, что блок PLT корректно
размещен в памяти.

\labeledfigure{fig:lemmas}{Доказательства сохранения семантики}{
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
         → (S : State (statetype Γ (pltize Ψ) DS CS))
         → GOT[ f ]-correctness (State.memory S)
         → exec-block S (plt-stub (got f))
         ≡ (S , loadblock (State.memory S) (func f))
exec-plt f S p rewrite sym p = exec-ijmp S (got f)
\end{code}
}

\labeledfigure{fig:proofs}{Доказательства сохранения семантики}{
\begin{code}
exblock-eq-proof : ∀ {Γ Ψ DS CS}
                 → (f : code Γ DS CS ∈ Ψ)
                 → (S : State (statetype Γ (pltize Ψ) DS CS))
                 → GOT[ f ]-correctness (State.memory S)
                 → ExBlockEq
                   (block (plt-stub (got f)) S)
                   (block
                     (proj₂ $ loadblock (State.memory S) (func f))
                     S)
exblock-eq-proof f S p
  = left (exec-block-≡ (plt-stub (got f)) _ S S
                       (exec-plt f S p))
         equal

block-eq-proof : ∀ {Γ Ψ DS CS}
               → (f : code Γ DS CS ∈ Ψ)
               → BlockEqAssuming
                 (λ S → (GOT[ f ]-correctness $ State.memory S)
                      × (PLT[ f ]-correctness $ State.memory S))
                 (plt f)
                 (func f)
block-eq-proof {Γ} {Ψ} {DS} {CS} f
  = block-eq-assuming lemma
  where
    ST = statetype Γ Ψ DS CS
    lemma : (S : State $ pltize-state ST)
          → (GOT[ f ]-correctness $ State.memory S)
          × (PLT[ f ]-correctness $ State.memory S)
          → ExBlockEq
            (construct-exblock (plt f) S)
            (construct-exblock (func f) S)
    lemma S (got-correctness , plt-correctness)
      rewrite plt-correctness
      = exblock-eq-proof f S got-correctness
\end{code}
}
