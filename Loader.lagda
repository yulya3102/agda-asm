# Эквивалентность статически и динамически слинкованных функций

\ignore{
\begin{code}
module Loader where

open import Data.Product
open import Data.List.Any
open Membership-≡
open import Relation.Binary.PropositionalEquality

open import MetaAsm
open import Asm
open import Linkers
\end{code}
}

Используя семантику инструкции \C{jmp[\_]} и определение \F{plt-stub},
покажем, что функция эквивалентна своему PLT при корректно заполненном GOT.

Это позволяет показать, что вызов функции напрямую, как в случае
статической линковки, семантически эквивалентнен вызову ее PLT, как в
случае динамической линковки.

Код - в приложениии.

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
