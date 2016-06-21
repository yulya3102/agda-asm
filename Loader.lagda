# Эквивалентность динамически и статически слинкованных функций

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

Доказательство эквивалентности блоков PLT и соответствующих им функций
опирается на предположения о том, что динамический загрузчик добросовестно
выполняет свою работу. Эти предположения приведены в листинге
\ref{fig:correctness}.  Предположение \F{GOT[ f ]-correctness} утверждает,
что в элементе GOT, соответстующем функции f, находится адрес f, а
предположение \F{PLT[ f ]-correctness} утверждает, что по адресу,
соответствующему нужному блоку PLT, действительно находится блок PLT.

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

Доказательство эквивалентности функции $f$ и ее блока PLT приведено в
**TODO reference appendix B**. Сперва, используя семантику инструкции
\C{jmp[\_]}, лемма \F{exec-ijmp} показывает, что в результате исполнения
блока с этой инструкцией
состояние исполнителя не изменится, а исполнение передастся на блок, адрес
которого записан в ячейке памяти, переданной аргументом в \C{jmp[\_]}.

Вторая лемма, \F{exec-plt}, используя предположение о корректности GOT
и предыдущую лемму, показывает, что исполнение блока PLT некоторой функции
$f$ приводит к исполнению функции $f$ в том же состоянии исполнителя.

Затем, используя лемму \F{exec-plt}, лемма \F{exblock-eq-proof}
конструирует отношение эквивалентности исполняемых блоков функции $f$ и ее
блока PLT для одного и того же состояния исполнителя $S$.

После этого \F{block-eq-proof} строит искомое отношение эквивалентности
блоков для произвольных одинаковых состояний исполнителя, удовлетворяющих
предположениям о корректности работы динамического загрузчика.
