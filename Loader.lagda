\iftoggle{russian-draft}{
\section{Эквивалентность динамически и статически слинкованных функций}
}{
\section{TODO}
}

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

\iftoggle{russian-draft}{
Доказательство эквивалентности блоков PLT и соответствующих им функций
опирается на предположения о том, что динамический загрузчик корректно
выполняет свою работу. Эти предположения приведены в листинге
\ref{fig:correctness}.  Предположение \F{GOT[ f ]-correctness} утверждает,
что в элементе GOT, соответстующем функции $f$, находится адрес функции $f$, а
предположение \F{PLT[ f ]-correctness} утверждает, что по адресу,
соответствующему нужному блоку PLT, действительно находится блок PLT.
}{
\textbf{TODO}
}

\labeledfigure{fig:correctness}{Properties of the dynamic loader}{
\begin{code}
GOT[_]-correctness : ∀ {Γ Ψ DS CS}
                   → (f : code Γ DS CS ∈ Ψ)
                   → (H : Data (pltize Ψ))
                   → Set
GOT[ f ]-correctness H
    = loadptr H (got f) ≡ linked-symbol f

PLT[_]-correctness : ∀ {Γ Ψ DS CS}
                   → (f : code Γ DS CS ∈ Ψ)
                   → (H : Data (pltize Ψ))
                   → Set
PLT[ f ]-correctness H
    = loadblock H (plt f) ≡ (dempty , plt-stub (got f))
\end{code}
}

\iftoggle{russian-draft}{
Код доказательства эквивалентности функции $f$ и ее блока PLT приведен в
приложении \ref{sec:proof}. Сперва, используя семантику инструкции
\C{jmp[\_]}, лемма \F{exec-ijmp} показывает, что в результате исполнения
блока с этой инструкцией
состояние исполнителя \AgdaBound{S} не изменится, а исполнение передастся
на блок, загруженный из адреса, записаного в ячейке памяти \AgdaBound{p},
переданной аргументом в \C{jmp[\_]}.

Вторая лемма, \F{exec-plt}, используя предположение о корректности GOT
и лемму \F{exec-ijmp}, показывает, что исполнение блока PLT, ссылающегося на
GOT некоторой функции $f$, приводит к исполнению функции $f$ в исходном
состоянии исполнителя.

Затем лемма \F{exblock-eq-proof}, используя предыдущую лемму,
конструирует отношение эквивалентности исполняемых блоков для блока PLT
функции $f$ и ее самой для одного и того же состояния исполнителя $S$.

После этого \F{block-eq-proof} строит искомое отношение эквивалентности
блоков для произвольных одинаковых состояний исполнителя, удовлетворяющих
предположениям о корректности работы динамического загрузчика.
}{
\textbf{TODO}
}
