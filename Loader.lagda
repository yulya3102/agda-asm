\iftoggle{russian-draft}{
\section{Эквивалентность динамически и статически слинкованных функций}
}{
\section{Equivalence of dynamically and statically linked functions}
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
The proof of equivalence of PLT block and corresponding functions relies on
assumptions of the correctness of dynamic loader. These assumptions are shown
in Listing \ref{fig:correctness}. Assumption \F{GOT[ f ]-correctness}
states that corresponding to function $f$ GOT element contains the address
of the function $f$. Assumption \F{PLT[ f ]-correctness} states that the
address corresponding to appropriate PLT function contains the PLT block.
}

**TODO: GOT[ f ]-correctness and PLT[ f ]-correctness statements**

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
}{
The code of the proof of the equivalence of function $f$ and its PLT block is
shown in Appendix \ref{sec:proof}. First, using instruction \C{jmp[\_]}
semantics, lemma \F{exec-ijmp} states that execution of block with this
instruction does not change machine state \V{S}. It also states that
execution continues with block loaded from the address from the variable \V{p}
which is an argument of that \C{jmp[\_]} instruction.
}

\iftoggle{russian-draft}{
Вторая лемма, \F{exec-plt}, используя предположение о корректности GOT
и лемму \F{exec-ijmp}, показывает, что исполнение блока PLT, ссылающегося на
GOT некоторой функции $f$, приводит к исполнению функции $f$ в исходном
состоянии исполнителя.
}{
The second lemma, \F{exec-plt}, uses the assumption of GOT correctness and
lemma \F{exec-ijmp}. It states that the execution of the PLT block
referring to the GOT of some function $f$ leads to the execution of the
function $f$ in the same machine state.
}

\iftoggle{russian-draft}{
Затем лемма \F{exblock-eq-proof}, используя предыдущую лемму,
конструирует отношение эквивалентности исполняемых блоков для блока PLT
функции $f$ и ее самой для одного и того же состояния исполнителя $S$.
}{
Then lemma \F{exblock-eq-proof}, using previous lemma, constructs the
executable blocks equivalence for the PLT block of some function $f$ and
function $f$ itself for some machine state $S$.
}

\iftoggle{russian-draft}{
После этого \F{block-eq-proof} строит искомое отношение эквивалентности
блоков для произвольных одинаковых состояний исполнителя, удовлетворяющих
предположениям о корректности работы динамического загрузчика.
}{
After that \F{block-eq-proof} constructs desired block equivalence relation
for arbitrary machine state that meets assumptions of the correctness of
dynamic loader's work result.
}

**TODO: program semantics statement**
