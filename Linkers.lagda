\iftoggle{russian-draft}{
\section{Динамическая линковка и загрузка}
}{
\section{Dynamic linking and loading}
}

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

\iftoggle{russian-draft}{
Эта работа не рассматривает объектные файлы и программы как таковые.
Вместо этого она рассматривает ABI программы целиком, о котором можно
рассуждать и без разбиения программы на разные библиотеки.  Данная статья
фокусируется на том, какие изменения динамический линкер производит с кодом
программы, а не каким образом происходит поиск внешних символов. С учетом
этого формализация разбиения программы на различные библиотеки является
лишним усложнением.
}{
This work does not consider object files and programs as actual files.
Instead it focuses on the program ABI, which can be discussed without
splitting a program into separate libraries. This paper focuses on the
program code transformations performed by dynamic linker and not the way
that external symbols should be searched for. Keeping this in mind,
formalization of splitting a program into separate libraries seems like
extra complication.
}

\labeledfigure{fig:changeABI}{Object file ABI changes performed by linker}{
\begin{code}
pltize : HeapTypes → HeapTypes
pltize [] = []
pltize (atom x ∷ Ψ) = atom x ∷ pltize Ψ
pltize (code Γ DS CS ∷ Ψ)
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

\iftoggle{russian-draft}{
С указанным выше упрощением понятие "внешнего" символа сводится всего лишь
к указанию на то, какие блоки кода должны иметь соответствующие им элементы
GOT и PLT. В целях простоты будем считать, что записи GOT и PLT
генерируются на каждый блок кода. Приведенная в листинге
\ref{fig:changeABI} функция \F{pltize} показывает, как
динамический линковщик меняет layout памяти, добавляя в него новые
элементы. Вместо каждого блока кода исходной программы $f$, рассчитывающего
на состояние регистров \AgdaBound{Γ} и состояния стеков данных
\AgdaBound{DS} и вызовов \AgdaBound{CS}, в динамически слинкованной
программе будет целых три элемента в памяти:
}{
With simplification stated earlier, notion of the "external" symbol is
reduced to marking blocks that should have corresponding GOT and PLT
elements. In order of simplicity, we will consider every code block as
having its own GOT and PLT entries. Function \F{pltize} from listing
\ref{fig:changeABI} shows how dynamic linker changes the layout of memory
by adding new elements to it. Instead of every block $f$ from original
program, that expects register state \V{Γ}, data stack \V{DS} and call
stack \V{CS}, dynamically linked program will have three elements in
memory:
}

\begin{itemize}
\item
\iftoggle{russian-draft}{
    соответствующий этому блоку кода блок PLT, который является блоком кода
    того же типа, что и $f$;
}{
    blok PLT that corresponds to this block $f$, and it have the same type
    as $f$;
}
\item
\iftoggle{russian-draft}{
    элемент GOT, являющийся указателем на блок кода того же типа, что и $f$;
}{
    GOT entry that is a pointer to a block of the same type as $f$;
}
\item
\iftoggle{russian-draft}{
    сам блок кода $f$.
}{
    block $f$.
}
\end{itemize}

\iftoggle{russian-draft}{
В реальности таблицы PLT и GOT вынесены в отдельные секции и не
располагаются рядом с кодом. Это не влияет на семантику программы,
потому перестановка элементов в памяти и группировка таблиц GOT и PLT в
данной работе не рассматривается.
}{
In real programs PLT and GOT are stored in additional sections and not
around the actual code. This does not change the program semantics, so we
do not cover in this paper rearrangement of memory elements and grouping
GOT and PLT entries together.
}

\iftoggle{russian-draft}{
Определенные дальше в листинге \ref{fig:changeABI} функции \F{plt}, \F{got}
и \F{linked-symbol} позволяют, зная, по
какому адресу находилась функция \AgdaBound{f} \AgdaSymbol{=} \F{code} \AgdaBound{\Gamma} \AgdaBound{DS} \AgdaBound{CS} в неслинкованной программе, определить,
по каким адресам будут расположены в слинкованной программе соответствующие
этой функции элемент PLT $plt.f$, элемент GOT $got.f$ и сама функция
$f$ соответственно.
}{
Functions \F{plt}, \F{got} and \F{unlinked-symbol} from listing
\ref{fig:changeABI} allow to determine where PLT entry $plt.f$, GOT entry
$got.f$ and original function $f$ \AgdaSymbol{=} \F{code} \V{\Gamma} \V{DS}
\V{CS} will be stored in dynamically linked program.
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

\iftoggle{russian-draft}{
Как было указано ранее, блок PLT должен обеспечивать получение в рантайме
адреса пролинкованной внешней функции и передачу исполнения на этот адрес.
Простейший блок PLT выглядит следующим образом: используя указанный при
компиляции адрес соответствующей ему ячейки GOT, он исполняет инструкцию
непрямого перехода \C{jmp[\_]} на тот адрес, который записан в GOT. Так
как динамический загрузчик должен после загрузки библиотеки с нужной
функцией заполнить соответствующие ей элементы GOT, положив в них ее адрес,
исполнение указанного блока PLT будет приводить к исполнению самой функции.
Код такого блока PLT, выраженный в используемой формализации языка
ассемблера, приведен в листинге \ref{fig:plt-stub}.
}{
As stated earlier, PLT block should in runtime get address of linked
external function and continue execution with code from that address. The
simplest PLT block looks like this: using specified in compile-time address
of corresponding GOT entry, it executes indirect jump instruction
\C{jmp[\_]} with address, stored in the GOT entry. As long as dynamic
loader correclty fills corresponding GOT elements after loading external
library, execution of specified PLT block will lead to execution of the
function itself. Code of such PLT block in our formalization of the
assembly language is shown in listing \ref{fig:plt-stub}.
}

\iftoggle{russian-draft}{
Как было сказано в секции \ref{sec:asm-review}, индексом Agda-типа блока
является описание изменений типа состояния исполнителя,
производимых этим блоком. В случае с блоком \F{plt-stub} это \C{dempty}:
пустое изменение состояния, потому что приведенный блок PLT ничего не
меняет. В противном случае вызов
функции через ее блок PLT не был бы прозрачным и менял бы семантику
программы.
}{
As noted in the \ref{sec:asm-review} section, Agda type of a block is
indexed by a description of machine state changes performed by this block.
For the \F{plt-stub} block it is an empty change \C{dempty}, because this
block does not change anything. Otherwise, function call through the
corresponding PLT block would be noticable and would change the program
semantics.
}
