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
\textbf{TODO}
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
\textbf{TODO}
}

\begin{itemize}
\item
\iftoggle{russian-draft}{
    соответствующий этому блоку кода блок PLT, который является блоком кода
    того же типа, что и $f$;
}{
    \textbf{TODO}
}
\item
\iftoggle{russian-draft}{
    элемент GOT, являющийся указателем на блок кода того же типа, что и $f$;
}{
    \textbf{TODO}
}
\item
\iftoggle{russian-draft}{
    сам блок кода $f$.
}{
    \textbf{TODO}
}
\end{itemize}

\iftoggle{russian-draft}{
В реальности таблицы PLT и GOT вынесены в отдельные секции и не
располагаются рядом с кодом. Это не влияет на семантику программы,
потому перестановка элементов в памяти и группировка таблиц GOT и PLT в
данной работе не рассматривается.

Определенные дальше в листинге \ref{fig:changeABI} функции \F{plt}, \F{got}
и \F{linked-symbol} позволяют, зная, по
какому адресу находилась функция \AgdaBound{f} \AgdaSymbol{=} \F{code} \AgdaBound{\Gamma} \AgdaBound{DS} \AgdaBound{CS} в неслинкованной программе, определить,
по каким адресам будут расположены в слинкованной программе соответствующие
этой функции элемент PLT $plt.f$, элемент GOT $got.f$ и сама функция
$f$ соответственно.
}{
\textbf{TODO}
}

\ignore{
\begin{code}
pltize-ptr : ∀ {Ψ τ} → τ ∈ Ψ → τ ∈ pltize Ψ
pltize-ptr {[]} ()
pltize-ptr {_ ∷ Ψ} {atom _}      (here refl) = here refl
pltize-ptr {_ ∷ Ψ} {code _ _ _} (here refl) = here refl
pltize-ptr {atom _ ∷ Ψ}          (there px)  = there (pltize-ptr px)
pltize-ptr {code _ _ _ ∷ Ψ}     (there px)  = there (there (there (pltize-ptr px)))

pltize-atom : ∀ {Ψ τ} → RegValue Ψ τ → RegValue (pltize Ψ) τ
pltize-atom (ptr x) = ptr (pltize-ptr x)
pltize-atom (int x) = int x

pltize-state : StateType → StateType
pltize-state ST = record ST { memory = pltize $ StateType.memory ST }

postulate
  pltize-diff : ∀ {ST} → Diff ST → Diff (pltize-state ST)
  pltize-block : ∀ {ST d} → Block ST d → Block (pltize-state ST) (pltize-diff d)
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

Как было сказано в секции \ref{sec:asm-review}, индексом Agda-типа блока
является описание изменений типа состояния исполнителя,
производимых этим блоком. В случае с блоком \F{plt-stub} это \C{dempty}:
пустое изменение состояния, потому что приведенный блок PLT ничего не
меняет. В противном случае вызов
функции через ее блок PLT не был бы прозрачным и менял бы семантику
программы.
}{
\textbf{TODO}
}
