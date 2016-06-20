# Динамическая линковка и загрузка

В данной работе формализуется упрощенный вариант динамической линковки,
используемой в файлах ELF и описанной в [@dsohowto]. В этом упрощенном
варианте поддерживается только линковка внешних функций и не подерживаются
внешние переменные.

Динамический линковщик добавляет в программу две дополнительные таблицы:
GOT (Global Offset Table) и PLT (Procedure Linkage Table). Первая хранит в
себе указатели на код, заполняемые в рантайме, вторая же содержит блоки
кода. На каждую внешнюю функцию в GOT и PLT добавляется по одному элементу,
причем все вызовы внешней функции $f$ заменяются на вызовы соответствующего
ей блока PLT $plt.f$. Элементы GOT заполняются в рантайме динамическим
загрузчиком: в ячейке GOT $got.f$, соответствующей внешней функции $f$,
после загрузки функции $f$ должен находиться ее адрес. Блок PLT в этом
случае должен выполнять необходимые действия для того, чтобы получить этот
адрес в рантайме и передать исполнение ему, не нарушив семантики программы.

\ignore{
## Linkers

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
open import Programs
\end{code}

## Static vs. dynamic linking

Statically linked program is just all binaries merged together without any
transformations. Dynamically linked program is a bunch of object files with
PLT and GOT added and calls to functions replaced with calls to
correspondent PLT elements. But when they are loaded into memory, there's no
separations between libraries left, so the only difference between
statically and dynamically linked programs is in GOT, PLT and calls to
functions. Therefore, we don't even need to define dynamically linked
program as several object files.

???: dynamically linked program cat have more than one PLT entry
correspondent to some function
TODO: what is input
TODO: how to get dynamically linked program

## Statically linked program

Static linking does not change program code, so any code without undefined
symbols can be considered statically linked. However, undefined symbols can
appear only when one binary uses symbols from another binary. Since this
formalisation doesn't have any notion of binaries and considers programs as
code loaded into memory, notion of 'undefined symbol' can't possibly make
sense. Therefore, any program in this typed assembly language can be
considered statically linked.

\begin{code}
static : ∀ {ST} → Program ST → Program ST
static = id
\end{code}

## Dynamically linked program

Dynamic linking adds some changes to program code:

*   each function gets its own GOT and PLT entries;
*   every function call is replaced with corresponding PLT entry call.

Program transformed this way can be considered dynamically linked.

TODO: GOT-correctness

TODO: generic code proofs (???)

TODO: equivalence proof
}

В этой статье не рассматриваются объектные файлы и программы как таковые.
Вместо этого рассматривается ABI программы целиком, а о нем можно
рассуждать и без разбиения программы на разные библиотеки.  Данная статья
фокусируется на том, какие изменения динамический линкер производит с кодом
программы, а не каким образом происходит поиск внешних символов. С учетом
этого формализация разбиения программы на различные библиотеки является
лишним усложнением.

\labeledfigure{fig:changeABI}{Изменения в ABI объектного файла, производимые линкером}{
\begin{code}
pltize : HeapTypes → HeapTypes
pltize [] = []
pltize (atom x ∷ Ψ) = atom x ∷ pltize Ψ
pltize (code Γ DS CS ∷ Ψ)
  = code Γ DS CS
  ∷ (atom (code Γ DS CS *)
  ∷ (code Γ DS CS
  ∷ pltize Ψ))

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

func : ∀ {Γ Ψ DS CS} → code Γ DS CS ∈ Ψ
    → code Γ DS CS ∈ pltize Ψ
func (here refl) = there (there (here refl))
func {Ψ = atom x ∷ Ψ} (there f) = there $ func f
func {Ψ = code Γ DS CS ∷ Ψ} (there f)
  = there (there (there (func f)))
\end{code}
}

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

*   соответствующий этому блоку кода блок PLT, который является блоком кода
    того же типа, что и $f$;
*   элемент GOT, являющийся указателем на блок кода того же типа, что и $f$;
*   сам блок кода $f$.

В реальности таблицы PLT и GOT вынесены в отдельные секции и не
располагаются рядом с кодом, но мы не рассматриваем перестановку элементов
в памяти в целях простоты реализации.

Определенные дальше функции \F{plt}, \F{got} и \F{func} позволяют, зная, по
какому адресу находился блок кода $f$ в неслинкованной программе, определить,
по каким адресам будут расположены в слинкованной программе соответствующие
этому блоку кода элемент PLT $plt.f$, элемент GOT $got.f$ и сам блок кода
$f$ соответственно.

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

Как было указано ранее, блок PLT должен обеспечивать получение в рантайме
адреса пролинкованной внешней функции и передачу исполнения на этот адрес.
Простейший блок PLT выглядит следующим образом: используя указанный при
компиляции адрес соответствующей ему ячейки GOT, он исполняет инструкцию
непрямого перехода \C{jmp[\_]} на тот адрес, который записан в GOT. Так
как динамический загрузчик должен после загрузки библиотеки с нужной
функцией заполнить соответствующие ей элементы GOT, положив в них ее адрес,
исполнение указанного блока PLT будет приводить к исполнению самой функции.

Как было сказано в секции **TODO TAL review section reference**, последним
параметром типа блока является дифф над типом состояния исполнителя,
производимый этим блоком. В случае с блоком \F{plt-stub} это \C{dempty}:
пустое изменение состояния, потому что приведенный блок PLT ничего не
меняет. И это абсолютно правильно, потому что в противном случае вызов
функции через ее блок PLT не был бы прозрачным и менял бы семантику
программы.

\labeledfigure{fig:plt-stub}{Определение блока PLT}{
\begin{code}
plt-stub : ∀ {Γ Ψ DS CS}
         → atom (code Γ DS CS *) ∈ Ψ
         → Block (statetype Γ Ψ DS CS) dempty
plt-stub got = ↝ jmp[ got ]
\end{code}
}

\ignore{
\begin{code}
_++[_]++_ : ∀ {α} → {A : Set α} → (σs : List A) → (τ : A) → (τs : List A)
          → σs ++ τ ∷ τs ≡ (σs ++ [ τ ]) ++ τs
[] ++[ τ ]++ τs = refl
(σ ∷ σs) ++[ τ ]++ τs = cong (_∷_ σ) (σs ++[ τ ]++ τs)

pltize-++ : ∀ Γ Δ → pltize (Γ ++ Δ) ≡ pltize Γ ++ pltize Δ
pltize-++ [] Δ = refl
pltize-++ (atom τ ∷ Ψ) Δ rewrite pltize-++ Ψ Δ = refl
pltize-++ (code Γ DS CS ∷ Ψ) Δ rewrite pltize-++ Ψ Δ = refl

pltize-idata : ∀ Γ {Ψ} → IData (Γ ++ Ψ) Ψ → IData (pltize $ Γ ++ Ψ) (pltize Ψ)
pltize-idata Γ [] = []
pltize-idata Γ (_∷_ {atom τ} {τs} (atom x) Ψ)
  = (atom (pltize-atom x)) ∷ Ψ-tail
  where
    lemma : Γ ++ atom τ ∷ τs ≡ (Γ ++ [ atom τ ]) ++ τs
    lemma = Γ ++[ atom τ ]++ τs
    Ψ' : IData ((Γ ++ [ atom τ ]) ++ τs) τs
    Ψ' rewrite sym lemma = Ψ
    Ψ-tail : IData (pltize $ Γ ++ atom τ ∷ τs) (pltize τs)
    Ψ-tail rewrite lemma = pltize-idata (Γ ++ [ atom τ ]) Ψ'
pltize-idata Δ (_∷_ {code Γ DS CS} {τs} (block x) Ψ)
  = Values.block (plt-stub this-got)
  ∷ (Values.atom (Values.ptr this-func)
  ∷ (Values.block (pltize-block x)
  ∷ Ψ-tail))
  where
    lemma : Δ ++ code Γ DS CS ∷ τs ≡ (Δ ++ [ code Γ DS CS ]) ++ τs
    lemma = Δ ++[ code Γ DS CS ]++ τs
    Ψ' : IData ((Δ ++ [ code Γ DS CS ]) ++ τs) τs
    Ψ' rewrite sym lemma = Ψ
    Ψ-tail : IData (pltize $ Δ ++ code Γ DS CS ∷ τs) (pltize τs)
    Ψ-tail rewrite lemma = pltize-idata (Δ ++ [ code Γ DS CS ]) Ψ'
    this-got : atom (code Γ DS CS *) ∈ (pltize $ Δ ++ code Γ DS CS ∷ τs)
    this-got rewrite pltize-++ Δ (code Γ DS CS ∷ τs)
      = ++ʳ (pltize Δ) {pltize $ code Γ DS CS ∷ τs} (there (here refl))
    this-func : code Γ DS CS ∈ (pltize $ Δ ++ code Γ DS CS ∷ τs)
    this-func rewrite pltize-++ Δ (code Γ DS CS ∷ τs)
      = ++ʳ (pltize Δ) {pltize $ code Γ DS CS ∷ τs} (here refl)

pltize-data : ∀ {Ψ} → Data Ψ → Data (pltize Ψ)
pltize-data = pltize-idata []

dynamic : ∀ {ST} → Program ST → Program (pltize-state ST)
dynamic (program memory start)
  -- TODO: replace every `call f` with `call (plt f)`
  = program (pltize-data memory) (func start)
\end{code}
}
