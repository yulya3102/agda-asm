# Линковка

В этой статье не рассматриваются объектные файлы и программы как таковые.
Я рассматриваю только ABI программы целиком, а о нем можно рассуждать и без
разбиения программы на разные библиотеки. Основной поинт в том, что линкер
меняет код программы не просто заполнением релокаций, как в статической
линковке, но и добавляет какой-то свой код, позволяющий эффективно делать
это в рантайме. В этом разделе описывается, какой именно код добавляет
линкер в программу, и почему это работает.

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

Линкер генерирует в коде две таблицы: GOT (global offset table) и PLT
(procedure linkage table), в первой хранятся указатели на код, заполняемые
в рантайме, а вторая содержит блоки кода. На каждую внешнюю функцию в GOT и
PLT добавляется по одному элементу: в GOT добавляется ячейка, в которую
динамический загрузчик после загрузки бинарного файла положит адрес
пролинкованной функции, а в PLT добавляется блок кода, который будет
вызываться использоваться в этом бинанике вместо самой функции.

Так как в этой реализации на самом деле нет никакого разделения на
бинарники, а значит, и внешних функций тоже, то записи GOT и PLT
генерируются на каждый блок кода. Функция `pltize` показывает, как
динамический линковщик меняет layout памяти, добавляя в него новые
элементы: вместо каждого блока кода исходной программы в слинкованной
программе будет целых три элемента в памяти: соответствующий этому блоку
кода блок PLT (блок кода того же типа), элемент GOT (указатель на блок кода
того же типа, что и блок PLT) и сам блок кода. В реальной жизни таблицы PLT
и GOT сгруппированы в одном месте и не располагаются рядом с реальным
кодом, но мы не рассматриваем перестановку элементов в памяти в целях
простоты реализации.

Определенные дальше функции `plt`, `got` и `func` позволяют, зная, по
какому адресу находился блок кода в неслинкованной программе, определить,
по каким адресам будут расположены в слинкованной программе соответствующие
этому блоку кода элементы PLT, GOT и сам блок кода соответственно.

\begin{code}
pltize : DataType → DataType
pltize [] = []
pltize (atom x ∷ Ψ) = atom x ∷ pltize Ψ
pltize (block Γ DS CS ∷ Ψ)
  = block Γ DS CS
  ∷ (atom (block Γ DS CS *)
  ∷ (block Γ DS CS
  ∷ pltize Ψ))
\end{code}

\begin{code}
plt : ∀ {Γ Ψ DS CS} → block Γ DS CS ∈ Ψ
    → block Γ DS CS ∈ pltize Ψ
plt (here refl) = here refl
plt {Ψ = atom x ∷ Ψ} (there f) = there $ plt f
plt {Ψ = block Γ DS CS ∷ Ψ} (there f)
  = there (there (there (plt f)))
\end{code}

\begin{code}
got : ∀ {Γ Ψ DS CS} → block Γ DS CS ∈ Ψ
    → atom (block Γ DS CS *) ∈ pltize Ψ
got (here refl) = there (here refl)
got {Ψ = atom x ∷ Ψ} (there f) = there $ got f
got {Ψ = block Γ DS CS ∷ Ψ} (there f)
  = there (there (there (got f)))
\end{code}

\begin{code}
func : ∀ {Γ Ψ DS CS} → block Γ DS CS ∈ Ψ
    → block Γ DS CS ∈ pltize Ψ
func (here refl) = there (there (here refl))
func {Ψ = atom x ∷ Ψ} (there f) = there $ func f
func {Ψ = block Γ DS CS ∷ Ψ} (there f)
  = there (there (there (func f)))
\end{code}

\ignore{
\begin{code}
pltize-ptr : ∀ {Ψ τ} → τ ∈ Ψ → τ ∈ pltize Ψ
pltize-ptr {[]} ()
pltize-ptr {_ ∷ Ψ} {atom _}      (here refl) = here refl
pltize-ptr {_ ∷ Ψ} {block _ _ _} (here refl) = here refl
pltize-ptr {atom _ ∷ Ψ}          (there px)  = there (pltize-ptr px)
pltize-ptr {block _ _ _ ∷ Ψ}     (there px)  = there (there (there (pltize-ptr px)))

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

Блок PLT выглядит следующим образом: используя данный ему адрес GOT,
он делает `indirect jump` на тот адрес, который записан в GOT. Динамический
загрузчик должен после загрузки библиотеки с нужной функцией заполнить
соответствующие ей элементы GOT, положив в них ее адрес. Тогда исполнение
блока PLT будет приводить к исполнению самой функции. `dempty` в последнем
параметре типа блока указывает на то, что этот блок никак не изменяет
состояние исполнителя.

\begin{code}
plt-stub : ∀ {Γ Ψ DS CS}
         → atom (block Γ DS CS *) ∈ Ψ
         → Block (statetype Γ Ψ DS CS) dempty
plt-stub got = ↝ jmp[ got ]
\end{code}

\ignore{
\begin{code}
_++[_]++_ : ∀ {α} → {A : Set α} → (σs : List A) → (τ : A) → (τs : List A)
          → σs ++ τ ∷ τs ≡ (σs ++ [ τ ]) ++ τs
[] ++[ τ ]++ τs = refl
(σ ∷ σs) ++[ τ ]++ τs = cong (_∷_ σ) (σs ++[ τ ]++ τs)

pltize-++ : ∀ Γ Δ → pltize (Γ ++ Δ) ≡ pltize Γ ++ pltize Δ
pltize-++ [] Δ = refl
pltize-++ (atom τ ∷ Ψ) Δ rewrite pltize-++ Ψ Δ = refl
pltize-++ (block Γ DS CS ∷ Ψ) Δ rewrite pltize-++ Ψ Δ = refl

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
pltize-idata Δ (_∷_ {block Γ DS CS} {τs} (block x) Ψ)
  = Values.block (plt-stub this-got)
  ∷ (Values.atom (Values.ptr this-func)
  ∷ (Values.block (pltize-block x)
  ∷ Ψ-tail))
  where
    lemma : Δ ++ block Γ DS CS ∷ τs ≡ (Δ ++ [ block Γ DS CS ]) ++ τs
    lemma = Δ ++[ block Γ DS CS ]++ τs
    Ψ' : IData ((Δ ++ [ block Γ DS CS ]) ++ τs) τs
    Ψ' rewrite sym lemma = Ψ
    Ψ-tail : IData (pltize $ Δ ++ block Γ DS CS ∷ τs) (pltize τs)
    Ψ-tail rewrite lemma = pltize-idata (Δ ++ [ block Γ DS CS ]) Ψ'
    this-got : atom (block Γ DS CS *) ∈ (pltize $ Δ ++ block Γ DS CS ∷ τs)
    this-got rewrite pltize-++ Δ (block Γ DS CS ∷ τs)
      = ++ʳ (pltize Δ) {pltize $ block Γ DS CS ∷ τs} (there (here refl))
    this-func : block Γ DS CS ∈ (pltize $ Δ ++ block Γ DS CS ∷ τs)
    this-func rewrite pltize-++ Δ (block Γ DS CS ∷ τs)
      = ++ʳ (pltize Δ) {pltize $ block Γ DS CS ∷ τs} (here refl)

pltize-data : ∀ {Ψ} → Data Ψ → Data (pltize Ψ)
pltize-data = pltize-idata []

dynamic : ∀ {ST} → Program ST → Program (pltize-state ST)
dynamic (program memory start)
  -- TODO: replace every `call f` with `call (plt f)`
  = program (pltize-data memory) (func start)
\end{code}
}

Доказательство эквивалентности блоков PLT и соответствующих им функций
опирается на предположения о том, что динамический загрузчик добросовестно
выполняет свою работу. Предположение `GOT[ f ]-correctness` утверждает, что
в элементе GOT, соответстующем функции f, находится адрес f, а
предположение `PLT[ f ]-correctness` утверждает, что по адресу,
соответствующему нужному блоку PLT, действительно находится блок PLT.

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
exec-ijmp (state Γ Ψ DS CS) p = refl
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

Хотелось бы еще сюда засунуть формализованное определение и доказательство
эквивалентности программ, а то пока я умею только махать руками на эту тему

\begin{code}
-- TODO: program equivalence
\end{code}
