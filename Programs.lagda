## Programs

\ignore{
\begin{code}
module Programs where

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

We will think of program as of binary loaded to memory. Due to this
assumption we can ignore memory mapping problems. With this assumption, we
can say that *program* is pair of memory state (with code and data) and
start block.

\begin{code}
record Program (ST : StateType) : Set where
  constructor program
  field
    memory : Data (StateType.memory ST)
    start  : IPRT (StateType.memory ST)
                  (StateType.registers ST)
                  (StateType.datastack ST)
                  (StateType.callstack ST)
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

## Компоновка кода

Преобразование памяти определяется аналогично приведенному в первой
реализации.  Все, кроме блоков, остается неизменным, а на каждый блок
дополнительно добавляются элементы PLT и GOT.

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

Зная, по какому адресу находилась функция в памяти без GOT и PLT, можно
получить адреса в измененной памяти для:

*   соответствующего этой функции элемента PLT;

\begin{code}
plt : ∀ {Γ Ψ DS CS} → block Γ DS CS ∈ Ψ
    → block Γ DS CS ∈ pltize Ψ
plt (here refl) = here refl
plt {Ψ = atom x ∷ Ψ} (there f) = there $ plt f
plt {Ψ = block Γ DS CS ∷ Ψ} (there f)
  = there (there (there (plt f)))
\end{code}

*   соответствующего этой функции элемента GOT;

\begin{code}
got : ∀ {Γ Ψ DS CS} → block Γ DS CS ∈ Ψ
    → atom (block Γ DS CS *) ∈ pltize Ψ
got (here refl) = there (here refl)
got {Ψ = atom x ∷ Ψ} (there f) = there $ got f
got {Ψ = block Γ DS CS ∷ Ψ} (there f)
  = there (there (there (got f)))
\end{code}

*   самой функции.

\begin{code}
func : ∀ {Γ Ψ DS CS} → block Γ DS CS ∈ Ψ
    → block Γ DS CS ∈ pltize Ψ
func (here refl) = there (there (here refl))
func {Ψ = atom x ∷ Ψ} (there f) = there $ func f
func {Ψ = block Γ DS CS ∷ Ψ} (there f)
  = there (there (there (func f)))

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

pltize-diff : ∀ {ST} → Diff ST → Diff (pltize-state ST)
pltize-diff (diff rdiff dsdiff csdiff) = diff rdiff dsdiff csdiff

postulate
  pltize-block : ∀ {ST d} → Block ST d → Block (pltize-state ST) (pltize-diff d)

{-
pltize-block : ∀ {ST d} → Block ST d → Block (pltize-state ST) (pltize-diff d)
pltize-block (Blocks.↝ x) = {!!}
pltize-block (x Blocks.∙ b) = {!!}
-}
\end{code}

Блок PLT выглядит так же, как и в первой реализации.

\begin{code}
plt-stub : ∀ {Γ Ψ DS CS} → atom (block Γ DS CS *) ∈ Ψ
         → Block (statetype Γ Ψ DS CS) dempty
plt-stub got = ↝ jmp[ got ]

_++[_]++_ : ∀ {α} → {A : Set α} → (σs : List A) → (τ : A) → (τs : List A)
          → σs ++ τ ∷ τs ≡ (σs ++ [ τ ]) ++ τs
[] ++[ τ ]++ τs = refl
(σ ∷ σs) ++[ τ ]++ τs = cong (_∷_ σ) (σs ++[ τ ]++ τs)

postulate
  pltize-idata : ∀ Γ {Ψ} → IData (Γ ++ Ψ) Ψ → IData (pltize $ Γ ++ Ψ) (pltize Ψ)

{-
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
  = Values.block (plt-stub {!!})
  ∷ (Values.atom (Values.ptr {!!})
  ∷ (Values.block (pltize-block x)
  ∷ Ψ-tail))
  where
    lemma : Δ ++ block Γ DS CS ∷ τs ≡ (Δ ++ [ block Γ DS CS ]) ++ τs
    lemma = Δ ++[ block Γ DS CS ]++ τs
    Ψ' : IData ((Δ ++ [ block Γ DS CS ]) ++ τs) τs
    Ψ' rewrite sym lemma = Ψ
    Ψ-tail : IData (pltize $ Δ ++ block Γ DS CS ∷ τs) (pltize τs)
    Ψ-tail rewrite lemma = pltize-idata (Δ ++ [ block Γ DS CS ]) Ψ'
-}

pltize-data : ∀ {Ψ} → Data Ψ → Data (pltize Ψ)
pltize-data = pltize-idata []
\end{code}

Опишем важное свойство: элемент GOT корректно заполнен, если в нём
действительно находится указатель на соответствующую этому элементу
функцию.

\begin{code}
GOT[_]-correctness : ∀ {Γ Ψ DS CS}
                   → (f : block Γ DS CS ∈ Ψ)
                   → (H : Data (pltize Ψ))
                   → Set
GOT[ f ]-correctness H = loadptr H (got f) ≡ func f
\end{code}

## Доказательства

Для доказательства эквивалентности вызовов функции и соответствующего ей
элемента PLT потребуются несколько лемм:

*   состояние исполнителя в момент непосредственного вызова функции
    эквивалентно состоянию исполнителя после исполнения непрямого `jmp`
    по указателю на ее тело;

\begin{code}
exec-ijmp : ∀ {ST} → (S : State ST)
          → (p : atom (block
               (StateType.registers ST)
               (StateType.datastack ST)
               (StateType.callstack ST)
             *) ∈ StateType.memory ST)
          → exec-block S (↝ jmp[ p ])
          ≡ S
          , loadblock
            (State.memory S)
            (loadptr (State.memory S) p)
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
         ≡ S , loadblock (State.memory S) (func f)
exec-plt f S p rewrite sym p = exec-ijmp S (got f)
\end{code}

Используя эти леммы, можно доказать, что если GOT заполнен корректно,
то верна внешняя эквивалентность блока PLT, использующего соответствующий
функции элемент GOT, и самой функции:

\begin{code}
proof : ∀ {Γ Ψ DS CS}
      → (f : block Γ DS CS ∈ Ψ)
      → (S : State (statetype Γ (pltize Ψ) DS CS))
      → GOT[ f ]-correctness (State.memory S)
      → BlockEq S S
        (plt-stub (got f))
        (proj₂ $ loadblock (State.memory S) (func f))
proof f S p = left (exec-plt f S p) equal
\end{code}
