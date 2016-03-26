## Introduction

???

??? how-hard-memory-management-can-be ??? However, discussed in this
paper properties of dynamic linking does not require dynamic memory
management. Keeping that in mind, we can assume that all memory is static
and no allocation is taken.

## ??? (why and how)

???: should it be all-detailed typecheckable paper or
overview-with-key-ideas and some formalizations

## Typed assembly language definition

\ignore{
\begin{code}
module Functions where

open import Data.Nat
open import Data.List
open import Data.List.Any
open Membership-≡
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Function
\end{code}
}

### Machine state types

TODO: write somewhere about different sizeof(type) for different types

There are three common parts of machine state used in assembly languages:
registers, memory and stack. Although stack is usually appears to be part
of memory, it has one important aspect that makes stack a separate concept.

In our model memory doesn't support dynamic allocation and statically
allocated for every object that needs it. But memory on stack is actually
dynamically allocated, and stack objects lifetime may differ from program
lifetime. Therefore, address pointing to some place in stack can point to
different objects of different types during the program lifetime. However,
memory allocation on stack is done with very simple algorithm: just
increment or decrement stack pointer until you reach stack limit. Its
simplicity allows us to forget hard memory allocation problems and
implement stack as another part of machine state with two operations:
allocating some memory of given type on top of it and freeing the memory on
top of it. We could also assume that stack can grow indefinitely and memory
is not limited, but that's not necessary since we only care for small part
of program lifetime that allocates finite amount of stack memory needed to
run allocator at most ??? times.

TODO: memory, registers and stacks definition (types)

???: RegType/Type difference does not really matter

\begin{code}
data RegType : Set

RegTypes = List RegType

data Type : Set

DataType = List Type
\end{code}

There is another difficulty in stack definition. Stack actually serves for
two purposes: tracking return addresses and saving stack frames with local
variables. These two purposes are similar, but for type system they are
quite different. For local variables it only should only check ???, but for
return address it should make sure that `ret` is executed only in suitable
machine state. So, in our model there will be two different stacks: call
stack and data stack.

TODO: callstacktype should refer to itself, but that's not problem

TODO: callstacktype and datastacktype definitions

\begin{code}
DataStackType : Set
CallStackType : Set
\end{code}

\begin{code}
DataStackType = List RegType
\end{code}

\begin{code}
CallStackType = List (RegTypes × DataStackType)
\end{code}

\ignore{
\begin{code}
record StateType : Set where
  constructor statetype
  field
    registers : RegTypes
    memory    : DataType
    datastack : DataStackType
    callstack : CallStackType
\end{code}

\begin{code}
data RegType where
  _*  : Type → RegType
  int : RegType
\end{code}

\begin{code}
data Type where
  atom : RegType → Type
  block : RegTypes → DataStackType → CallStackType → Type
\end{code}
}

\ignore{
\begin{code}
data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A
\end{code}
}

### Meta-assembler

TODO: reusable agda code is nice

Actual assembler code has to know exact instruction set, it wouldn't make
much sense to write any code without any knowledge about instructions. On
the other hand, any assembler code can be represented as a sequence of
basic blocks (?), and other concepts can be defined using basic blocks
definition. Using this method, concepts like memory and registers can have
block type as parameter and don't depend on instruction set directly. This
helps to keep code much more generic.

\ignore{
\begin{code}
module Diffs where
\end{code}
}

To statically analyze types of different parts of machine state we need to
know how blocks change them. For us to do this, type of block needs to have
information about changes of machine state types applied by the block.

TODO: diffs definition

TODO: block definition

TODO: memory, registers and stacks definition

Определим тип, описывающий одно изменение списка фиксированной длины:
в таком списке можно только менять элементы, что и требуется от регистров.
Так как не любое изменение можно применить к произвольному списку, его
тип должен ограничивать, к какому списку его можно применять.

\begin{code}
  module ListChg (A : Set) where
    data Chg (Γ : List A) : Set where
\end{code}

Для того, чтобы описать изменение элемента в списке, необходимо указать,
какая позиция меняется и на что.

\begin{code}
      chg : ∀ {τ} → τ ∈ Γ → A → Chg Γ
\end{code}

Сами по себе изменения не несут особого смысла: необходимо указать, как
они применяются к спискам.

\begin{code}
    chgapply : (Γ : List A) → Chg Γ → List A
    chgapply (_ ∷ Γ) (chg (here refl) σ) = σ ∷ Γ
    chgapply (τ ∷ Γ) (chg (there p)   σ) = τ ∷ chgapply Γ (chg p σ)
\end{code}

Блок кода последовательно применяет изменения к списку регистров,
значит, в его типе должен быть описан набор изменений.

Набор изменений является общим для изменений различных видов. То, к чему
применяется изменение, будем называть _контекстом_.

\begin{code}
  module DiffDefinition
    {Ctx : Set}
    {Chg : Ctx → Set}
    (chgapply : (Γ : Ctx) → Chg Γ → Ctx)
    where
\end{code}

Так же, как и для изменения, тип набора изменений ограничивает контекст, к
которому его можно применять.

\begin{code}
    data Diff (Γ : Ctx) : Set where
\end{code}

Набор изменений — это:

*   либо пустой набор;

\begin{code}
      dempty  : Diff Γ
\end{code}

*   либо это изменение, добавленное перед уже имеющимся набором.

\begin{code}
      dchg    : (c : Chg Γ) → Diff (chgapply Γ c) → Diff Γ
\end{code}

Для набора изменений определены несколько функций:

*   применение набора к контексту — это последовательное применение всех
    изменений из набора;

\begin{code}
    dapply : (Γ : Ctx) → Diff Γ → Ctx
    dapply Γ dempty = Γ
    dapply Γ (dchg c d) = dapply (chgapply Γ c) d
\end{code}

*   объединение двух наборов изменений;

\begin{code}
    dappend : ∀ {Γ} → (d : Diff Γ)
            → Diff (dapply Γ d) → Diff Γ
    dappend dempty b = b
    dappend (dchg c a) b = dchg c (dappend a b)
\end{code}

*   лемма, доказывающая, что объединение с пустым набором не меняет набор;

\begin{code}
    dappend-dempty-lemma : ∀ {Γ} → (d : Diff Γ)
                         → dappend d dempty ≡ d
    dappend-dempty-lemma dempty = refl
    dappend-dempty-lemma (dchg c d)
      rewrite dappend-dempty-lemma d = refl
\end{code}

*   лемма, доказывающая, что применение объединения наборов эквивалентно
    последовательному применению этих наборов.

\begin{code}
    dappend-dapply-lemma : ∀ S → (d₁ : Diff S)
                         → (d₂ : Diff (dapply S d₁))
                         → dapply S (dappend d₁ d₂)
                         ≡ dapply (dapply S d₁) d₂
    dappend-dapply-lemma S dempty d₂ = refl
    dappend-dapply-lemma S (dchg c d₁) d₂
      = dappend-dapply-lemma (chgapply S c) d₁ d₂
\end{code}

Определение изменений для регистров используется из предыдущих реализаций.

\begin{code}
  module RegDiff where

    open ListChg RegType public
    open DiffDefinition chgapply public
\end{code}

В отличие от предыдущих реализаций, в тип инструкций должны входить и стек
вызовов, и стек данных. Это означает, что для них необходимо определить
наборы изменений.

\begin{code}
  module StackDiff (A : Set) where
    data Chg (S : List A) : Set where
\end{code}

Возможными изменениями стека являются:

*   добавление значения на вершину стека;

\begin{code}
      push : (i : A) → Chg S
\end{code}

*   снятие значения с вершины стека, если стек не пуст.

\begin{code}
      pop  : ∀ {Γ S'} → S ≡ Γ ∷ S' → Chg S
\end{code}

Определим, как изменения применяются к стеку, и используем определенный
ранее тип набора изменений.

\begin{code}
    chgapply : (S : List A) → Chg S → List A
    chgapply cs (push x) = x ∷ cs
    chgapply (._ ∷ S') (pop refl) = S'

    open DiffDefinition chgapply public
\end{code}

Общим набором изменений состояния исполнителя будет являться структура,
описывающая изменения регистров и двух стеков.

\begin{code}
  record Diff (S : StateType) : Set where
    constructor diff
    field
      rdiff  : RegDiff.Diff (StateType.registers S)
      dsdiff : StackDiff.Diff RegType (StateType.datastack S)
      csdiff : StackDiff.Diff (RegTypes × DataStackType)
               (StateType.callstack S)
  open Diff public
\end{code}

Определим вспомогательные функции и типы для конструирования и применения
изменений состояния исполнителя:

*   конструирование пустого набора изменений;

\begin{code}
  dempty : ∀ {S} → Diff S
  dempty = diff
    RegDiff.dempty
    StackDiff.dempty
    StackDiff.dempty
\end{code}

*   применение набора изменений к состоянию исполнителя;

\begin{code}
  dapply : (S : StateType) → Diff S → StateType
  dapply (statetype r m d c) (diff rd dd cd) =
      statetype
      (RegDiff.dapply r rd)
      m
      (StackDiff.dapply RegType d dd)
      (StackDiff.dapply (RegTypes × DataStackType) c cd)
\end{code}

*   объединение двух наборов изменений;

\begin{code}
  dappend : ∀ {S} → (d : Diff S) → Diff (dapply S d) → Diff S
  dappend (diff rd dd cd) (diff rd' dd' cd') =
      diff
      (RegDiff.dappend rd rd')
      (StackDiff.dappend RegType dd dd')
      (StackDiff.dappend (RegTypes × DataStackType) cd cd')
\end{code}

*   изменение стека данных;

\begin{code}
  DataStackChg : StateType → Set
  DataStackChg S
    = StackDiff.Chg RegType (StateType.datastack S)
\end{code}

*   изменение стека вызовов;

\begin{code}
  CallStackChg : StateType → Set
  CallStackChg S
    = StackDiff.Chg
      (RegTypes × DataStackType)
      (StateType.callstack S)
\end{code}

*   изменение набора регистров;

\begin{code}
  RegChg : StateType → Set
  RegChg S = RegDiff.Chg (StateType.registers S)
\end{code}

*   изменение, производимое инструкцией: одна инструкция может изменить
    либо регистры, либо стек, либо и то, и другое (например, при `pop`
    значения со стека в регистр);

\begin{code}
  data SmallChg (S : StateType) : Set where
    onlyreg   : RegChg S → SmallChg S
    onlystack : DataStackChg S → SmallChg S
    regstack  : RegChg S → DataStackChg S → SmallChg S
\end{code}

*   конструирование набора изменений состояния исполнителя по одному
    изменению регистров;

\begin{code}
  regChg : ∀ {S} → RegChg S → Diff S
  regChg c =
      diff
      (RegDiff.dchg c RegDiff.dempty)
      StackDiff.dempty
      StackDiff.dempty
\end{code}

*   конструирование набора изменений состояния исполнителя по одному
    изменению стека данных;

\begin{code}
  dsChg : ∀ {S} → DataStackChg S → Diff S
  dsChg c =
    diff
    RegDiff.dempty
    (StackDiff.dchg c StackDiff.dempty)
    StackDiff.dempty
\end{code}

*   конструирование набора изменений состояния исполнителя по одному
    изменению, производимому инструкцией;

\begin{code}
  sChg : ∀ {S} → SmallChg S → Diff S
  sChg (onlyreg r) = regChg r
  sChg (onlystack d) = dsChg d
  sChg (regstack r d) =
    diff
    (RegDiff.dchg r RegDiff.dempty)
    (StackDiff.dchg d StackDiff.dempty)
    StackDiff.dempty
\end{code}

*   конструирование набора изменений состояния исполнителя по одному
    возможному изменению стека вызовов.

\begin{code}
  csChg : ∀ S → Maybe (CallStackChg S) → Diff S
  csChg S nothing = dempty
  csChg S (just c) =
      diff
      RegDiff.dempty
      StackDiff.dempty
      (StackDiff.dchg c StackDiff.dempty)
\end{code}

## Метаассемблер

Аналогично приведенному в предыдущей главе, метаассемблер состоит из
четырех модулей.

\ignore{
\begin{code}
module Meta where
  open Diffs
\end{code}
}

### Модуль Blocks

Ранее управляющие инструкции описывали только состояние исполнителя,
требуемое для выполнения инструкции. С добавлением в состояние исполнителя
стека вызовов становится возможным описание изменений, производимых
управляющей инструкцией. По типу управляющей инструкции видно, что в
результате исполнения может измениться только, возможно, стек
вызовов. <!--- и это очень няшно -->

Тип инструкции тоже задает, какие части состояния исполнителя он может
изменить: это либо регистры, либо стек данных, либо и то, и то.

\begin{code}
  module Blocks
    (ControlInstr : (S : StateType)
                  → Maybe (CallStackChg S)
                  → Set)
    (Instr : (S : StateType) → SmallChg S → Set)
    where
\end{code}

Определение блока аналогично приведенному ранее.

\begin{code}
    data Block (S : StateType) : Diff S → Set where
      ↝ : ∀ {c} → ControlInstr S c → Block S (csChg S c)
      _∙_ : ∀ {c d}
           → Instr S c
           → Block (dapply S (sChg c)) d
           → Block S (dappend (sChg c) d)
\end{code}

### Модуль Values

\begin{code}
  module Values
    (Block : (S : StateType) → Diff S → Set)
    where
\end{code}

Определения значений аналогичны используемым ранее, но поделены на два
класса, соответствующие значениям размера регистра и значениям
произвольного размера.

\begin{code}
    data RegValue (Ψ : DataType) : RegType → Set where
      ptr : ∀ {τ} → τ ∈ Ψ → RegValue Ψ (τ *)
      int : ℕ → RegValue Ψ int

    data Value (Ψ : DataType) : Type → Set where
      atom : ∀ {τ} → RegValue Ψ τ → Value Ψ (atom τ)
      block : ∀ {Γ DS CS d}
            → Block (statetype Γ Ψ DS CS) d
            → Value Ψ (block Γ DS CS)
\end{code}

Определим вспомогательные функции для работы со значениями:

*   получение блока из значения типа `block`;

\begin{code}
    unblock : ∀ {Ψ Γ DS CS} → Value Ψ (block Γ DS CS)
            → Σ (Diff (statetype Γ Ψ DS CS))
                (Block (statetype Γ Ψ DS CS))
    unblock (block b) = _ , b
\end{code}

*   получение указателя на `τ` из значения типа `τ *`.

\begin{code}
    unptr : ∀ {Ψ τ} → Value Ψ (atom (τ *)) → τ ∈ Ψ
    unptr (atom (ptr x)) = x
\end{code}

Определение набора регистров аналогично приведенному ранее.

\begin{code}
    data Registers (Ψ : DataType) : RegTypes → Set where
      []  : Registers Ψ []
      _∷_ : ∀ {τ τs}
          → RegValue Ψ τ
          → Registers Ψ τs
          → Registers Ψ (τ ∷ τs)
\end{code}

Определим вспомогательные функции для работы с регистрами:

*   загрузка значения из заданного регистра;

\begin{code}
    fromreg : ∀ {Ψ Γ τ} → Registers Ψ Γ → τ ∈ Γ → RegValue Ψ τ
    fromreg (x ∷ Γ) (here refl) = x
    fromreg (x ∷ Γ) (there p) = fromreg Γ p
\end{code}

*   запись значения в заданный регистр.

\begin{code}
    toreg : ∀ {Ψ Γ σ τ}
          → Registers Ψ Γ
          → (r : σ ∈ Γ)
          → RegValue Ψ τ
          → Registers Ψ (RegDiff.chgapply Γ (RegDiff.chg r τ))
    toreg (x ∷ Γ) (here refl) v = v ∷ Γ
    toreg (x ∷ Γ) (there r) v = x ∷ (toreg Γ r v)
\end{code}

Состояние памяти определяется аналогично приведенному ранее.

\begin{code}
    data IData (Ψ : DataType) : DataType → Set where
      []  : IData Ψ []
      _∷_ : ∀ {τ τs} → Value Ψ τ → IData Ψ τs → IData Ψ (τ ∷ τs)

    Data : DataType → Set
    Data Ψ = IData Ψ Ψ

    load : ∀ {Ψ τ} → Data Ψ → τ ∈ Ψ → Value Ψ τ
    load {Ψ} {τ} = iload
      where
      iload : ∀ {Γ} → IData Ψ Γ → τ ∈ Γ → Value Ψ τ
      iload [] ()
      iload (x ∷ H) (here refl) = x
      iload (x ∷ H) (there p) = iload H p
\end{code}

Определим вспомогательные функции для работы с памятью:

*   загрузка блока кода из памяти по указателю на блок;

\begin{code}
    loadblock : ∀ {Ψ Γ CS DS} → Data Ψ → block Γ DS CS ∈ Ψ
             → Σ (Diff (statetype Γ Ψ DS CS))
                 (Block (statetype Γ Ψ DS CS))
    loadblock Ψ f = unblock $ load Ψ f
\end{code}

*   загрузка указателя на `τ` из памяти по указателю на `τ *`.

\begin{code}
    loadptr : ∀ {Ψ τ} → Data Ψ → atom (τ *) ∈ Ψ → τ ∈ Ψ
    loadptr Ψ p = unptr $ load Ψ p
\end{code}

Стек данных — список значений размера регистра, в типе которого указано,
значения каких типов в нем находятся.

\begin{code}
    data DataStack (Ψ : DataType) : List RegType → Set
      where
      []   : DataStack Ψ []
      _∷_  : ∀ {τ DS} → RegValue Ψ τ
           → DataStack Ψ DS
           → DataStack Ψ (τ ∷ DS)
\end{code}

Типизированный instruction pointer — указатель на блок кода в памяти.

\begin{code}
    IPRT : DataType
         → RegTypes
         → DataStackType
         → CallStackType
         → Set
    IPRT Ψ Γ DS CS = block Γ DS CS ∈ Ψ
\end{code}

Стек вызовов — список типизированных instruction pointer-ов.  Ранее было
описано, почему в типе стека вызовов не указывается требуемое блоком
состояние стека вызовов.

\begin{code}
    data CallStack (Ψ : DataType) : CallStackType → Set where
      []  : CallStack Ψ []
      _∷_ : ∀ {Γ DS CS} → IPRT Ψ Γ DS CS → CallStack Ψ CS
          → CallStack Ψ ((Γ , DS) ∷ CS)
\end{code}

Состояние исполнителя — совокупность состояний регистров, памяти и стеков.

\begin{code}
    record State (S : StateType) : Set where
      constructor state
      field
        registers : Registers
                    (StateType.memory S)
                    (StateType.registers S)
        memory    : Data (StateType.memory S)
        datastack : DataStack
                    (StateType.memory S)
                    (StateType.datastack S)
        callstack : CallStack
                    (StateType.memory S)
                    (StateType.callstack S)
\end{code}

### Модуль ExecBlk

\begin{code}
  module ExecBlk
\end{code}

Сигнатуры инструкций и управляющих инструкций были описаны ранее.

\begin{code}
    (Instr : (S : StateType) → Diffs.SmallChg S → Set)
    (ControlInstr : (S : StateType)
                  → Maybe (Diffs.CallStackChg S)
                  → Set)
\end{code}

Результат исполнения инструкции заивисит от состояния исполнителя и
определяет, как изменятся регистры, память и стек данных.

\begin{code}
    (exec-instr : ∀ {S c}
                → Values.State
                  (Blocks.Block ControlInstr Instr)
                  S
                → Instr S c
                → Values.Registers
                 (Blocks.Block ControlInstr Instr)
                 (StateType.memory S)
                 (StateType.registers
                   (Diffs.dapply S (Diffs.sChg c)))
                × (Values.Data
                  (Blocks.Block ControlInstr Instr)
                  (StateType.memory S)
                × Values.DataStack
                 (Blocks.Block ControlInstr Instr)
                 (StateType.memory S)
                 (StateType.datastack
                   (Diffs.dapply S (Diffs.sChg c)))))
\end{code}

Результат исполнения управляющей инструкции тоже зависит от состояния
исполнителя и определяет, как изменится стек вызовов и какой блок будет
исполняться следующим.

\begin{code}
    (exec-control : ∀ {S c}
                 → Values.State
                   (Blocks.Block ControlInstr Instr)
                   S
                 → ControlInstr S c
                 → Values.CallStack
                  (Blocks.Block ControlInstr Instr)
                  (StateType.memory S)
                  (StateType.callstack
                    (Diffs.dapply S (Diffs.csChg S c)))
                 × Σ (Diffs.Diff
                       (Diffs.dapply S (Diffs.csChg S c)))
                     (Blocks.Block ControlInstr Instr
                       (Diffs.dapply S (Diffs.csChg S c))))
    where
    open Diffs
    open Blocks ControlInstr Instr
    open Values Block
\end{code}

Для определения функции `exec-block` потребовалось определить несколько
лемм:

\ignore{
\begin{code}
    module DiffLemmas where
\end{code}
}

*   если набор изменений состояния исполнителя построен как набор изменений
    стека вызовов, то набор изменений регистров пуст;

\begin{code}
      reg-const : ∀ S → (c : Maybe (CallStackChg S))
                → rdiff (csChg S c) ≡ RegDiff.dempty
      reg-const S (just c) = refl
      reg-const S nothing = refl
\end{code}

*   если набор изменений состояния исполнителя построен как набор изменений
    стека вызовов, то набор изменений стека данных пуст;

\begin{code}
      ds-const : ∀ S → (c : Maybe (CallStackChg S))
               → dsdiff (csChg S c) ≡ StackDiff.dempty
      ds-const S (just x) = refl
      ds-const S nothing = refl
\end{code}

*   если набор изменений состояния исполнителя построен как набор
    изменений, производимых инструкцией, то набор изменений стека вызовов
    пуст;

\begin{code}
      cs-lemma : ∀ S → (c : SmallChg S)
               → csdiff (sChg c) ≡ StackDiff.dempty
      cs-lemma S (onlyreg x) = refl
      cs-lemma S (onlystack x) = refl
      cs-lemma S (regstack x x₁) = refl
\end{code}

*   применение набора изменений, построенных как набор изменений стека
    вызовов, к состоянию исполнителя изменяет только стек вызовов, оставляя
    остальное неизменным.

\begin{code}
      dapply-csChg : ∀ S → (c : Maybe (CallStackChg S))
                   → dapply S (csChg S c)
                   ≡ statetype
                    (StateType.registers S)
                    (StateType.memory S)
                    (StateType.datastack S)
                    (StackDiff.dapply (RegTypes × DataStackType)
                      (StateType.callstack S) (csdiff (csChg S c)))
      dapply-csChg S (just x) = refl
      dapply-csChg S nothing = refl
\end{code}

\ignore{
\begin{code}
    open DiffLemmas
\end{code}
}

Проблемой предыдущей реализации было то, что для некоторых блоков важно
было их расположение в памяти, из-за чего определить, какой блок будет
исполняться следующим, не всегда представлялось возможным. Если
потребовать, чтобы все управляющие инструкции задавали явно все требуемые
значения, не рассчитывая на определенное расположение в памяти, проблема не
будет возникать. Такие управляющие инструкции могут отличаться от имеющихся
в реальном ассемблере, но каждая из них должна транслироваться в реальный
ассемблер с сохранением семантики и возможным добавлением дополнительных
переходов.

\begin{code}
    exec-block : ∀ {ST d} → State ST → Block ST d
               → State (dapply ST d)
               × Σ (Diff (dapply ST d)) (Block (dapply ST d))
    exec-block {S} (state Γ Ψ DS CS) (Blocks.↝ {c} ci)
      rewrite reg-const S c | ds-const S c
      = (state Γ Ψ DS CS') , next-block
      where
      ecr = exec-control (state Γ Ψ DS CS) ci
      CS' = proj₁ ecr
      next-block : Σ
        (Diff
         (statetype (StateType.registers S) (StateType.memory S)
          (StateType.datastack S)
          (StackDiff.dapply (RegTypes × DataStackType)
           (StateType.callstack S) (csdiff (csChg S c)))))
        (Block
         (statetype (StateType.registers S) (StateType.memory S)
          (StateType.datastack S)
          (StackDiff.dapply (RegTypes × DataStackType)
           (StateType.callstack S) (csdiff (csChg S c)))))
      next-block rewrite sym (dapply-csChg S c) = proj₂ ecr
    exec-block {S} (state Γ Ψ DS CS) (Blocks._∙_ {c} {d} i b)
      rewrite cs-lemma S c
            | RegDiff.dappend-dapply-lemma
              (StateType.registers S)
              (rdiff (sChg c))
              (rdiff d)
            | StackDiff.dappend-dapply-lemma RegType
              (StateType.datastack S)
              (dsdiff (sChg c))
              (dsdiff d)
            = exec-block (state Γ' Ψ' DS' CS) b
      where
      eir = exec-instr (state Γ Ψ DS CS) i
      Γ'  = proj₁ eir
      Ψ'  = proj₁ (proj₂ eir)
      DS' = proj₂ (proj₂ eir)
\end{code}

## Program equivalence as block equivalence

TODO: block equivalence definition
TODO: why it can be considered as program equivalence

### Модуль Eq

Эквивалентность блоков определяется аналогично приведенному выше.

\begin{code}
  module Eq
    (Block : (S : StateType) → Diff S → Set)
    (exec-block : ∀ {ST d} → Values.State Block ST → Block ST d
                → Values.State Block (dapply ST d)
                × Σ (Diff (dapply ST d)) (Block (dapply ST d)))
    where
    open Values Block

    data BlockEq
      : {ST₁ ST₂ : StateType}
      → {d₁ : Diff ST₁} {d₂ : Diff ST₂}
      → (S₁ : State ST₁) (S₂ : State ST₂)
      → Block ST₁ d₁ → Block ST₂ d₂
      → Set
      where
      equal : ∀ {ST}
            → {S : State ST} {d : Diff ST} {A : Block ST d}
            → BlockEq S S A A
      left  : ∀ {ST₁ ST}
            → {d₁ : Diff ST₁} {d₂ : Diff (dapply ST₁ d₁)}
            → {d : Diff ST}
            → {S₁ : State ST₁} {S₂ : State (dapply ST₁ d₁)}
            → {S : State ST}
            → {A₁ : Block ST₁ d₁} {A₂ : Block (dapply ST₁ d₁) d₂}
            → {B : Block ST d}
            → exec-block S₁ A₁ ≡ S₂ , d₂ , A₂
            → BlockEq S₂ S A₂ B
            → BlockEq S₁ S A₁ B
      right : ∀ {ST₁ ST}
            → {d₁ : Diff ST₁} {d₂ : Diff (dapply ST₁ d₁)}
            → {d : Diff ST}
            → {S₁ : State ST₁} {S₂ : State (dapply ST₁ d₁)}
            → {S : State ST}
            → {A₁ : Block ST₁ d₁} {A₂ : Block (dapply ST₁ d₁) d₂}
            → {B : Block ST d}
            → exec-block S₁ A₁ ≡ S₂ , d₂ , A₂
            → BlockEq S S₂ B A₂
            → BlockEq S S₁ B A₁
\end{code}

## Ассемблер x86-64

\ignore{
\begin{code}
module x86-64 where
  open Meta
  open Diffs
\end{code}
}

\begin{code}
  data ControlInstr (S : StateType) : Maybe (CallStackChg S) → Set
  data Instr (S : StateType) : SmallChg S → Set

  open Blocks ControlInstr Instr
  open Values Block
\end{code}

Как было сказано ранее, определяемые инструкции могут не совпадать с
имеющимися в реальном ассемблере. Такой инструкцией является, например,
инструкция `call`. Дополнительным параметром она принимает указатель на
блок, который будет добавлен на стек вызовов. В реальный ассемблер эта
инструкция может быть транслироваться двумя инструкциями: `call` нужного
блока, за которым следует `jmp` на второй указанный блок.

Многие реализованные инструкции не требуются для реализации блока PLT и
приведены здесь, чтобы показать возможность корректного определения
подобных инструкций.

\begin{code}
  data ControlInstr (S : StateType) where
    call : ∀ {Γ DS}
         → (f : block
           (StateType.registers S)
           (StateType.datastack S)
           ((Γ , DS) ∷ StateType.callstack S)
           ∈ StateType.memory S)
         → (cont : block Γ DS (StateType.callstack S)
                 ∈ StateType.memory S)
         → ControlInstr S (just $ StackDiff.push (Γ , DS))
    jmp[_] : (ptr : atom
           (block
           (StateType.registers S)
           (StateType.datastack S)
           (StateType.callstack S) *)
           ∈ StateType.memory S)
         → ControlInstr S nothing
    jmp : (f : block
          (StateType.registers S)
          (StateType.datastack S)
          (StateType.callstack S)
          ∈ StateType.memory S)
        → ControlInstr S nothing
    ret  : ∀ {CS}
         → (p : StateType.callstack S
         ≡ (StateType.registers S , StateType.datastack S) ∷ CS)
         → ControlInstr S (just (StackDiff.pop p))
\end{code}

Определенные инструкции являются примером того, как можно реализовать
работу с регистрами и стеком данных.

\begin{code}
  data Instr (S : StateType) where
    mov  : ∀ {σ τ}
         → (r : σ ∈ StateType.registers S)
         → RegValue (StateType.memory S) τ
         → Instr S (onlyreg (RegDiff.chg r τ))
    push : ∀ {τ}
         → τ ∈ StateType.registers S
         → Instr S (onlystack (StackDiff.push τ))
    pop  : ∀ {σ τ DS}
         → (r : σ ∈ StateType.registers S)
         → (p : StateType.datastack S ≡ τ ∷ DS)
         → Instr S (regstack (RegDiff.chg r τ) (StackDiff.pop p))
\end{code}

Функции, определяющие результаты исполнения заданных инструкций, определяются
тривиально.

\begin{code}
  exec-control : ∀ {S c}
               → State S
               → ControlInstr S c
               → CallStack
                 (StateType.memory S)
                 (StateType.callstack (dapply S (csChg S c)))
               × Σ (Diff (dapply S (csChg S c)))
                   (Block (dapply S (csChg S c)))
  exec-control (state Γ Ψ DS CS) (call f cont)
    = cont ∷ CS , loadblock Ψ f
  exec-control (state Γ Ψ DS CS) (jmp[ p ])
    = CS , loadblock Ψ (loadptr Ψ p)
  exec-control (state Γ Ψ DS CS) (jmp f)
    = CS , loadblock Ψ f
  exec-control (state Γ Ψ DS (f ∷ CS)) (ret refl)
    = CS , loadblock Ψ f

  exec-instr : ∀ {S c}
             → State S
             → Instr S c
             → Registers
               (StateType.memory S)
               (StateType.registers (dapply S (sChg c)))
             × (Data (StateType.memory S)
             × DataStack
               (StateType.memory S)
               (StateType.datastack (dapply S (sChg c))))
  exec-instr (state Γ Ψ DS CS) (mov r x)
    = toreg Γ r x , Ψ , DS
  exec-instr (state Γ Ψ DS CS) (push r)
    = Γ , Ψ , fromreg Γ r ∷ DS
  exec-instr (state Γ Ψ (v ∷ DS) CS) (pop r refl)
    = toreg Γ r v , Ψ , DS
  
  open ExecBlk Instr ControlInstr exec-instr exec-control
  open Eq Block exec-block
\end{code}

## Programs

\ignore{
\begin{code}
  module Linkers where
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

code with PLT and GOT

GOT-correctness

generic code proofs (???)

equivalence proof
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
\end{code}

Блок PLT выглядит так же, как и в первой реализации.

\begin{code}
    plt-stub : ∀ {Γ Ψ DS CS} → atom (block Γ DS CS *) ∈ Ψ
             → Block (statetype Γ Ψ DS CS) dempty
    plt-stub got = ↝ jmp[ got ]
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
