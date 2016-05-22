\ignore{
\begin{code}
module MetaAsm where

open import Data.Nat
open import Data.List
open import Data.List.Any
open Membership-≡
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Function
\end{code}
}

# Обзор используемой формализации TAL

\ignore{
\begin{code}
data RegType : Set
\end{code}

\begin{code}
data Type : Set
\end{code}
}
\ignore{
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

There is another difficulty in stack definition. Stack actually serves for
two purposes: tracking return addresses and saving stack frames with local
variables. These two purposes are similar, but for type system they are
quite different. For local variables it only should only check ???, but for
return address it should make sure that `ret` is executed only in suitable
machine state. So, in our model there will be two different stacks: call
stack and data stack, with different typing rules.

\begin{code}
DataStackType : Set
CallStackType : Set
\end{code}

Registers, memory and data stack are typed with list of types of its elements.

\begin{code}
RegFileTypes = List RegType
HeapTypes = List Type
DataStackType = List RegType
\end{code}

TODO: how instruction pointers should be typed

Call stack should be typed with list ot its elements, too. But elements of
call stack are instruction pointers, which types include types of call
stack itself: type of instruction pointer is a type of underlying basic
block, type of basic block is a type of machine state required to correctly
execute this block, and type of machine state includes type of call stack.
Therefore, list of types of instruction pointers can't be used as call
stack type.

However, we have some knowledge about operations on call stack elements:
an element of type `IP` from call stack can be used only when this element
was taken from top of the stack with type `IP ∷ CS`. Typically this happens
when `ret` instruction is executed, and execution continues with block from
extracted instuction pointer with type `IP`. Execution can be continued
only with block typed with current machine state type, and current machine
state has callstack with type `CS`. Therefore, `IP` can't have callstack
type other than `CS`.

Now, we have a restriction on type of instruction pointer that allows us to
infer its call stack type from call stack that contains it. Therefore, type
of call stack element doesn't have to have information about its call stack
type, and we can think that it's defined implicitly. Type of call stack
element doesn't have to have type of memory either, because it's static and
does not change during program lifetime. The only parts of machine state
type that should be stored in type of call stack element are its registers
type and data stack type:

\begin{code}
CallStackType = List (RegFileTypes × DataStackType)
\end{code}
}

Оригинальный TAL позволял использовать переменные типов и кортежи в памяти,
что является оверкиллом для нашей задачи. Система типов в используемой
формализации куда проще: типы размером с регистр включают в себя указатели
и целые числа, а единственным типом произвольного размера являются блоки
кода. Тип блока кода включает в себя типы ожидаемых этим блоком регистров и
стека.

\ignore{
The only arbitrary-sized type that is not also register type is "block
type", which contains all parts of machine state type except for static
memory.
}

Значения типов из первой категории могут находиться в регистрах, а значения
типов второй категории можно сохранять в память. При этом первая категория
является подмножеством второй.

\ignore{
Values with types from the first category can be stored in registers, and
values with types from the second category can be stored in memory. The
first category is a subset of the second category.
}

Для простоты реализации стек был распилен на две части, одна из которых
называется стеком данных и позволяет сохранять в себе данные размером с
регистр, а вторая, стек вызовов, сохраняет адреса возврата. Так,
управляющим инструкциям, завершающим блок, дозволено обращаться только к
стеку вызовов, в то время как не-управляющие инструкции могут работать
только со стеком данных.

Таким образом, тип состояния исполнителя включает в себя не только типы
регистров и памяти, но и типы обоих стеков.

\labeledfigure{fig:statetype}{Тип состояния исполнителя}{
\begin{code}
record StateType : Set where
  constructor statetype
  field
    registers : RegFileTypes
    memory    : HeapTypes
    datastack : DataStackType
    callstack : CallStackType
\end{code}
}

\labeledfigure{fig:types}{Поддерживаемые типы данных}{
\begin{code}
data RegType where
  _*  : Type → RegType
  int : RegType

data Type where
  atom : RegType → Type
  block : RegFileTypes
        → DataStackType → CallStackType
        → Type
\end{code}
}

\ignore{
\ignore{
\begin{code}
open import Data.Maybe
\end{code}
}

### Meta assembly language

The key idea of meta definitions is to define everything in terms of basic
blocks. The defintion of basic block should have instruction set as a
parameter, but once this parameter applied, basic block definition can be
used in other definitions without direct dependency on particular
instrution set.

### Diffs

\ignore{
\begin{code}
module Diffs where
\end{code}
}

The type of basic block should contain information about machine state type
required to execute this block correctly. But to statically analyze
sequence of blocks execution we need to keep track of machine state type
changes. Consider following example:

    f:
        mov rax, 42
        jmp g

    g:
        store ptr, rax
        ret

Knowing types of block `f` and block `g`, we need to statically check that
after executing block `f` machine state type will be exact the same as the
type of block `g`. To achieve this, we will save in block type information
about set of changes of machine type applied by the block. We will refer to
this set of changes as "diff".

Diff on some context consists of sequence of atomic changes. Atomic change
type defines type of context that can be changed by this change.

\begin{code}
  module DiffDefinition
    {Ctx : Set}
    {Chg : Ctx → Set}
    (chgapply : (Γ : Ctx) → Chg Γ → Ctx)
    where
    data Diff (Γ : Ctx) : Set where
      dempty  : Diff Γ
      dchg    : (c : Chg Γ) → Diff (chgapply Γ c) → Diff Γ
\end{code}

\ignore{
Набор изменений является общим для изменений различных видов. То, к чему
применяется изменение, будем называть _контекстом_.
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

Определение изменений для регистров используется из предыдущих реализаций.

\begin{code}
  module RegDiff where

    open ListChg RegType public
    open DiffDefinition chgapply public
\end{code}

В отличие от предыдущих реализаций, в тип инструкций должны входить и стек
вызовов, и стек данных. Это означает, что для них необходимо определить
наборы изменений.
}

Atomic changes are defined for each machine state part. For example, atomic
stack change includes `push` and `pop` operations.

\begin{code}
  module StackDiff (A : Set) where
    data Chg (S : List A) : Set where
      push : (i : A) → Chg S
      pop  : ∀ {Γ S'} → S ≡ Γ ∷ S' → Chg S

    chgapply : (S : List A) → Chg S → List A
    chgapply cs (push x) = x ∷ cs
    chgapply (._ ∷ S') (pop refl) = S'
\end{code}

TODO: block definition

TODO: memory, registers and stacks definition

\ignore{
\begin{code}
    open DiffDefinition chgapply public
\end{code}

Общим набором изменений состояния исполнителя будет являться структура,
описывающая изменения регистров и двух стеков.

\begin{code}
  module StateDiff where
    data Chg (S : StateType) : Set where
      rchg  : RegDiff.Chg (StateType.registers S) → Chg S
      dschg : StackDiff.Chg RegType (StateType.datastack S) → Chg S
      cschg : StackDiff.Chg (RegFileTypes × DataStackType)
               (StateType.callstack S) → Chg S

    chgapply : (S : StateType) → Chg S → StateType
    chgapply S (rchg x)
      = record S {
        registers = RegDiff.chgapply (StateType.registers S) x
      }
    chgapply S (dschg x)
      = record S {
        datastack = StackDiff.chgapply _ (StateType.datastack S) x
      }
    chgapply S (cschg x)
      = record S {
        callstack = StackDiff.chgapply _ (StateType.callstack S) x
      }

    open DiffDefinition chgapply public
  open StateDiff public
\end{code}

Определим вспомогательные функции и типы для конструирования и применения
изменений состояния исполнителя:

*   конструирование пустого набора изменений;

\begin{code}
\end{code}

*   применение набора изменений к состоянию исполнителя;

\begin{code}
\end{code}

*   объединение двух наборов изменений;

\begin{code}
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
      (RegFileTypes × DataStackType)
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
  regChg S = dchg (rchg S) dempty
\end{code}

*   конструирование набора изменений состояния исполнителя по одному
    изменению стека данных;

\begin{code}
  dsChg : ∀ {S} → DataStackChg S → Diff S
  dsChg S = dchg (dschg S) dempty
\end{code}

*   конструирование набора изменений состояния исполнителя по одному
    изменению, производимому инструкцией;

\begin{code}
  sChg : ∀ {S} → SmallChg S → Diff S
  sChg (onlyreg r) = regChg r
  sChg (onlystack d) = dsChg d
  sChg (regstack r d) = dchg (rchg r) $ dchg (dschg d) dempty
\end{code}

*   конструирование набора изменений состояния исполнителя по одному
    возможному изменению стека вызовов.

\begin{code}
  csChg : ∀ S → Maybe (CallStackChg S) → Diff S
  csChg S (just x) = dchg (cschg x) dempty
  csChg S nothing = dempty
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
    infixr 10 _∙_
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
    data RegValue (Ψ : HeapTypes) : RegType → Set where
      ptr : ∀ {τ} → τ ∈ Ψ → RegValue Ψ (τ *)
      int : ℕ → RegValue Ψ int

    data Value (Ψ : HeapTypes) : Type → Set where
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

    unint : ∀ {Ψ} → RegValue Ψ int → ℕ
    unint (int x) = x
\end{code}

*   получение указателя на `τ` из значения типа `τ *`.

\begin{code}
    unptr : ∀ {Ψ τ} → Value Ψ (atom (τ *)) → τ ∈ Ψ
    unptr (atom (ptr x)) = x

    atom-ptr-unptr : ∀ {Ψ τ} → (v : Value Ψ (atom (τ *)))
                   → atom (ptr (unptr v)) ≡ v
    atom-ptr-unptr (atom (ptr x)) = refl
\end{code}

Определение набора регистров аналогично приведенному ранее.

\begin{code}
    data Registers (Ψ : HeapTypes) : RegFileTypes → Set where
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
    data IData (Ψ : HeapTypes) : HeapTypes → Set where
      []  : IData Ψ []
      _∷_ : ∀ {τ τs} → Value Ψ τ → IData Ψ τs → IData Ψ (τ ∷ τs)

    Data : HeapTypes → Set
    Data Ψ = IData Ψ Ψ

    private
      istore : ∀ {Ψ Γ τ} → τ ∈ Γ → IData Ψ Γ → Value Ψ τ → IData Ψ Γ
      istore (here refl) (x ∷ M) v = v ∷ M
      istore (there p) (x ∷ M) v = x ∷ istore p M v

      iload : ∀ {Ψ Γ τ} → IData Ψ Γ → τ ∈ Γ → Value Ψ τ
      iload [] ()
      iload (x ∷ H) (here refl) = x
      iload (x ∷ H) (there p) = iload H p

    load : ∀ {Ψ τ} → Data Ψ → τ ∈ Ψ → Value Ψ τ
    load {Ψ} {τ} = iload

    store : ∀ {Ψ τ} → τ ∈ Ψ → Data Ψ → Value Ψ τ → Data Ψ
    store {Ψ} {τ} = istore
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

    store-loaded : ∀ {Ψ τ} → (v : τ ∈ Ψ) → (M : Data Ψ)
                 → store v M (load M v) ≡ M
    store-loaded = istore-iloaded
      where
      istore-iloaded : ∀ {Ψ Γ τ} → (v : τ ∈ Γ) → (M : IData Ψ Γ)
                     → istore v M (iload M v) ≡ M
      istore-iloaded (here refl) (x ∷ M) = refl
      istore-iloaded (there v) (x ∷ M) rewrite istore-iloaded v M = refl

    store-loaded-ptr : ∀ {Ψ τ} → (M : Data Ψ)
                     → (p : atom (τ *) ∈ Ψ)
                     → {x : τ ∈ Ψ} → loadptr M p ≡ x
                     → store p M (atom (ptr x)) ≡ M
    store-loaded-ptr M p px
      rewrite sym px | atom-ptr-unptr (load M p)
      = store-loaded p M
\end{code}

Стек данных — список значений размера регистра, в типе которого указано,
значения каких типов в нем находятся.

\begin{code}
    data DataStack (Ψ : HeapTypes) : List RegType → Set
      where
      []   : DataStack Ψ []
      _∷_  : ∀ {τ DS} → RegValue Ψ τ
           → DataStack Ψ DS
           → DataStack Ψ (τ ∷ DS)

    peek : ∀ {M τ DS} → DataStack M (τ ∷ DS) → RegValue M τ
    peek (x ∷ ds) = x

    dspop : ∀ {M τ DS} → DataStack M (τ ∷ DS) → DataStack M DS
    dspop (x ∷ ds) = ds
\end{code}

Типизированный instruction pointer — указатель на блок кода в памяти.

\begin{code}
    IPRT : HeapTypes
         → RegFileTypes
         → DataStackType
         → CallStackType
         → Set
    IPRT Ψ Γ DS CS = block Γ DS CS ∈ Ψ

    IPST : StateType → Set
    IPST (statetype Γ Ψ DS CS) = IPRT Ψ Γ DS CS
\end{code}

Стек вызовов — список типизированных instruction pointer-ов.  Ранее было
описано, почему в типе стека вызовов не указывается требуемое блоком
состояние стека вызовов.

\begin{code}
    data CallStack (Ψ : HeapTypes) : CallStackType → Set where
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
\end{code}

*   если набор изменений состояния исполнителя построен как набор изменений
    стека вызовов, то набор изменений стека данных пуст;

\begin{code}
\end{code}

*   если набор изменений состояния исполнителя построен как набор
    изменений, производимых инструкцией, то набор изменений стека вызовов
    пуст;

\begin{code}
\end{code}

*   применение набора изменений, построенных как набор изменений стека
    вызовов, к состоянию исполнителя изменяет только стек вызовов, оставляя
    остальное неизменным.

\begin{code}
      dapply-csChg : ∀ S → (c : Maybe (CallStackChg S))
                   → dapply S (csChg S c)
                   ≡ record S {
                     callstack = maybe′
                       (StackDiff.chgapply _ (StateType.callstack S))
                       (StateType.callstack S)
                       c
                   }
      dapply-csChg S (just x) = refl
      dapply-csChg S nothing = refl

      sChg-csdiff : ∀ S → (c : SmallChg S)
                  → StateType.callstack S
                  ≡ StateType.callstack (dapply S (sChg c))
      sChg-csdiff S (onlyreg x) = refl
      sChg-csdiff S (onlystack x) = refl
      sChg-csdiff S (regstack x x₁) = refl

      mem-chg : ∀ S → (c : StateDiff.Chg S)
              → StateType.memory S
              ≡ StateType.memory (StateDiff.chgapply S c)
      mem-chg S (rchg x) = refl
      mem-chg S (dschg x) = refl
      mem-chg S (cschg x) = refl

      mem-diff : ∀ S → (d : Diff S)
               → StateType.memory S
               ≡ StateType.memory (dapply S d)
      mem-diff S DiffDefinition.dempty = refl
      mem-diff S (DiffDefinition.dchg c d)
        rewrite mem-chg S c = mem-diff _ d

      dapply-dappend-sChg : ∀ {S} → (c : SmallChg S)
                          → (d : Diff (dapply S (sChg c)))
                          → dapply S (dappend (sChg c) d)
                          ≡ dapply (dapply S (sChg c)) d
      dapply-dappend-sChg (onlyreg x) d = refl
      dapply-dappend-sChg (onlystack x) d = refl
      dapply-dappend-sChg (regstack c x) d = refl
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
      with exec-control (state Γ Ψ DS CS) ci
    ... | CS' , next-block
      rewrite dapply-csChg S c
      = state Γ Ψ DS CS' , next-block
    exec-block {S} (state Γ Ψ DS CS) (Blocks._∙_ {c} {d} i b)
      with exec-instr (state Γ Ψ DS CS) i
    ... | Γ' , Ψ' , DS'
      rewrite sChg-csdiff S c | mem-diff S (sChg c)
            | dapply-dappend-sChg c d
      = exec-block (state Γ' Ψ' DS' CS) b
\end{code}
}
}
