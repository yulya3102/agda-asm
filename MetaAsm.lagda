\ignore{
## Typed assembly language definition

As stated earlier, we need a formalisation of typed assembly language that
looks just like real assembly language. The problem is that it's too
hard to write it for every supported instruction set, so it would be
reasonable to extract some common parts and make it reusable. We will refer
to this reusable set of definitions as "meta assembly language".

What differs one assembly language from another is instruction set and its
execution semantics. Other concepts, like memory, registers and stack, are
common and can be defined once for some supported set of assembly languages.

Our meta assembly language formalises common concepts as Agda modules
parametrised with instruction set. As a result, particular assembly
language can be formalised with implementing its instruction set and
importing Agda module with proper arguments.

Formalised meta assembly language includes:

*   basic blocks;
*   registers and "small" values that can be stored in registers;
*   memory and values that can be stored in it;
*   execution semantics for given basic block.

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

### The core of assembly language

The core of meta assembly language is considered common for any assembly
language. It includes machine state and supported data types, which
naturally fall into two categories:

*   register-sized types;

\begin{code}
data RegType : Set
\end{code}

*   arbitrary-sized types.

\begin{code}
data Type : Set
\end{code}

Values with types from the first category can be stored in registers, and
values with types from the second category can be stored in memory. The
first category is a subset of the second category.

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
RegTypes = List RegType
DataType = List Type
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
CallStackType = List (RegTypes × DataStackType)
\end{code}

Machine state type is simply record of types of its parts.

\begin{code}
record StateType : Set where
  constructor statetype
  field
    registers : RegTypes
    memory    : DataType
    datastack : DataStackType
    callstack : CallStackType
\end{code}

Supported register-sized types are pointers and integers.

\begin{code}
data RegType where
  _*  : Type → RegType
  int : RegType
\end{code}

The only arbitrary-sized type that is not also register type is "block
type", which contains all parts of machine state type except for static
memory.

\begin{code}
data Type where
  atom : RegType → Type
  block : RegTypes → DataStackType → CallStackType → Type
\end{code}

\ignore{
\begin{code}
data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A
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

    IPST : StateType → Set
    IPST (statetype Γ Ψ DS CS) = IPRT Ψ Γ DS CS
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
}
}
