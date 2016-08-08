\iftoggle{russian-draft}{
\section{Обзор используемой формализации TAL}
}{
\section{TAL formalization}
}

\label{sec:asm-review}

\iftoggle{russian-draft}{
Оригинальный Typed Assembly Language достаточно выразителен для
реализации возможностей высокоуровневых языков, таких как параметрический
полиморфизм или пользовательские структуры данных. Для нашей задачи эти
возможности не являются существенными, но вместо этого возникает
необходимость наличия определенных типов данных и инструкций, используемых
в реализации динамической линковки. В связи с этим используемая
формализация TAL имеет несколько существенных отличий от оригинального
Typed Assembly Language.

Первым отличием является отсутствие параметров типов. Это является
значительным упрощением исходного языка, позволяющим сильно упростить
используемую формализацию. Тем не менее, динамический линковщик не
нуждается в полиморфизме на уровне языка ассемблера: он не интерпретирует и
не меняет данный ему код, всего лишь добавляя к нему дополнительные
элементы.

Вторым отличием является отсутствие кортежей в памяти, в которых
динамический линковщик также не нуждается. Вместе с типом кортежа из языка
удаляются неинициализированные значения и метки инициализированности.
}{
Original Typed Assembly Language is powerful enough to implement high-level
language featues such as parametric polymorphism or records. These features
are not necessary for our task, but instead we have to have specific data
types and instructions which are typically used to implement dynamic
linking. Therefore, our TAL formalization has some differences from
original Typed Assembly Language.

The lack of type variables is the first difference. It greatly simplifies
original TAL language and allows to simplify our formalization. However,
dynamic linker does not need polymorphism at assembly language level: it
does not interpret and does not change input code, only appending
additional elements to it.

The lack of tuples is the second difference. Dynamic linker does not need
it either. Uninitialized "garbage" values and initialization flags are
deleted from language along with tuple type.
}

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

data RegType : Set
data Type : Set
DataStackType : Set
CallStackType : Set

RegFileTypes = List RegType
HeapTypes = List Type
DataStackType = List RegType
CallStackType = List (RegFileTypes × DataStackType)
\end{code}
}

\labeledfigure{fig:statetype}{Machine state type}{
\begin{code}
record StateType : Set
  where
  constructor sttype
  field
    registers : RegFileTypes
    memory    : HeapTypes
    datastack : DataStackType
    callstack : CallStackType
\end{code}
}

\labeledfigure{fig:types}{Supported data types}{
\begin{code}
data RegType
  where
  _*  : Type → RegType
  int : RegType

data Type
  where
  atom : RegType → Type
  code : RegFileTypes
       → DataStackType → CallStackType
       → Type
\end{code}
}

\iftoggle{russian-draft}{
Действительно необходимой для формализации динамической линковки является
семантика инструкции непрямого перехода, позволяющая динамически менять
целевую точку передачи исполнения. Аргументом этой инструкции является
указатель на ячейку памяти, в которой находится указатель на блок кода,
который необходимо исполнить. Для корректной типизации этой инструкции в
поддерживаемые типы данных необходимо добавить тип указателя на
типизированную ячейку памяти (тип \C{\_*} в листинге \ref{fig:types}), и
это является третьим отличием. По сути, это тип кортежа из оригинального
TAL, но фиксированной длины и без метки инициализированности.

Динамическая линковка добавляет в объектные файлы код-"прослойку" между
различными библиотеками, исполняемый при вызове внешних функций. Этот код
не должен никак влиять на семантику программы. Это означает, что мы не
можем абстрагироваться от стека вызовов, который может быть "испорчен"
вызовом дополнительных процедур. \emph{Программы} оригинального TAL, помимо исполняемой
последовательности инструкций, включали в себя состояния регистров и
памяти. В используемой формализации они дополнительно включают в себя
состояние стека, который для простоты реализации был разделен на две части:
стек данных и стек вызовов. Типы ожидаемых стека данных и стека вызовов так
же добавляются в параметры типа последовательности инструкций (конструктор
\C{code} в листинге \ref{fig:types}), который в оригинальном TAL содержал
только ожидаемый тип регистров, и это еще одно существенное отличие
используемой формализации от оригинального TAL.
}{
What is really necessary for dynamic linking formalization is indirect jump
instruction semantics. This instruction allows to dynamically change target
executable code. The argument of this instruction is a pointer to a memory
location where the address of target executable code is stored. To
correctly type indirect jump instruction we need to support the type of
pointer to typed memory (the type \C{\_*} from listing \ref{fig:types}).
This is the third difference from the original Typed Assembly Language.
Essentially, this is the tuple type from the original TAL, but without
initialization flag and of fixed length.

Dynamic linker adds intermedium code between different libraries. This code
is called when external function is called. It must not affect program
semantics. Therefore, we can't hide call stack in abstractions, because it
can be affected by additional procedure calls. \emph{Programs} of original TAL
includes \emph{instruction sequence}, \emph{register files} and \emph{heaps}. Our
formalization additionally includes \emph{stack}, which is split in two parts:
\emph{data stack} and \emph{call stack}. Instruction sequence type from original TAL
contained only expected \emph{register file type}, but in our formalization
it contains also types of expected data stack and call stack, as shown
in \C{code} constructor of listing \ref{fig:types}. This is another
difference from original TAL.
}

\ignore{
\begin{code}
open import Data.Maybe

module Diffs where
  module DiffDefinition
    {Ctx : Set}
    {Chg : Ctx → Set}
    (chgapply : (Γ : Ctx) → Chg Γ → Ctx)
    where
    data Diff (Γ : Ctx) : Set where
      dempty  : Diff Γ
      dchg    : (c : Chg Γ) → Diff (chgapply Γ c) → Diff Γ

    dapply : (Γ : Ctx) → Diff Γ → Ctx
    dapply Γ dempty = Γ
    dapply Γ (dchg c d) = dapply (chgapply Γ c) d

    dappend : ∀ {Γ} → (d : Diff Γ)
            → Diff (dapply Γ d) → Diff Γ
    dappend dempty b = b
    dappend (dchg c a) b = dchg c (dappend a b)

    dappend-dempty-lemma : ∀ {Γ} → (d : Diff Γ)
                         → dappend d dempty ≡ d
    dappend-dempty-lemma dempty = refl
    dappend-dempty-lemma (dchg c d)
      rewrite dappend-dempty-lemma d = refl

    dappend-dapply-lemma : ∀ S → (d₁ : Diff S)
                         → (d₂ : Diff (dapply S d₁))
                         → dapply S (dappend d₁ d₂)
                         ≡ dapply (dapply S d₁) d₂
    dappend-dapply-lemma S dempty d₂ = refl
    dappend-dapply-lemma S (dchg c d₁) d₂
      = dappend-dapply-lemma (chgapply S c) d₁ d₂

  module ListChg (A : Set) where
    data Chg (Γ : List A) : Set where
      chg : ∀ {τ} → τ ∈ Γ → A → Chg Γ

    chgapply : (Γ : List A) → Chg Γ → List A
    chgapply (_ ∷ Γ) (chg (here refl) σ) = σ ∷ Γ
    chgapply (τ ∷ Γ) (chg (there p)   σ) = τ ∷ chgapply Γ (chg p σ)

  module RegDiff where

    open ListChg RegType public
    open DiffDefinition chgapply public

  module StackDiff (A : Set) where
    data Chg (S : List A) : Set where
      push : (i : A) → Chg S
      pop  : ∀ {Γ S'} → S ≡ Γ ∷ S' → Chg S

    chgapply : (S : List A) → Chg S → List A
    chgapply cs (push x) = x ∷ cs
    chgapply (._ ∷ S') (pop refl) = S'

    open DiffDefinition chgapply public

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

  DataStackChg : StateType → Set
  DataStackChg S
    = StackDiff.Chg RegType (StateType.datastack S)

  CallStackChg : StateType → Set
  CallStackChg S
    = StackDiff.Chg
      (RegFileTypes × DataStackType)
      (StateType.callstack S)

  RegChg : StateType → Set
  RegChg S = RegDiff.Chg (StateType.registers S)

  data SmallChg (S : StateType) : Set where
    onlyreg   : RegChg S → SmallChg S
    onlystack : DataStackChg S → SmallChg S
    regstack  : RegChg S → DataStackChg S → SmallChg S

  regChg : ∀ {S} → RegChg S → Diff S
  regChg S = dchg (rchg S) dempty

  dsChg : ∀ {S} → DataStackChg S → Diff S
  dsChg S = dchg (dschg S) dempty

  sChg : ∀ {S} → SmallChg S → Diff S
  sChg (onlyreg r) = regChg r
  sChg (onlystack d) = dsChg d
  sChg (regstack r d) = dchg (rchg r) $ dchg (dschg d) dempty

  csChg : ∀ S → Maybe (CallStackChg S) → Diff S
  csChg S (just x) = dchg (cschg x) dempty
  csChg S nothing = dempty

module Meta where
  open Diffs

  module Blocks
    (ControlInstr : (S : StateType)
                  → Maybe (CallStackChg S)
                  → Set)
    (Instr : (S : StateType) → SmallChg S → Set)
    where
    infixr 10 _∙_
\end{code}
}

\iftoggle{russian-draft}{
Часть программы, не содержащая исполняемой последовательности инструкций,
будем называть \emph{состоянием исполнителя}. Тип состояния исполнителя приведен в
листинге \ref{fig:statetype}.

Для обеспечения корректности вызова функции $g$ в конце
блока кода (последовательности инструкций) $f$ необходимо понимать, как
блок $f$ типа $S_f$ меняет
типы регистров и стеков и может ли он к концу своего исполнения получить
ожидаемый функцией $g$ тип $S_g$. Для этого тип блока, кроме ожидаемых типов
регистров и стеков, хранит некоторое описание изменений типов различных
частей \emph{программы}, применяемое этим блоком. Это описание хранится в типе
\F{Diff}, параметром которого является тип состояния исполнителя, к
которому может применяться это изменение.
Индуктивное определение \emph{блока кода} приведено в листинге \ref{fig:block}.

Семантика приведенного языка ассемблера определяется двумя функциями,
описывающими семантику инструкций общего назначения (\emph{instructions} из
оригинального TAL) и инструкций перехода (последние инструкции в
\emph{instruction sequences} оригинального TAL). Каждому виду инструкций
разрешено менять только часть \emph{программы}, и результатом
исполнения инструкции является новое состояние этой части
\emph{программы}. Так, для управляющих инструкций результатом исполнения
является пара из нового состояния стека вызовов и следующего блока, который
нужно исполнить. Кроме того, семантика блока кода описывается похожим
образом: результатом исполнения блока является пара из нового состояния
исполнителя и блока, который нужно исполнить следующим.
}{
\emph{Machine state} is the part of the \emph{program} that does not
contain \emph{instruction sequence}. Its type is shown in listing
\ref{fig:statetype}.

To ensurre that function $g$ call in the end of the \emph{block}
(\emph{instruction sequence}) $f$ is correct, we have to know how block $f$
of type $S_f$ changes register file types and stack types and whether it
can transform machine state type $S_f$ to expected by function $g$ machine
state type $S_g$. To achieve this, type of block should contain not only
expected types of register file and stack, but some description of how this
block changes differnet parts of machine state type. This description is
stored in datatype \F{Diff}, which takes as parameter machine state type
that can be changed by this \emph{diff}. Recursive definitoin of the
\emph{code block} is shown in listing \ref{fig:block}.

Semantics of this assembly language is defined by two functions describing
semantics of regular instructions (\emph{instructions} from original TAL)
and branch instructions (last instructions in \emph{instruction sequence}
from original TAL). Each type of instruction is allowed to change only part
of \emph{program}, and execution result is described by the new state of
that part of the \emph{program}. So, some branch instruction execution
result is a pair of new call stack state and next block to execute.
Moreover, semantics of the block is described in the same manner: block
execution result is a pair of the new machine state and next block to
execute.
}

\labeledfigure{fig:block}{Recursive definition of code block}{
\begin{code}
    data Block (S : StateType) : Diff S → Set
      where
      ↝ : ∀ {c} → ControlInstr S c
        → Block S (csChg S c)
      _∙_ : ∀ {c d}
           → Instr S c
           → Block (dapply S (sChg c)) d
           → Block S (dappend (sChg c) d)
\end{code}
}

\ignore{
\begin{code}
  module Values
    (Block : (S : StateType) → Diff S → Set)
    where

    data RegValue (Ψ : HeapTypes) : RegType → Set where
      ptr : ∀ {τ} → τ ∈ Ψ → RegValue Ψ (τ *)
      int : ℕ → RegValue Ψ int

    data Value (Ψ : HeapTypes) : Type → Set where
      atom : ∀ {τ} → RegValue Ψ τ → Value Ψ (atom τ)
      block : ∀ {Γ DS CS d}
            → Block (sttype Γ Ψ DS CS) d
            → Value Ψ (code Γ DS CS)

    unblock : ∀ {Ψ Γ DS CS} → Value Ψ (code Γ DS CS)
            → Σ (Diff (sttype Γ Ψ DS CS))
                (Block (sttype Γ Ψ DS CS))
    unblock (block b) = _ , b

    unint : ∀ {Ψ} → RegValue Ψ int → ℕ
    unint (int x) = x

    unptr : ∀ {Ψ τ} → Value Ψ (atom (τ *)) → τ ∈ Ψ
    unptr (atom (ptr x)) = x

    atom-ptr-unptr : ∀ {Ψ τ} → (v : Value Ψ (atom (τ *)))
                   → atom (ptr (unptr v)) ≡ v
    atom-ptr-unptr (atom (ptr x)) = refl

    data Registers (Ψ : HeapTypes) : RegFileTypes → Set where
      []  : Registers Ψ []
      _∷_ : ∀ {τ τs}
          → RegValue Ψ τ
          → Registers Ψ τs
          → Registers Ψ (τ ∷ τs)

    fromreg : ∀ {Ψ Γ τ} → Registers Ψ Γ → τ ∈ Γ → RegValue Ψ τ
    fromreg (x ∷ Γ) (here refl) = x
    fromreg (x ∷ Γ) (there p) = fromreg Γ p

    toreg : ∀ {Ψ Γ σ τ}
          → Registers Ψ Γ
          → (r : σ ∈ Γ)
          → RegValue Ψ τ
          → Registers Ψ (RegDiff.chgapply Γ (RegDiff.chg r τ))
    toreg (x ∷ Γ) (here refl) v = v ∷ Γ
    toreg (x ∷ Γ) (there r) v = x ∷ (toreg Γ r v)

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

    loadblock : ∀ {Ψ Γ CS DS} → Data Ψ → code Γ DS CS ∈ Ψ
             → Σ (Diff (sttype Γ Ψ DS CS))
                 (Block (sttype Γ Ψ DS CS))
    loadblock Ψ f = unblock $ load Ψ f

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

    IPRT : HeapTypes
         → RegFileTypes
         → DataStackType
         → CallStackType
         → Set
    IPRT Ψ Γ DS CS = code Γ DS CS ∈ Ψ

    IPST : StateType → Set
    IPST (sttype Γ Ψ DS CS) = IPRT Ψ Γ DS CS

    data CallStack (Ψ : HeapTypes) : CallStackType → Set where
      []  : CallStack Ψ []
      _∷_ : ∀ {Γ DS CS} → IPRT Ψ Γ DS CS → CallStack Ψ CS
          → CallStack Ψ ((Γ , DS) ∷ CS)

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

  module ExecBlk
    (Instr : (S : StateType) → Diffs.SmallChg S → Set)
    (ControlInstr : (S : StateType)
                  → Maybe (Diffs.CallStackChg S)
                  → Set)
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

    module DiffLemmas where
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

    open DiffLemmas

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
