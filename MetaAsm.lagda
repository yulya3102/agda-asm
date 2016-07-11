# Обзор используемой формализации TAL

\label{sec:asm-review}

Оригинальный Typed Assembly Language был достаточно выразительным для
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

\ignore{
\begin{code}
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

\labeledfigure{fig:statetype}{Тип состояния исполнителя}{
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

\labeledfigure{fig:types}{Поддерживаемые типы данных}{
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

Действительно необходимой для формализации динамической линковки является
семантика инструкции непрямого перехода, позволяющая динамически менять
целевую точку передачи исполнения. Аргументом этой инструкции является
указатель на ячейку памяти, в которой находится указатель на блок кода,
который необходимо исполнить. Для корректной типизации этой инструкции в
поддерживаемые типы данных необходимо добавить тип указателя на
типизированную ячейку памяти (тип \C{\_*} в листинге \ref{fig:types}), и
это является третьим отличием.

Динамическая линковка добавляет в объектные файлы код-"прослойку" между
различными библиотеками, исполняемый при вызове внешних функций. Этот код
не должен никак влиять на семантику программы. Это означает, что мы не
можем абстрагироваться от стека вызовов, который может быть "испорчен"
вызовом "лишних" процедур. *Программы* оригинального TAL, помимо исполняемой
последовательности инструкций, включали в себя состояния регистров и
памяти. В используемой формализации они дополнительно включают в себя
состояние стека, который для простоты реализации был разделен на две части:
стек данных и стек вызовов. Типы ожидаемых стека данных и стека вызовов так
же добавляются в параметры типа последовательности инструкций (тип
\C{code} в листинге \ref{fig:types}), который в оригинальном TAL содержал
только ожидаемый тип регистров, и это еще одно существенное отличие
используемой формализации от оригинального TAL.

\ignore{
\begin{code}
open import Data.Maybe

module Diffs where
\end{code}

\begin{code}
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
\end{code}

\begin{code}
  module ListChg (A : Set) where
    data Chg (Γ : List A) : Set where
      chg : ∀ {τ} → τ ∈ Γ → A → Chg Γ

    chgapply : (Γ : List A) → Chg Γ → List A
    chgapply (_ ∷ Γ) (chg (here refl) σ) = σ ∷ Γ
    chgapply (τ ∷ Γ) (chg (there p)   σ) = τ ∷ chgapply Γ (chg p σ)
\end{code}

\begin{code}
  module RegDiff where

    open ListChg RegType public
    open DiffDefinition chgapply public
\end{code}

\begin{code}
  module StackDiff (A : Set) where
    data Chg (S : List A) : Set where
      push : (i : A) → Chg S
      pop  : ∀ {Γ S'} → S ≡ Γ ∷ S' → Chg S

    chgapply : (S : List A) → Chg S → List A
    chgapply cs (push x) = x ∷ cs
    chgapply (._ ∷ S') (pop refl) = S'

    open DiffDefinition chgapply public
\end{code}

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

\begin{code}
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
\end{code}

\begin{code}
module Meta where
  open Diffs
\end{code}

\begin{code}
  module Blocks
    (ControlInstr : (S : StateType)
                  → Maybe (CallStackChg S)
                  → Set)
    (Instr : (S : StateType) → SmallChg S → Set)
    where
    infixr 10 _∙_
\end{code}
}

Кроме того, для обеспечения корректности вызова функции $g$ в конце
блока кода $f$ необходимо понимать, как блок $f$ типа $S_f$ меняет
типы регистров и стеков и может ли он к концу своего исполнения получить
ожидаемый блоком $g$ тип $S_g$. Для этого тип блока, кроме ожидаемых типов
регистров и стеков, хранит некоторый *дифф* типов, применяемый этим блоком.
Индуктивное определение *блока кода* приведено в листинге \ref{fig:block}.

Часть программы, не содержащая исполняемой последовательности инструкций,
будем называть *состоянием исполнителя*. Тип состояния исполнителя приведен в
листинге \ref{fig:statetype}.

Семантика приведенного языка ассемблера определяется двумя функциями,
описывающими семантику инструкций общего назначения (*instructions* из
оригинального TAL) и инструкций перехода (последние инструкции в
*instruction sequences* оригинального TAL). Каждому виду инструкций
разрешено менять только часть состояния исполнителя, и результатом
исполнения инструкции является новое состояние этой части состояния
исполнителя. Так, для управляющих инструкций результатом исполнения
является пара из стека вызовов и следующего блока, который нужно исполнить.

\labeledfigure{fig:block}{Индуктивное определение блока}{
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
            → Block (sttype Γ Ψ DS CS) d
            → Value Ψ (code Γ DS CS)
\end{code}

Определим вспомогательные функции для работы со значениями:

*   получение блока из значения типа `block`;

\begin{code}
    unblock : ∀ {Ψ Γ DS CS} → Value Ψ (code Γ DS CS)
            → Σ (Diff (sttype Γ Ψ DS CS))
                (Block (sttype Γ Ψ DS CS))
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
    loadblock : ∀ {Ψ Γ CS DS} → Data Ψ → code Γ DS CS ∈ Ψ
             → Σ (Diff (sttype Γ Ψ DS CS))
                 (Block (sttype Γ Ψ DS CS))
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
    IPRT Ψ Γ DS CS = code Γ DS CS ∈ Ψ

    IPST : StateType → Set
    IPST (sttype Γ Ψ DS CS) = IPRT Ψ Γ DS CS
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
