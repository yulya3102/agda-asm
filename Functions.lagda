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

## Основные определения

Одной из проблем прошлых решений является неучитывание размеров возможных
значений, из-за чего возможно написать код, загружающий в регистр значение,
которое не может быть загружено. Решить эту проблему возможно, поделив
возможные значения на два класса:

*   значения, которые могут располагаться в регистрах;

\begin{code}
data RegType : Set

RegTypes = List RegType
\end{code}

*   значения произвольного размера, которые могут располагаться в памяти.

\begin{code}
data Type : Set

DataType = List Type
\end{code}

Еще одной проблемой являлось полное отсутствие динамически аллоцируемой
памяти, в качестве которой можно использовать стек данных.

Для удобства будем считать стек вызовов и стек данных разными сущностями,
хотя на практике обычно используется один стек.

\begin{code}
DataStackType : Set
CallStackType : Set
\end{code}

Состояния обоих стеков, как и состояния регистров и памяти, входят в
состояние исполнителя.

\begin{code}
record StateType : Set where
  constructor statetype
  field
    registers : RegTypes
    memory    : DataType
    datastack : DataStackType
    callstack : CallStackType
\end{code}

Значениями, размер которых равен размеру регистра, являются указатели и
целые числа.

\begin{code}
data RegType where
  _*  : Type → RegType
  int : RegType
\end{code}

К значениям, которые могут располагаться в памяти, относятся как значения
размера регистра, так и блоки кода. Тип блока кода описывает состояния
регистров и обоих стеков, при которых он может быть корректно исполнен.

\begin{code}
data Type where
  atom : RegType → Type
  block : RegTypes → DataStackType → CallStackType → Type
\end{code}

Стек данных может хранить только значения размера регистра. Его тип можно
описать списком типов находящихся в нем значений.

\begin{code}
DataStackType = List RegType
\end{code}

<!--- вот тут на самом деле нетривиально — тип стека вызовов должен
ссылаться сам на себя, но это успешно обходится -->

Стек вызовов хранит указатели на блоки в памяти. Параметрами типа блока
<!--- вот тут до меня дошло, что здесь происходит какое-то ambiguity между
фразами "тип блока" здесь (конструктор block типа Type) и далее (тип Block)
--> являются типы регистров, тип стека данных и тип стека вызовов. При этом
сохраненный в стеке вызовов указатель на блок может быть исполнен только
при снятии его со стека. Это означает, что добавить указатель на блок в
стек вызовов можно только в тот момент исполнения, когда тип стека вызовов
совпадает с тем, на который рассчитывает блок. Это позволяет описать тип
стека вызовов как список пар типов регистров и стека данных, считая, что
тип стека вызовов задан неявно.

\begin{code}
CallStackType = List (RegTypes × DataStackType)
\end{code}

\ignore{
\begin{code}
data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A
\end{code}
}

## Наборы изменений

\ignore{
\begin{code}
module Diffs where
  import NotSSA
\end{code}
}

Определение изменений для регистров используется из предыдущих реализаций.

\begin{code}
  module RegDiff where
\end{code}

\ignore{
\begin{code}
    open NotSSA.Diffs
\end{code}
}

\begin{code}
    open ListChg RegType public
    open Diff chgapply public
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
\end{code}

\ignore{
\begin{code}
    open NotSSA.Diffs
\end{code}
}

\begin{code}
    open Diff chgapply public
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
    data RegValue (Ψ : DataType) : RegType → Set where
      ptr : ∀ {τ} → τ ∈ Ψ → RegValue Ψ (τ *)
      int : ℕ → RegValue Ψ int

    data Value (Ψ : DataType) : Type → Set where
      atom : ∀ {τ} → RegValue Ψ τ → Value Ψ (atom τ)
      block : ∀ {Γ DS CS d}
            → Block (statetype Γ Ψ DS CS) d
            → Value Ψ (block Γ DS CS)

    unblock : ∀ {Ψ Γ DS CS} → Value Ψ (block Γ DS CS)
            → Σ (Diff (statetype Γ Ψ DS CS))
                (Block (statetype Γ Ψ DS CS))
    unblock (block b) = _ , b

    unptr : ∀ {Ψ τ} → Value Ψ (atom (τ *)) → τ ∈ Ψ
    unptr (atom (ptr x)) = x
      
    data Registers (Ψ : DataType) : RegTypes → Set where
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

    loadfunc : ∀ {Ψ Γ CS DS} → Data Ψ → block Γ DS CS ∈ Ψ
             → Σ (Diff (statetype Γ Ψ DS CS))
                 (Block (statetype Γ Ψ DS CS))
    loadfunc Ψ f = unblock $ load Ψ f

    loadptr : ∀ {Ψ τ} → Data Ψ → atom (τ *) ∈ Ψ → τ ∈ Ψ
    loadptr Ψ p = unptr $ load Ψ p

    data Stack {I : Set} {A : I → Set} (Ψ : DataType)
      : List I → Set
      where
      []   : Stack Ψ []
      _∷_  : ∀ {τ S} → A τ
           → Stack {A = A} Ψ S
           → Stack Ψ (τ ∷ S)

    IPRT : DataType
         → RegTypes
         → DataStackType
         → CallStackType
         → Set
    IPRT Ψ Γ DS CS = block Γ DS CS ∈ Ψ

    DataStack = λ Ψ → Stack {A = RegValue Ψ} Ψ

    data CallStack (Ψ : DataType) : CallStackType → Set where
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
\end{code}

### Модуль ExecBlk

\begin{code}
  module ExecBlk
    (ControlInstr : (S : StateType)
                  → Maybe (Diffs.CallStackChg S)
                  → Set)
    (Instr : (S : StateType) → Diffs.SmallChg S → Set)
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
    where
    open Diffs
    open Blocks ControlInstr Instr
    open Values Block
  
    module DiffLemmas where
      reg-const : ∀ S → (c : Maybe (CallStackChg S))
                → rdiff (csChg S c) ≡ RegDiff.dempty
      reg-const S (just c) = refl
      reg-const S nothing = refl
    
      ds-const : ∀ S → (c : Maybe (CallStackChg S))
               → dsdiff (csChg S c) ≡ StackDiff.dempty
      ds-const S (just x) = refl
      ds-const S nothing = refl
    
      cs-lemma : ∀ S → (c : SmallChg S)
               → csdiff (sChg c) ≡ StackDiff.dempty
      cs-lemma S (onlyreg x) = refl
      cs-lemma S (onlystack x) = refl
      cs-lemma S (regstack x x₁) = refl
  
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
  
    open DiffLemmas
  
    exec-block : ∀ {ST d} → State ST → Block ST d
               → State (dapply ST d)
               × Σ (Diff (dapply ST d)) (Block (dapply ST d))
    exec-block {S} (state Γ Ψ DS CS) (Blocks.↝ {c} ci)
      rewrite reg-const S c | ds-const S c
      = (state Γ Ψ DS CS') , blk
      where
      ecr = exec-control (state Γ Ψ DS CS) ci
      CS' = proj₁ ecr
      blk : Σ
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
      blk rewrite sym (dapply-csChg S c) = proj₂ ecr
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

### Модуль Eq

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

## Ассемблер amd64

\begin{code}
module AMD64 where
  open Meta
  open Diffs

  data ControlInstr (S : StateType) : Maybe (CallStackChg S) → Set
  data Instr (S : StateType) : SmallChg S → Set

  open Blocks ControlInstr Instr
  open Values Block
\end{code}

Одной из проблем предыдущей реализации было то, что блоки кода, не накладывая
никаких ограничений на свое расположение в памяти, рассчитывали на некоторый
контекст. Это происходило в тех местах, где это требовалось управляющим
инструкциям, например, инструкции вызова функции или условных переходов.
Эту проблему возможно решить, заменив подобные инструкции на другие,
принимающие в качестве дополнительного аргумента адрес, по которому должно
располагаться продолжение кода. В требуемый ассемблер x86\_64 это может
отображаться одним дополнительным `jmp` на указанный адрес.

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
    jump : (f : block
           (StateType.registers S)
           (StateType.datastack S)
           (StateType.callstack S)
           ∈ StateType.memory S)
         → ControlInstr S nothing
    ret  : ∀ {CS}
         → (p : StateType.callstack S
         ≡ (StateType.registers S , StateType.datastack S) ∷ CS)
         → ControlInstr S (just (StackDiff.pop p))

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
    = cont ∷ CS , loadfunc Ψ f
  exec-control (state Γ Ψ DS CS) (jmp[ p ])
    = CS , loadfunc Ψ (loadptr Ψ p)
  exec-control (state Γ Ψ DS CS) (jump f)
    = CS , loadfunc Ψ f
  exec-control (state Γ Ψ DS (f ∷ CS)) (ret refl)
    = CS , loadfunc Ψ f

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
  
  open ExecBlk ControlInstr Instr exec-control exec-instr
  open Eq Block exec-block
\end{code}

## Линковка

\begin{code}
  module Linkers where
\end{code}

Преобразование памяти делается аналогично приведенному в первой реализации.
Все, кроме блоков, остается неизменным, а на каждый блок дополнительно
добавляются элементы PLT и GOT.

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
    blk : ∀ {Γ Ψ DS CS} → block Γ DS CS ∈ Ψ
        → block Γ DS CS ∈ pltize Ψ
    blk (here refl) = there (there (here refl))
    blk {Ψ = atom x ∷ Ψ} (there f) = there $ blk f
    blk {Ψ = block Γ DS CS ∷ Ψ} (there f)
      = there (there (there (blk f)))
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
    GOT[ f ]-correctness H = loadptr H (got f) ≡ blk f
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
              , loadfunc
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
             ≡ S , loadfunc (State.memory S) (blk f)
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
            (proj₂ $ loadfunc (State.memory S) (blk f))
    proof f S p = left (exec-plt f S p) equal
\end{code}
