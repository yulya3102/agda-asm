## Вторая реализация: метаассемблер

В области формальных доказательств существуют серьезные проблемы с
переиспользованием доказательств: даже при небольшом изменении основных
определений все доказательства приходится менять. При этом определения
многих сущностей косвенно используют определения конкретных инструкций
ассемблера, не вдаваясь в детали, и являются общими для всех языков
ассемблера. Эти определения можно было бы определить независимо от
конкретного языка ассемблера, используя конкретные реализации инструкций
как параметры. Набор этих определений будем называть метаассемблером.

От конкретного ассемблера можно абстрагироваться, переформулировав все
определения так, чтобы они использовали понятие блока кода. Тогда
реализовать метаассемблер можно, определив несколько модулей,
принимающих параметрами сущности конкретного ассемблера. Таких модулей
реализовано четыре:

*   Модуль `Blocks`, принимающий параметрами типы (???) инструкций и
    управляющих инструкций. Определяет понятие блока.
*   Модуль `Values`, принимающий параметром тип блока. Определяет все
    основные сущности: значения, память и регистры.
*   Модуль `ExecBlk`, принимающий параметрами типы инструкций и управляющих
    инструкций, а также функции, определяющие, как эти инструкции меняют
    контекст исполнения. Определяют функцию, определяющую, как блок
    изменяет состояние исполнителя.
*   Модуль `Eq`, принимающий параметрами тип блока и функцию, определяющую,
    как блок изменяет состояние исполнителя. Определяет понятие
    эквивалентности блоков.

С помощью этих модулей можно легко получать все нужные определения, имея
минимальное определение ассемблера, просто импортировав нужные модули с
нужными параметрами.

### Основные определения

\ignore{
\begin{code}
module Meta where

open import DevCore

open import Data.List
open import Data.List.Any
open Membership-≡
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function

module Meta where
\end{code}
}

В этой версии память больше не считается неизменной, поэтому состояние
исполнителя должно описывать не только регистры, но и память.

\begin{code}
  record StateType : Set where
    constructor state
    field
      heap : HeapTypes
      regs : RegFileTypes
  open StateType public
\end{code}

Определение набора изменений регистров аналогично используемому ранее.

\ignore{
\begin{code}
  module Diffs where
    import NotSSA
    open NotSSA.Diffs
    open ListChg Type public
    open Diff chgapply public
\end{code}
}

Так как почти нигде в коде не используется применение изменений к набору
регистров отдельно от всего контекста, удобно определить функцию для
применения изменений сразу ко всему контексту.

\begin{code}
    sdapply : (S : StateType) → Diff (regs S) → StateType
    sdapply (state h r) d = state h (dapply r d)

    SDiff = λ S → Diff (regs S)
\end{code}

\ignore{
\begin{code}
  open Diffs public
\end{code}
}

### Модуль Blocks

Типы инструкций и управляющих инструкций аналогичны используемым ранее.
Отличием является только то, что в качестве первого аргумента они содержат
не типы регистров, а тип состояния исполнителя.

\begin{code}
  module Blocks
    (ControlInstr : StateType → Set)
    (Instr : (S : StateType) → Chg (regs S) → Set)
    where
\end{code}

Определение блока аналогично приведенным в предыдущих секциях.

\begin{code}
    data Block (S : StateType) : Diff (regs S) → Set where
      ↝    : ControlInstr S → Block S dempty
      _∙_  : ∀ {c d} → Instr S c → Block (sdapply S (dchg c dempty)) d
           → Block S (dchg c d)
\end{code}

### Модуль Values

Параметром этого модуля, как уже было сказано, является тип блока.

\begin{code}
  module Values
    (Block : (S : StateType) → Diff (regs S) → Set)
    where
\end{code}

Определение значений аналогично используемому ранее.

\begin{code}
    data Value (Ψ : HeapTypes) : Type → Set where
      function : ∀ {Γ} → {d : Diff Γ}
               → Block (state Ψ Γ) d
               → Value Ψ (blk Γ) 
      ptr : ∀ {τ} → τ ∈ Ψ → Value Ψ (τ *)
\end{code}

Первая реализация не позволяла блокам ссылаться друг на друга. Эту проблему
можно решить, если определить память, используя два параметра типа: первый
говорит о том, на что значения могут ссылаться, а второй говорит о том, что
в памяти в действительности располагается.

\begin{code}
    data IHeap (Ψ : HeapTypes) : HeapTypes → Set where
      []  : IHeap Ψ []
      _∷_ : ∀ {τ Δ} → Value Ψ τ → IHeap Ψ Δ → IHeap Ψ (τ ∷ Δ)
\end{code}

При этом корректно заполненной память считается тогда, когда эти параметры
совпадают.

\begin{code}
    Heap : HeapTypes → Set
    Heap Ψ = IHeap Ψ Ψ
\end{code}

Определим функцию для загрузки значений из памяти:

\begin{code}
    load : ∀ {Ψ τ} → τ ∈ Ψ → Heap Ψ → Value Ψ τ
    load p heap = iload [] p heap
      where
      ++[]-lemma : {A : Set} (a : A) (as bs : List A)
            → as ++ a ∷ bs ≡ (as ++ [ a ]) ++ bs
      ++[]-lemma a [] bs = refl
      ++[]-lemma a (x ∷ as) bs rewrite ++[]-lemma a as bs = refl

      iload : ∀ {Ψ τ} ψs → τ ∈ Ψ → IHeap (ψs ++ Ψ) Ψ
            → Value (ψs ++ Ψ) τ
      iload ψs (here refl) (x ∷ _) = x
      iload {ψ ∷ Ψ} ψs (there p) (x ∷ h)
        rewrite ++[]-lemma ψ ψs Ψ = iload (ψs ++ [ ψ ]) p h
\end{code}

Регистры — список значений, ссылающихся на память, в типе которого описано,
значения каких типов он хранит.
<!--- тут до меня дошло, что это копипаста IHeap :( -->

\begin{code}
    data IRegisters (Ψ : HeapTypes) : RegFileTypes → Set where
      []  : IRegisters Ψ []
      _∷_ : ∀ {τ τs} → Value Ψ τ → IRegisters Ψ τs
          → IRegisters Ψ (τ ∷ τs)

    Registers : StateType → Set
    Registers S = IRegisters (heap S) (regs S)
\end{code}

Ниже приведены вспомогательные функции для работы с значениями.

\begin{code}
    unptr : ∀ {Ψ τ} → Value Ψ (τ *) → τ ∈ Ψ
    unptr (ptr x) = x

    unfun : ∀ {Ψ Γ} → Value Ψ (blk Γ)
          → Σ (Diff Γ) (Block (state Ψ Γ))
    unfun (function x) = _ , x

    _∈B_ : ∀ {S d} → Block S d → Heap (heap S) → Set
    _∈B_ {S} b Ψ = Σ (blk (regs S) ∈ heap S)
                 $ λ ptr → (unfun (load ptr Ψ)) ≡ _ , b
\end{code}

### Модуль ExecBlk

Перед тем, как описывать исполнение кода, необходимо определить набор
сущностей, влияющих на результат исполнения, но не не известных на момент
компиляции. К ним относятся instruction pointer и стек вызовов.

\begin{code}
  module Exec-Context (Ψ : HeapTypes) where
\end{code}

Instruction pointer заданного типа `Γ` — индекс блока, рассчитывающего
на состояние регистров `Γ`, находящийся в памяти.

\begin{code}
    IPRFT = λ Γ → blk Γ ∈ Ψ
\end{code}

Instruction pointer — **TODO: то, что выше, только произвольного типа, и я
понятия не имею, как это сформулировать**

\begin{code}
    IP = Σ RegFileTypes IPRFT
\end{code}

В этой версии вместо сохранения в стеке вызовов самих блоков будем хранить
указатели на них.

\begin{code}
    CallStack = List IP
\end{code}

\ignore{
\begin{code}
  open Exec-Context public
\end{code}
}

Параметрами модуля `ExecBlk` являются типы инструкций и управляющих
инструкций, а также функции, описывающие результат их исполнения.
изменятся. Опишем типы этих параметров.

\begin{code}
  module ExecBlk
\end{code}

Сигнатуры инструкций и управляющих инструкций уже были описаны ранее.

\begin{code}
    (Instr : (S : StateType) → Chg (regs S) → Set)
    (ControlInstr : StateType → Set)
\end{code}

Результат исполнения инструкции зависит от того, какие значения в данный
момент находятся в памяти и регистрах, и определяет, на какие значения они
изменятся.

\begin{code}
    (exec-instr : {S : StateType}
                → {c : Chg (regs S)} → Instr S c
                → Values.Heap
                  (Blocks.Block ControlInstr Instr)
                  (heap S)
                → Values.Registers
                  (Blocks.Block ControlInstr Instr)
                  S
                → Values.Heap
                  (Blocks.Block ControlInstr Instr)
                  (heap $ sdapply S (dchg c dempty))
                × Values.Registers
                  (Blocks.Block ControlInstr Instr)
                  (sdapply S (dchg c dempty)))
\end{code}

Результат исполнения управляющей инструкции зависит от того, какие
значения находятся в памяти, что находится в стеке вызовов и чему равен
instruction pointer, и определяет, как изменится стек вызовов и instruction
pointer. При этом тип instruction pointer-а заранее известен. **TODO: тут
вообще-то имеется в виду, что возвращаемым значением является IPRFT, а не
просто IP, но звучит это как-то криво**

\begin{code}
    (exec-control : {S : StateType}
                  → ControlInstr S
                  → Values.Heap
                    (Blocks.Block ControlInstr Instr)
                    (heap S)
                  → CallStack (heap S)
                  → IP (heap S)
                  → CallStack (heap S)
                  × IPRFT (heap S) (regs S))
    where
    open Blocks ControlInstr Instr public
    open Values Block public
\end{code}

Результатом исполнения блока является **TODO: объединение?** результатов
всех входящих в блок инструкций. Это означает, что результат исполнения
блока зависит от того, какие значения находятся в памяти и регистрах, чему
равен instruction pointer и что находится в стеке вызовов и определяет,
какой блок будет исполняться следующим и как изменятся стек вызовов и
значения в памяти и регистрах.

Однако, для некоторых блоков (например, блоков, заканчивающихся условным
переходом или вызовом функции) важно их расположение в памяти: за ними
должен располагаться блок кода, имеющий подходящий тип.  Это не было учтено
при реализации блоков, из-за чего корректно определить функцию `exec-blk`
оказалось затруднительно.

\begin{code}
    exec-blk : {S : StateType} {d : Diff (regs S)} {b : Block S d}
             → (Ψ : Heap (heap S))
             → b ∈B Ψ
             → Registers S → CallStack (heap S)
             → (Σ (Diff $ dapply (regs S) d) (Block $ sdapply S d))
             × (Heap (heap $ sdapply S d)
             × (Registers (sdapply S d)
             × CallStack (heap $ sdapply S d)))
    exec-blk {b = b} Ψ p Γ cs = {!!}
\end{code}

### Модуль Eq

Параметрами этого модуля являются тип блока и функция, определяющая
результат исполнения блока.

\begin{code}
  module Eq
    (Block : (S : StateType) → Diff (regs S) → Set)
    (exec-blk : {S : StateType} {d : Diff (regs S)} {b : Block S d}
              → (Ψ : Values.Heap Block (heap S))
              → Values._∈B_ Block b Ψ
              → Values.Registers Block S → CallStack (heap S)
              → (Σ (Diff $ dapply (regs S) d) (Block $ sdapply S d))
              × (Values.Heap Block (heap $ sdapply S d)
              × (Values.Registers Block (sdapply S d)
              × CallStack (heap $ sdapply S d))))
    where
    open Values Block
\end{code}

Определение эквивалентности блоков почти аналогично приведенному ранее.
<!--- Фиг знает, надо ли тут это. Если забыть о тупняке, происходящем в
первой реализации, то это утверждение скорее сбивает с толку, чем сообщает
что-то полезное -->
Отличием является то, что стек вызовов теперь считается меняющимся после
исполнения любого блока.

\begin{code}
    data BlockEq :
      {S₁ S₂ : StateType} → {d₁ : SDiff S₁} {d₂ : SDiff S₂} →
      (Ψ₁ : Heap (heap S₁)) (Ψ₂ : Heap (heap S₂)) →
      (Γ₁ : Registers S₁) (Γ₂ : Registers S₂) →
      (CC₁ : CallStack (heap S₁)) (CC₂ : CallStack (heap S₂)) →
      Block S₁ d₁ → Block S₂ d₂ → Set
      where
\end{code}

Два блока эквивалентны, если:

*   они одинаковы;

\begin{code}
      equal : ∀ {S} → {d : SDiff S}
            → {Ψ : Heap (heap S)} {CC : CallStack (heap S)}
            → {B : Block S d} {Γ : Registers S}
            → BlockEq Ψ Ψ Γ Γ CC CC B B
\end{code}

*   исполнение первого из них приводит к блоку, эквивалентному второму;

\begin{code}
      left  : ∀ {S₁ S}
            → {d₁ : SDiff S₁} {d₂ : SDiff (sdapply S₁ d₁)}
            → {d : SDiff S}
            → {A₁ : Block S₁ d₁} {A₂ : Block (sdapply S₁ d₁) d₂}
            → {B : Block S d}
            → (Ψ₁ : Heap (heap S₁))
            → (Ψ₂ : Heap (heap (sdapply S₁ d₁)))
            → (Ψ : Heap (heap S))
            → (ip₁ : A₁ ∈B Ψ₁) (ip₂ : A₂ ∈B Ψ₂)
            → (ip : B ∈B Ψ)
            → (Γ₁ : Registers S₁) (Γ₂ : Registers (sdapply S₁ d₁))
            → (Γ : Registers S)
            → (CC₁ : CallStack (heap S₁))
            → (CC₂ : CallStack (heap $ sdapply S₁ d₁))
            → (CC : CallStack (heap S))
            → exec-blk Ψ₁ ip₁ Γ₁ CC₁ ≡ (_ , A₂) , Ψ₂ , Γ₂ , CC₂
            → BlockEq Ψ₁ Ψ Γ₁ Γ CC₁ CC A₁ B
            → BlockEq Ψ₂ Ψ Γ₂ Γ CC₂ CC A₂ B
\end{code}

*   исполнение второго из них приводит к блоку, эквивалентному первому.

\begin{code}
      right : ∀ {S₁ S}
            → {d₁ : SDiff S₁} {d₂ : SDiff (sdapply S₁ d₁)}
            → {d : SDiff S}
            → {A₁ : Block S₁ d₁} {A₂ : Block (sdapply S₁ d₁) d₂}
            → {B : Block S d}
            → (Ψ₁ : Heap (heap S₁))
            → (Ψ₂ : Heap (heap (sdapply S₁ d₁)))
            → (Ψ : Heap (heap S))
            → (ip₁ : A₁ ∈B Ψ₁) (ip₂ : A₂ ∈B Ψ₂)
            → (ip : B ∈B Ψ)
            → (Γ₁ : Registers S₁) (Γ₂ : Registers (sdapply S₁ d₁))
            → (Γ : Registers S)
            → (CC₁ : CallStack (heap S₁))
            → (CC₂ : CallStack (heap $ sdapply S₁ d₁))
            → (CC : CallStack (heap S))
            → exec-blk Ψ₁ ip₁ Γ₁ CC₁ ≡ (_ , A₂) , Ψ₂ , Γ₂ , CC₂
            → BlockEq Ψ Ψ₁ Γ Γ₁ CC CC₁ B A₁
            → BlockEq Ψ Ψ₂ Γ Γ₂ CC CC₂ B A₂
\end{code}

\ignore{
\begin{code}
open Meta
\end{code}
}

### Ассемблер x86-64

\ignore{
\begin{code}
module x86-64 where
\end{code}
}

Определения инструкций и управляющих инструкций аналогично приведенным
ранее.

\begin{code}
  data ControlInstr (S : StateType) : Set where
    jmp call : blk (regs S) ∈ heap S → ControlInstr S
    jmp[_]   : blk (regs S) * ∈ heap S → ControlInstr S

  data Instr (S : StateType) : Chg (regs S) → Set where
    mov : ∀ {τ σ} → (r : σ ∈ regs S)
        → Values.Value
          (Blocks.Block ControlInstr Instr)
          (heap S) τ
        → Instr S (chg r τ)
\end{code}

Описание результатов исполнения определенных инструкций аналогично
приведенному ранее.

**TODO: надо распилить CallCtx из SSAшной реализации, потому что делает код
менее похожим на происходящее здесь и вообще не несет особого смысла**

\begin{code}
  exec-control : {S : StateType}
               → ControlInstr S
               → Values.Heap
                 (Blocks.Block ControlInstr Instr)
                 (heap S)
               → CallStack (heap S) → IP (heap S)
               → CallStack (heap S) × IPRFT (heap S) (regs S)
  exec-control {state heap regs} (jmp x) Ψ cs ip = cs , x
  exec-control {state heap regs} (call x) Ψ cs ip = ip ∷ cs , x
  exec-control {state heap regs} (jmp[ x ]) Ψ cs ip
    = cs
    , (Values.unptr
      (Blocks.Block ControlInstr Instr)
      $ Values.load (Blocks.Block ControlInstr Instr) x Ψ)
\end{code}

Функция `exec-instr` не была реализована. <!--- потому что потерялся смысл -->

\begin{code}
  exec-instr : {S : StateType}
             → {c : Chg (regs S)} → Instr S c
             → Values.Heap
               (Blocks.Block ControlInstr Instr)
               (heap S)
             → Values.Registers
               (Blocks.Block ControlInstr Instr)
               S
             → Values.Heap
               (Blocks.Block ControlInstr Instr)
               (heap $ sdapply S (dchg c dempty))
             × Values.Registers
               (Blocks.Block ControlInstr Instr)
               (sdapply S (dchg c dempty))
  exec-instr = {!!}
\end{code}

<!---
Вообще-то раньше после этого был еще какой-то веселый код, который показал,
что нифига эта реализация не работает. Код выпилился за ненадобностью, а
опены остались.
-->

\begin{code}
  open ExecBlk Instr ControlInstr exec-instr exec-control
  open Eq Block exec-blk
\end{code}

### Проблемы этого решения

Несмотря на то, что это решение не обладает описанными ранее недостатками,
оно имеет ряд проблем.

*   Размеры возможных значений никак не учитываются. Ничто не мешает загрузить
    в регистр блок кода.
*   Блок кода не накладывает никаких ограничений на свое расположение в
    памяти, но может рассчитывать на то, что после него лежит подходящий
    блок. Это означает, что существует возможность после блока,
    завершающегося call, поместить блок данных, что приведет к некорректному
    состоянию стека вызовов.
*   Нет никакой динамической аллокации памяти (???), которая нужна хотя бы
    для того, чтобы можно было сохранить значения регистров.
*   Инструкции не накладывают ограничений на состояние стека вызовов. Это
    означает, что инструкция `ret` может быть исполнена при пустом стеке
    вызовов, что некорректно.
