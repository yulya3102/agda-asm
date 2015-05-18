\begin{code}
module NotSSAInstructions where

open import OXIj.BrutalDepTypes
open Data-List
open Data-Any

{-
Все интересуемые меня значения — указатели куда-либо. Поэтому все
известные мне значения имеют один размер.

Более того, я не умею в аллокацию памяти, ибо это не имеет отношения
к ассемблеру. Я умею только менять значения в памяти по указателю, и
это ок.
-}

data Type : Set

RegFileTypes = List Type
HeapTypes    = List Type

data Type where
  blk : (Γ : RegFileTypes) → Type -- Кусок кода, рассчитывающий на наличие
                                  -- регистров Γ в текущем контексте исполнения
  _✴  : Type → Type               -- Указатель

open Membership {A = Type} _≡_

{-
  Внизу в описании типа инструкций раньше использовался список регистров,
  добавляемых инструкцией. На самом деле это примитивнейший diff, умеющий
  только добавлять что-либо, не изменяя и не удаляя. Собственно, из-за
  этого и получалось SSA.

  Если же вместо списка новых регистров сделать нормальный diff (только
  для типов регистров, не для значений), то получится не-SSA-шный вариант.
  Можно вообще выкинуть добавление новых регистров, тогда будет практически
  нормальный ассемблер.
-}
module TDiffs where
  -- Некоторое атомарное изменение RegFile
  data TChg (Γ : RegFileTypes) : Set where
    -- изменить значение в регистре r
    tchgcr : ∀ {r} → r ∈ Γ → (r' : Type) → TChg Γ

  -- Применить изменение к RegFile
  appChg : (Γ : RegFileTypes) → TChg Γ → RegFileTypes
  appChg (_ ∷ Γ) (tchgcr (here refl) r') = r' ∷ Γ
  appChg (a ∷ Γ) (tchgcr (there r) r') = a ∷ appChg Γ (tchgcr r r')

  -- Собственно, diff, являющийся списком атомарных изменений
  data TDiff (Γ : RegFileTypes) : Set where
    tdempty  : TDiff Γ
    tdchg    : (tchg : TChg Γ) → TDiff (appChg Γ tchg) → TDiff Γ

  -- Применение TDiff к RegFile
  tdapply : (Γ : RegFileTypes) → TDiff Γ → RegFileTypes
  tdapply Γ tdempty = Γ
  tdapply Γ (tdchg tchg td) = tdapply (appChg Γ tchg) td

  -- Склеивание diff-ов
  tdappend : ∀ {Γ} → (td : TDiff Γ) → TDiff (tdapply Γ td) → TDiff Γ
  tdappend tdempty b = b
  tdappend (tdchg tchg a) b = tdchg tchg (tdappend a b)

  record State : Set where
    constructor state
    field
      heap : HeapTypes
      regs : RegFileTypes
  open State

  record SDiff (S : State) : Set where
    constructor diff
    field
      heapDiff : TDiff (heap S)
      regsDiff : TDiff (regs S)
  open SDiff

  sdempty : ∀ {S} → SDiff S
  sdempty = diff tdempty tdempty

  sdapply : (S : State) → SDiff S → State
  sdapply s d = state (tdapply (heap s) (heapDiff d)) (tdapply (regs s) (regsDiff d))

  sdappend : ∀ {S} → (d : SDiff S) → SDiff (sdapply S d) → SDiff S
  sdappend (diff h r) (diff h' r') = diff (tdappend h h') (tdappend r r')
open TDiffs

{-
  Инструкции бывают двух типов: управляюшие инструкции (call, jump и
  подобные) и все остальные (их я буду называть просто инструкциями).
  Блок — последовательность инструкций, заканчивающаяся управляющей
  инструкцией. Внутри блока не может быть никаких переходов.
  Мне удобно такое деление, потому что меня интересует не просто
  изменение контекста исполнения, а переходы между различными кусками
  кода, то есть блоками.

  Блок задаёт, на какой контекст регистров Γ он рассчитывает, и какие
  новые регистры Δ добавляет к этому контексту.
-}
module Blocks
  (ControlInstr : HeapTypes → RegFileTypes → Set)
  (Instr : (Ψ : HeapTypes) → (Γ : RegFileTypes) → TDiff Γ → Set)
  where
  data Block (Ψ : HeapTypes) (Γ : RegFileTypes) : TDiff Γ → Set where
    -- Блок, завершающий исполнение
    halt : Block Ψ Γ tdempty
    -- Блок, переходящий куда-либо в соответствии с результатом
    -- исполнения управляющей инструкции
    ↝    : ControlInstr Ψ Γ → Block Ψ Γ tdempty
    -- Какая-нибудь инструкция внутри блока
    _∙_  : ∀ {d' d} → Instr Ψ Γ d' → Block Ψ (tdapply Γ d') d → Block Ψ Γ (tdappend d' d)

  -- Иногда из функции надо вернуть абсолютно любой блок,
  -- с любыми параметрами типа (как Γ и Δ), как это нормально делается?
  -- Или использовать Σ и есть правильный способ?
  NewBlk : HeapTypes → Set
  NewBlk Ψ = Σ RegFileTypes (λ Γ → Σ (TDiff Γ) (λ d → Block Ψ Γ d))

  -- Какие-то определения про контекст исполнения
  
  -- call stack, по сути, есть всего лишь список адресов блоков возврата
  -- Будем хранить не адреса, а сами блоки
  CallStack : HeapTypes → Set
  CallStack Ψ = List (NewBlk Ψ)

  -- Контекст исполнения (кроме регистров) — call stack и instruction
  -- pointer. На самом деле меня интересует не IP, а IP+1 (блок, который
  -- будет исполняться следующим)
  CallCtx : HeapTypes → Set
  CallCtx Ψ = CallStack Ψ × NewBlk Ψ

{-
  Управляющая инструкция не добавляет никаких новых регистров, поэтому,
  в отличие от блока, имеет только один параметр.
-}
data ControlInstr (Ψ : HeapTypes) (Γ : RegFileTypes) : Set
  where
  call   : (f : blk Γ ∈ Ψ) → ControlInstr Ψ Γ
  jmp[_] : (f : (blk Γ) ✴ ∈ Ψ) → ControlInstr Ψ Γ
  -- А вот эта инструкция мне на самом деле не нужна,
  -- она здесь просто потому что я могу
  jmp    : (f : blk Γ ∈ Ψ) → ControlInstr Ψ Γ

data Value (Ψ : HeapTypes) : Type → Set

-- Возможно, имеет смысл сюда засунуть не TDiff, а TChg
data Instr (Ψ : HeapTypes) (Γ : RegFileTypes) : TDiff Γ → Set where
  -- Я могу делать инструкции, _меняющие_ регистры, а не добавляющие новые!
  mov  : ∀ {r τ} → (r∈Γ : r ∈ Γ) → Value Ψ τ → Instr Ψ Γ (tdchg (tchgcr r∈Γ τ) tdempty)

-- возможно, всё, что ниже, стоит дропнуть

open Blocks ControlInstr Instr

data Value (Ψ : HeapTypes) where
  function : {Γ : RegFileTypes} → {d : TDiff Γ} → Block Ψ Γ d → Value Ψ (blk Γ)
  ptr      : ∀ {τ} → τ ∈ Ψ → Value Ψ (τ ✴)

RegFile : HeapTypes → Set
RegFile Ψ = List (Σ Type (Value Ψ))
rftypes : {Ψ : HeapTypes} → RegFile Ψ → RegFileTypes
rftypes [] = []
rftypes (r ∷ rs) = projl r ∷ rftypes rs

-- Набор heap-related определений


data Heap (Γ : HeapTypes) : HeapTypes → Set where
  []  : Heap Γ []
  _∷_ : ∀ {τ Ψ} → Value Γ τ → Heap Γ Ψ → Heap Γ (τ ∷ Ψ)

-- Разыменование указателя
deref : ∀ {l Ψ} → Heap Ψ Ψ → l ✴ ∈ Ψ → l ∈ Ψ
deref Ψ p = {!!}

-- Куча почти одинаковых определений
wk-value : ∀ {Ψ Ψ' τ} → Ψ ⊆ Ψ' → Value Ψ τ → Value Ψ' τ

wk-tdiff : ∀ {Ψ Ψ' Γ} → TDiff Γ → Ψ ⊆ Ψ' → TDiff Γ
wk-tdiff tdempty ss = tdempty
wk-tdiff (tdchg tchg d) ss = tdchg tchg (wk-tdiff d ss)

wk-instr : ∀ {Ψ Ψ' Γ} {d : TDiff Γ} → (ss : Ψ ⊆ Ψ') → Instr Ψ Γ d → Instr Ψ' Γ (wk-tdiff d ss)
wk-instr ss (mov r v) = mov r (wk-value ss v)

wk-cinstr : ∀ {Ψ Ψ' Γ} → Ψ ⊆ Ψ' → ControlInstr Ψ Γ → ControlInstr Ψ' Γ
wk-cinstr ss (call f) = call (ss f)
wk-cinstr ss jmp[ f ] = jmp[ ss f ]
wk-cinstr ss (jmp f) = jmp (ss f)

wk-blk : ∀ {Ψ Ψ' Γ Δ} → (ss : Ψ ⊆ Ψ') → Block Ψ Γ Δ → Block Ψ' Γ (wk-tdiff Δ ss)
wk-blk ss halt = halt
wk-blk ss (↝ x) = ↝ (wk-cinstr ss x)
wk-blk ss (x ∙ b) = wk-instr ss {!x!} ∙ (wk-blk ss b)

wk-value ss (function x) = function (wk-blk ss x)
wk-value ss (ptr x)      = ptr (ss x)

-- Получение значения из heap по "адресу"
load : ∀ {l Ψ} → Heap Ψ Ψ → l ∈ Ψ → Value Ψ l
load (x ∷ vs) (here refl) = {!!}
load (x ∷ vs) (there p)   = {!!}

loadblk : ∀ {Γ Ψ} → Heap Ψ Ψ → blk Γ ∈ Ψ → NewBlk Ψ
loadblk Ψ f with load Ψ f
loadblk Ψ f | function x = _ , _ , x


-- Набор определений, показывающих, как CallCtx меняется при исполнении

-- На самом деле это тоже часть определения ControlInstr, ибо определяет
-- семантику каждой конкретной инструкции, но если засунуть что-нибудь
-- похожее в определение типа или конструкторы, сломается strict positivity
-- :(
-- Ограничение на стек хорошо бы засунуть в определение типа, потому что
-- без него инструкция `ret` может быть поставлена в неправильное место.
-- Правда, я не понимаю, действительно ли мне надо об этом задумываться
exec-control : ∀ {Γ Ψ} → Heap Ψ Ψ → CallCtx Ψ → ControlInstr Ψ Γ → CallCtx Ψ
exec-control H (cs , ret) (call f) = ret ∷ cs , loadblk H f
exec-control H (cs , ret) jmp[ f ] = cs , loadblk H (deref H f)
exec-control H (cs , ret) (jmp f)  = cs , loadblk H f

exec-blk : ∀ {Γ Ψ} {Δ : TDiff Γ} → Heap Ψ Ψ → CallCtx Ψ → Block Ψ Γ Δ → CallCtx Ψ
exec-blk {Γ} H (cs , ret) halt = cs , Γ , _ , halt
exec-blk H cc (↝ x) = exec-control H cc x
-- Просто инструкции не могут менять контекст исполнения, поэтому
-- они игнорируются
exec-blk H cc (i ∙ b) = exec-blk H cc b



-- Два блока считаются эквивалентными в одном контексте исполнения, если
-- они в итоге приводят к одному и тому же блоку с одинаковым контекстом
-- исполнения
data BlockEq {Ψ : HeapTypes} (H : Heap Ψ Ψ) (CC : CallCtx Ψ)
    : {Γ₁ Γ₂ : RegFileTypes} → {d₁ : TDiff Γ₁} {d₂ : TDiff Γ₂}
    → Block Ψ Γ₁ d₁ → Block Ψ Γ₂ d₂ → Set
    where
  -- Равные блоки эквивалентны
  equal  : ∀ {Γ Δ} → {B : Block Ψ Γ Δ} → BlockEq H CC B B
  -- Левый блок исполняет инструкцию
  left   : ∀ {Γ₁ Γ₂ Γ₃}
         → {d₁ : TDiff Γ₁} {d₂ : TDiff Γ₂} {d₃ : TDiff Γ₃}
         → {A : Block Ψ Γ₁ d₁} → {B : Block Ψ Γ₂ d₂} → {C : Block Ψ Γ₃ d₃}
         → projr (exec-blk H CC C) ≡ _ , _ , A
         → BlockEq H CC A B
         → BlockEq H CC C B
  -- Правый блок исполняет инструкцию
  right  : ∀ {Γ₁ Γ₂ Γ₃}
         → {d₁ : TDiff Γ₁} {d₂ : TDiff Γ₂} {d₃ : TDiff Γ₃}
         → {A : Block Ψ Γ₁ d₁} → {B : Block Ψ Γ₂ d₂} → {C : Block Ψ Γ₃ d₃}
         → projr (exec-blk H CC C) ≡ _ , _ , B
         → BlockEq H CC A B
         → BlockEq H CC A C
  -- Оба блока исполняют какие-то инструкции, меняющие CallCtx
  ctxchg : ∀ {Γ₁ Γ₂ Γ₁' Γ₂'}
         → {d₁ : TDiff Γ₁} {d₂ : TDiff Γ₂} {d₁' : TDiff Γ₁'} {d₂' : TDiff Γ₂'}
         → {CC' : CallCtx Ψ}
         → {A' : Block Ψ Γ₁' d₁'} {B' : Block Ψ Γ₂' d₂'}
         → BlockEq H CC' A' B'
         → {A : Block Ψ Γ₁ d₁}
         → exec-blk H CC A ≡ projl CC' , _ , _ , A'
         → {B : Block Ψ Γ₂ d₂} 
         → exec-blk H CC B ≡ projl CC' , _ , _ , B'
         → BlockEq H CC A B
\end{code}
