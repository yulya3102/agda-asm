В первую очередь стоит описывать, как определить корректность 
ассемблерного кода и какие типы должны быть использованы для этого.

Все значения, находящиеся либо в памяти, либо в регистрах, должны
иметь какой-либо тип. Так же стоит описывать состояние набора регистров,
потому что блоки кода могут рассчитывать на наличие в регистрах значений
конкретных типов. То же самое можно сказать и про состояние памяти.

\begin{code}
module Instructions where

open import OXIj.BrutalDepTypes
open Data-List

data Type : Set
RegFileTypes : Set
HeapTypes : Set
\end{code}

Состояние регистров можно представить списком типов, причем каждому
регистру должен соответстовать элемент списка. В этом случае регистр
является индексом в этом списке.

Аналогичные рассуждения верны и для состояния памяти.

\begin{code}
RegFileTypes = List Type
HeapTypes    = List Type
\end{code}

Рассматриваемыми мной значениями являются только блоки кода и указатели
куда-либо. При этом корректность исполнения блока кода можно гарантировать,
ограничив состояние регистров и памяти, которые должны быть на момент начала
исполнения блока. Но для простоты считаем, что значения, находящиеся
в памяти, никогда не изменяются, поэтому тип блока описывает только
требуемое состояние регистров.

\begin{code}
data Type where
  _✴  : Type → Type
  blk : (Γ : RegFileTypes) → Type

open Data-Any
open Membership {A = Type} _≡_
\end{code}

Как говорилось ранее, значения, лежащие в памяти, никогда не изменяются.
При этом все определения, касающиеся кода, могут на ссылаться на память,
потому целесообразно поместить эти определения в модуль с фиксированным
состоянием памяти.

\begin{code}
module FixedHeap (Ψ : HeapTypes) where
\end{code}

% не все йогурты одинаково полезны
Не все инструкции изменяют одинаковые части контекста исполнения.
Некоторые инструкции изменяют состояние регистров, некоторые определяют,
какой код будет исполняться дальше. \textbf{TODO: мне очень хочется придумать
название для первого вида инструкций, потому что меня откровенно бесит
называть их просто инструкциями} Второй тип инструкций будем называть
управляющими инструкциями.

Принимая во внимание тот факт, что с точки зрения компоновки необходимо
рассматривать лишь переходы между различными частями загруженного в
память кода, удобно ввести понятие базового блока кода — последовательности
инструкций, не содержащей никаких переходов, и впоследствии рассматривать
лишь переходы между этими блоками. В терминах различных видов инструкций
определение блока описывается как последовательность инструкций, меняющих
регистры, заканчивающаяся управляющей инструкцией.

Блок должен описывать, в каком контексте он будет корректно исполнен и
как он изменит этот контекст. Изменением контекста является список
добавляемых к этому контексту регистров.
\begin{code}
  data Block (Γ : RegFileTypes) : (Δ : RegFileTypes) → Set
\end{code}

Управляющая инструкция должна знать, в каком контексте она исполняется,
чтобы гарантировать, что блок, на который происходит переход, будет
исполнен корректно.

\begin{code}
  data ControlInstr (Γ : RegFileTypes) : Set
    where
    call   : (f : blk Γ ∈ Ψ) → ControlInstr Γ
    jmp[_] : (f : (blk Γ) ✴ ∈ Ψ) → ControlInstr Γ
    -- А вот эта инструкция мне на самом деле не нужна,
    -- она здесь просто потому что я могу
    jmp    : (f : blk Γ ∈ Ψ) → ControlInstr Γ

  data Value : Type → Set where
    function : {Γ Δ : RegFileTypes} → Block Γ Δ → Value (blk Γ)
    ptr      : ∀ {τ} → τ ∈ Ψ → Value (τ ✴)

  data Instr (Γ : RegFileTypes) : (Δ : RegFileTypes) → Set where
    -- Просто пример того, как может выглядеть инструкция
    mov  : ∀ {τ} → Value τ → Instr Γ [ τ ]

  data Block (Γ : RegFileTypes) where
    -- Блок, завершающий исполнение
    halt : Block Γ []
    -- Блок, переходящий куда-либо в соответствии с результатом
    -- исполнения управляющей инструкции
    ↝    : ControlInstr Γ → Block Γ []
    -- Какая-нибудь инструкция внутри блока
    _∙_  : ∀ {Γ' Δ} → Instr Γ Γ' → Block (Γ ++ Γ') Δ → Block Γ (Δ ++ Γ')

  -- Иногда из функции надо вернуть абсолютно любой блок,
  -- с любыми параметрами типа (как Γ и Δ), как это нормально делается?
  -- Или использовать Σ и есть правильный способ?
  NewBlk = Σ RegFileTypes (λ Γ → Σ RegFileTypes (λ Δ → Block Γ Δ))

open FixedHeap

-- Набор heap-related определений

data Heap : HeapTypes → Set where
  []  : Heap []
  -- Value Ψ τ может ссылаться на какие-то значения из Ψ
  -- (и, соответственно, из H)
  _,_ : ∀ {τ Ψ} → (H : Heap Ψ) → Value Ψ τ → Heap (τ ∷ Ψ)

-- Разыменование указателя
deref : ∀ {l Ψ} → Heap Ψ → l ✴ ∈ Ψ → l ∈ Ψ
deref [] ()
deref (vs , function x) (here ())
deref (vs , ptr p)      (here refl) = there p
deref (vs , x)          (there p)   = there (deref vs p)

-- Куча почти одинаковых определений
wk-value : ∀ {Ψ Ψ' τ} → Ψ ⊆ Ψ' → Value Ψ τ → Value Ψ' τ

wk-instr : ∀ {Ψ Ψ' Γ Δ} → Ψ ⊆ Ψ' → Instr Ψ Γ Δ → Instr Ψ' Γ Δ
wk-instr ss (mov x) = mov (wk-value ss x)

wk-cinstr : ∀ {Ψ Ψ' Γ} → Ψ ⊆ Ψ' → ControlInstr Ψ Γ → ControlInstr Ψ' Γ
wk-cinstr ss (call f) = call (ss f)
wk-cinstr ss jmp[ f ] = jmp[ ss f ]
wk-cinstr ss (jmp f) = jmp (ss f)

wk-blk : ∀ {Ψ Ψ' Γ Δ} → Ψ ⊆ Ψ' → Block Ψ Γ Δ → Block Ψ' Γ Δ
wk-blk ss halt = halt
wk-blk ss (↝ x) = ↝ (wk-cinstr ss x)
wk-blk ss (x ∙ b) = wk-instr ss x ∙ wk-blk ss b

wk-value ss (function x) = function (wk-blk ss x)
wk-value ss (ptr x)      = ptr (ss x)

-- Получение значения из heap по "адресу"
load : ∀ {l Ψ} → Heap Ψ → l ∈ Ψ → Value Ψ l
load (vs , x) (here refl) = wk-value there x
load (vs , x) (there p)   = wk-value there (load vs p)

loadblk : ∀ {Γ Ψ} → Heap Ψ → blk Γ ∈ Ψ → NewBlk Ψ
loadblk Ψ f with load Ψ f
loadblk Ψ f | function x = _ , _ , x

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

-- Набор определений, показывающих, как CallCtx меняется при исполнении

-- На самом деле это тоже часть определения ControlInstr, ибо определяет
-- семантику каждой конкретной инструкции, но если засунуть что-нибудь
-- похожее в определение типа или конструкторы, сломается strict positivity
-- :(
-- Ограничение на стек хорошо бы засунуть в определение типа, потому что
-- без него инструкция `ret` может быть поставлена в неправильное место.
-- Правда, я не понимаю, действительно ли мне надо об этом задумываться
exec-control : ∀ {Γ Ψ} → Heap Ψ → CallCtx Ψ → ControlInstr Ψ Γ → CallCtx Ψ
exec-control H (cs , ret) (call f) = ret ∷ cs , loadblk H f
exec-control H (cs , ret) jmp[ f ] = cs , loadblk H (deref H f)
exec-control H (cs , ret) (jmp f)  = cs , loadblk H f

exec-blk : ∀ {Γ Δ Ψ} → Heap Ψ → CallCtx Ψ → Block Ψ Γ Δ → CallCtx Ψ
exec-blk {Γ} H (cs , ret) halt = cs , Γ , _ , halt
exec-blk H cc (↝ x) = exec-control H cc x
-- Просто инструкции не могут менять контекст исполнения, поэтому
-- они игнорируются
exec-blk H cc (i ∙ b) = exec-blk H cc b



-- Два блока считаются эквивалентными в одном контексте исполнения, если
-- они в итоге приводят к одному и тому же блоку с одинаковым контекстом
-- исполнения
data BlockEq {Ψ : HeapTypes} (H : Heap Ψ) (CC : CallCtx Ψ)
    : {Γ₁ Γ₂ Δ₁ Δ₂ : RegFileTypes} → Block Ψ Γ₁ Δ₁ → Block Ψ Γ₂ Δ₂ → Set
    where
  -- Равные блоки эквивалентны
  equal  : ∀ {Γ Δ} → {B : Block Ψ Γ Δ} → BlockEq H CC B B
  -- Левый блок исполняет инструкцию
  left   : ∀ {Δ₁ Δ₂ Δ₃ Γ₁ Γ₂ Γ₃}
         → {A : Block Ψ Γ₁ Δ₁} → {B : Block Ψ Γ₂ Δ₂} → {C : Block Ψ Γ₃ Δ₃}
         → projr (exec-blk H CC C) ≡ _ , _ , A
         → BlockEq H CC A B
         → BlockEq H CC C B
  -- Правый блок исполняет инструкцию
  right  : ∀ {Δ₁ Δ₂ Δ₃ Γ₁ Γ₂ Γ₃}
         → {A : Block Ψ Γ₁ Δ₁} → {B : Block Ψ Γ₂ Δ₂} → {C : Block Ψ Γ₃ Δ₃}
         → projr (exec-blk H CC C) ≡ _ , _ , B
         → BlockEq H CC A B
         → BlockEq H CC A C
  -- Оба блока исполняют какие-то инструкции, меняющие CallCtx
  ctxchg : ∀ {Δ₁ Δ₂ Δ₁' Δ₂' Γ₁ Γ₂ Γ₁' Γ₂'}
         → {CC' : CallCtx Ψ}
         → {A' : Block Ψ Γ₁' Δ₁'} {B' : Block Ψ Γ₂' Δ₂'}
         → BlockEq H CC' A' B'
         → {A : Block Ψ Γ₁ Δ₁}
         → exec-blk H CC A ≡ projl CC' , _ , _ , A'
         → {B : Block Ψ Γ₂ Δ₂} 
         → exec-blk H CC B ≡ projl CC' , _ , _ , B'
         → BlockEq H CC A B

-- Динамическая линковка

-- plt состоит всего из одной инструкции, потому что я рассчитываю на то,
-- что весь нужный код уже загружен в память, и got заполнен
plt-stub : ∀ {Γ Ψ} → (blk Γ) ✴ ∈ Ψ → Block Ψ Γ []
plt-stub label = ↝ (jmp[ label ])

-- Преобразования heap

plt-heaptypes : HeapTypes → HeapTypes
-- На каждый блок в heap добавляются соответствующие got и plt (который,
-- очевидно, имеет тот же тип, что и сам блок)
plt-heaptypes (blk Γ ∷ Ψ) = blk Γ ∷ blk Γ ✴ ∷ blk Γ ∷ (plt-heaptypes Ψ)
-- Всё остальное остаётся неизменным
plt-heaptypes (x ∷ Ψ) = x ∷ (plt-heaptypes Ψ)
plt-heaptypes [] = []

plt-⊆ : ∀ {Ψ} → Ψ ⊆ plt-heaptypes Ψ
plt-⊆ {x = blk Γ} (Data-Any.here refl) = Data-Any.there $ Data-Any.there (Data-Any.here refl)
plt-⊆ {x = x ✴} (Data-Any.here refl) = Data-Any.here refl
plt-⊆ {blk Γ ∷ ψs} (there i) = there (there (there (plt-⊆ i)))
plt-⊆ {ψ ✴ ∷ ψs} (there i) = there (plt-⊆ i)

plt-heap : ∀ {Ψ} → Heap Ψ → Heap (plt-heaptypes Ψ)
plt-heap [] = []
plt-heap (vs , function f) = ((plt-heap vs , function (wk-blk plt-⊆ f)) , ptr (here refl)) , function (plt-stub (here refl))
plt-heap (vs , ptr x) = plt-heap vs , ptr (plt-⊆ x)

-- plt и got

plt : ∀ {Γ Ψ} → (blk Γ) ∈ Ψ → (blk Γ) ∈ plt-heaptypes Ψ
plt (here refl) = here refl
plt {Ψ = blk Δ ∷ Ψ} (there f) = there (there (there (plt f)))
plt {Ψ = x ✴ ∷ Ψ} (there f) = there (plt f)

got : ∀ {Γ Ψ} → (blk Γ) ∈ Ψ → (blk Γ) ✴ ∈ plt-heaptypes Ψ
got (here refl) = there (here refl)
got {Ψ = blk Δ ∷ Ψ} (there f) = there (there (there (got f)))
got {Ψ = x ✴ ∷ Ψ} (there f) = there (got f)

-- Преобразование кода

plt-code : ∀ {Ψ Γ Δ} → Block Ψ Γ Δ → Block (plt-heaptypes Ψ) Γ Δ
plt-code halt = halt
plt-code (↝ (call f)) = ↝ (call (plt f))
plt-code (↝ (jmp[_] f)) = ↝ (jmp[ plt-⊆ f ])
plt-code (↝ (jmp f)) = ↝ (jmp (plt-⊆ f ))
plt-code (i ∙ b) = wk-instr plt-⊆ i ∙ plt-code b

-- Сами доказательства

jmp[]-proof : ∀ {Ψ Γ Δ} → {CC : CallCtx Ψ}
           → {H : Heap Ψ}
           → {A : Block Ψ Γ Δ}
           → (f : (blk Γ) ✴ ∈ Ψ)
           → loadblk H (deref H f) ≡ _ , _ , A
           → BlockEq H CC A (↝ jmp[ f ])
jmp[]-proof {Ψ} {CC = CC} {H = H} {A = A} f p = right p equal

call-proof : ∀ {Ψ Γ} → (CC : CallCtx Ψ) → {A : NewBlk Ψ}
           → {H : Heap Ψ}
           → (f : (blk Γ) ∈ Ψ)
           → loadblk H f ≡ A
           → exec-blk H CC (↝ (call f)) ≡ ((projr CC ∷ projl CC) , A)
call-proof CC f p rewrite p = refl

loadplt : ∀ {Ψ Γ} → (H : Heap (plt-heaptypes Ψ)) → (f : blk Γ ∈ Ψ)
        → loadblk H (plt f) ≡ Γ , [] , ↝ jmp[ got f ]
loadplt H f = {!!}

jmp[]-plt-stub : ∀ {Ψ Γ} → (f : blk Γ ∈ Ψ) → plt-stub (got f) ≡ ↝ jmp[ got f ]
jmp[]-plt-stub f = refl

loadblk-Γ : ∀ {Ψ Γ} → (H : Heap Ψ) → (f : blk Γ ∈ Ψ) → projl (loadblk H f) ≡ Γ
loadblk-Γ H f = {!!}

plt-fun-eq : ∀ {Γ Ψ}
           → (H : Heap (plt-heaptypes Ψ))
           → (cc : CallCtx (plt-heaptypes Ψ))
           → (f : blk Γ ∈ Ψ)
           → BlockEq H cc
             (projr $ projr (loadblk H (plt-⊆ f)))
             (plt-stub (got f))
plt-fun-eq H cc f with jmp[]-plt-stub f | loadblk-Γ H (plt-⊆ f)
plt-fun-eq H cc f | refl | r = {!!}

proof : ∀ {Γ Ψ}
      → (H : Heap (plt-heaptypes Ψ))
      → (f : blk Γ ∈ Ψ)
      → (cc : CallCtx (plt-heaptypes Ψ)) -- для любого контекста исполнения
      → BlockEq H cc                     -- эквивалентны
        (wk-blk plt-⊆ (↝ (call f)))      -- вызов функции f напрямую
        (↝ (call (plt f)))               -- и вызов соответствующего plt
proof {Γ = Γ} {Ψ = Ψ} H f ctx = ctxchg after-call just-call plt-call
    where
    newblock-f   = loadblk H (plt-⊆ f)
    called-block = projr $ projr newblock-f

    just-call : exec-blk H ctx (↝ (call $ plt-⊆ f)) ≡
                projr ctx ∷ projl ctx , newblock-f
    just-call = call-proof ctx (plt-⊆ f) refl

    plt-call : exec-blk H ctx (↝ (call $ plt f)) ≡
               projr ctx ∷ projl ctx , _ , _ , ↝ jmp[ got f ]
    plt-call = call-proof ctx (plt f) (loadplt H f)

    after-call : BlockEq H (projr ctx ∷ projl ctx , newblock-f)
                 called-block
                 (↝ jmp[ got f ])
    after-call = plt-fun-eq H (projr ctx ∷ projl ctx , newblock-f) f
\end{code}
