\begin{code}
module NotSSAInstructions where

open import OXIj.BrutalDepTypes
open Data-List
open Data-Any

data Type : Set

RegFileTypes = List Type
HeapTypes    = List Type

data Type where
  blk : (Γ : RegFileTypes) → Type -- Кусок кода, рассчитывающий на наличие
                                  -- регистров Γ в текущем контексте исполнения
  _✴  : Type → Type               -- Указатель

open Membership {A = Type} _≡_

module TDiffs where
  {-
    TDiff описывает только изменения типов регистров и нужен
    мне только для описания инструкций и блоков кода
    
    TDiff должен описывать:

    * добавленные регистры
    * изменённые регистры

    При этом для TDiff должны быть определены dempty и dappend
  -}
  data TChg (Γ : RegFileTypes) : Set where
    chgnr : Type → TChg Γ
    chgcr : ∀ {r} → r ∈ Γ → (r' : Type) → TChg Γ
    chgur : ∀ {s r} → s ∈ Γ → r ∈ Γ → (r' : Type) → TChg Γ

  appChg : (Γ : RegFileTypes) → TChg Γ → RegFileTypes
  appChg Γ (chgnr x) = x ∷ Γ
  appChg (_ ∷ Γ) (chgcr (here refl) r') = r' ∷ Γ
  appChg (a ∷ Γ) (chgcr (there r) r') = a ∷ appChg Γ (chgcr r r')
  -- Да, семантически chgur и chgcr одинаковы с точки зрения
  -- изменения типов регистров, s ∈ Γ нужен будет потом, чтобы
  -- случайно не выкинуть используемое значение регистра
  -- Зачем тогда здесь паттернматчиться и копипастить предыдущие
  -- две строки? Затем, что иначе терминейшн-чекер фейлится :\
  appChg (_ ∷ Γ) (chgur s (here refl) r') = r' ∷ Γ
  appChg (a ∷ Γ) (chgur s (there r) r') = a ∷ appChg Γ (chgcr r r')

  data TDiff (Γ : RegFileTypes) : Set where
    tdempty  : TDiff Γ
    -- Почему я строю диффы в обратную сторону? :\
    tdchg : (chg : TChg Γ) → TDiff (appChg Γ chg) → TDiff Γ

  tdapply : (Γ : RegFileTypes) → TDiff Γ → RegFileTypes
  tdapply Γ tdempty = Γ
  tdapply Γ (tdchg chg td) = tdapply (appChg Γ chg) td

  tdappend : ∀ {Γ} → (td : TDiff Γ) → TDiff (tdapply Γ td) → TDiff Γ
  tdappend tdempty b = b
  tdappend (tdchg chg a) b = tdchg chg (tdappend a b)
open TDiffs

{-
  Многие определения используют heap, но никак его не меняют,
  потому в модуле с фиксированным Ψ
-}
module FixedHeap (Ψ : HeapTypes) where
  {-
    Для простоты будем считать, что регистры никогда не меняют тип,
    а инструкции вроде `mov` просто "добавляют" ещё один регистр в
    контекст (а процессор сам разберётся, как куда замапить
    используемые регистры).
    Да, так скапливается много "мусорных" регистров, которые уже
    никогда не будут использованы. Теоретически можно добавить
    что-нибудь вроде "забывания" регистров, например, в конце блока
    (это даже будет эмулировать некоторый scope для блоков), но мне
    немножко лениво это делать, и, вообще, это, по-моему, немножко
    анрелейтед.
  -}

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
  data Block (Γ : RegFileTypes) : TDiff Γ → Set

  {-
    Управляющая инструкция не добавляет никаких новых регистров, поэтому,
    в отличие от блока, имеет только один параметр.
  -}
  data ControlInstr (Γ : RegFileTypes) : Set
    where
    call   : (f : blk Γ ∈ Ψ) → ControlInstr Γ
    jmp[_] : (f : (blk Γ) ✴ ∈ Ψ) → ControlInstr Γ
    -- А вот эта инструкция мне на самом деле не нужна,
    -- она здесь просто потому что я могу
    jmp    : (f : blk Γ ∈ Ψ) → ControlInstr Γ

  data Value : Type → Set where
    function : {Γ : RegFileTypes} → {d : TDiff Γ} → Block Γ d → Value (blk Γ)
    ptr      : ∀ {τ} → τ ∈ Ψ → Value (τ ✴)

  -- Возможно, имеет смысл сюда засунуть не TDiff, а TChg
  data Instr (Γ : RegFileTypes) : TDiff Γ → Set where
    -- Просто пример того, как может выглядеть инструкция
    new  : ∀ {τ} → Value τ → Instr Γ (tdchg (chgnr τ) tdempty)
    -- Я могу делать инструкции, _меняющие_ регистры, а не добавляющие новые!
    mov  : ∀ {r τ} → (r∈Γ : r ∈ Γ) → Value τ → Instr Γ (tdchg (chgcr r∈Γ τ) tdempty)
    -- И даже инструкции, которые не просто затирают старое значение, а апдейтят его
    ld   : ∀ {r τ} → (s : τ ✴ ∈ Γ) → (d : r ∈ Γ) → Instr Γ (tdchg (chgur s d τ) tdempty)

  data Block (Γ : RegFileTypes) where
    -- Блок, завершающий исполнение
    halt : Block Γ tdempty
    -- Блок, переходящий куда-либо в соответствии с результатом
    -- исполнения управляющей инструкции
    ↝    : ControlInstr Γ → Block Γ tdempty
    -- Какая-нибудь инструкция внутри блока
    _∙_  : ∀ {d' d} → Instr Γ d' → Block (tdapply Γ d') d → Block Γ (tdappend d' d)

  -- Иногда из функции надо вернуть абсолютно любой блок,
  -- с любыми параметрами типа (как Γ и Δ), как это нормально делается?
  -- Или использовать Σ и есть правильный способ?
  NewBlk = Σ RegFileTypes (λ Γ → Σ (TDiff Γ) (λ d → Block Γ d))

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
wk-instr ss (new x) = new (wk-value ss x)
wk-instr ss (mov r v) = mov r (wk-value ss v)
wk-instr ss (ld s d) = ld s d

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

-- Динамическая линковка

-- plt состоит всего из одной инструкции, потому что я рассчитываю на то,
-- что весь нужный код уже загружен в память, и got заполнен
plt-stub : ∀ {Γ Ψ} → (blk Γ) ✴ ∈ Ψ → Block Ψ Γ tdempty
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
        → loadblk H (plt f) ≡ Γ , tdempty , ↝ jmp[ got f ]
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
