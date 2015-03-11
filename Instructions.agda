module Instructions where

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
  any : Type                      -- Любой другой тип

module List-Helpers (A : Set) where
  open Membership {A = A} _≡_

  drop : ∀ {x xs} → x ∈ xs → Σ (List A) (flip _⊆_ xs)
  drop {xs = x ∷ xs} (here pa) = xs , there
  drop {xs = _ ∷ xs} (there x) with drop x
  drop {x}  {y ∷ xs} (there _) | ys , ys⊆xs = y ∷ ys , ⊆-++-both-left [ y ] ys⊆xs

open List-Helpers Type

open Membership {A = Type} _≡_
postulate ⊆-++ : ∀ {Γ Δ Γ' Δ'} → Γ' ⊆ Γ → Δ' ⊆ Δ → (Γ' ++ Δ') ⊆ (Γ ++ Δ)

{-
  Я понятия не имею, как нормально заимплементить heap, и полагаюсь
  на то, что всё взаимодействие с ним будет корректным: все нужные
  значения загружены в память, и я всегда получу ровно то значение,
  на которое я рассчитываю. Конкретные примеры такого лютого
  читерства — запостулированные куски кода.
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

    Блок задаёт, на какой контекст регистров он рассчитывает, и какие
    новые регистры добавляет к этому контексту.
  -}
  -- `Block` starts with registers Γ, all of them are
  -- considered as free registers. Some of these
  -- registers are bounded, so they are removed from
  -- list of free registers. Result list of free
  -- registers is Δ, which is obviously must be subset
  -- of Γ. `Block` also can introduce some new registers.
  data Block {Γ : RegFileTypes} : {Δ : RegFileTypes}
    → (free : Δ ⊆ Γ) → (new : RegFileTypes) → Set

  {-
    Управляющая инструкция не добавляет никаких новых регистров, поэтому,
    в отличие от блока, имеет только один параметр.
  -}
  data ControlInstr (Γ : RegFileTypes) : Set
    where
    call   : (f : blk Γ ∈ Ψ) → ControlInstr Γ
    jmp[_] : (f : (blk Γ) ✴ ∈ Ψ) → ControlInstr Γ
    -- А вот эта инструкция мне на самом деле не нужна, она здесь because I can
    jmp    : (f : blk Γ ∈ Ψ) → ControlInstr Γ

  data Value : Type → Set where
    function : {free ss-free new : RegFileTypes} → {ss : ss-free ⊆ free} → Block ss new → Value (blk free)
    ptr      : ∀ {τ} → τ ∈ Ψ → Value (τ ✴)

  data Instr {free : RegFileTypes} : {free' : RegFileTypes} → free' ⊆ free → (new : RegFileTypes) → Set where
    any  : ∀ {Γ} Δ → (ss : Γ ⊆ free) → Instr ss Δ
    mov  : ∀ {τ} → Value τ → Instr id [ τ ]
    movr : ∀ {τ σ} → (r : τ ∈ free) → Value σ → Instr (projr (drop r)) [ σ ]

  data Block {Γ : RegFileTypes} where
    halt : Block id []
    ↝    : ControlInstr Γ → Block id []
    _∙_  : ∀ {new new' Δ Δ' Δ''}
         → {ss   : Δ ⊆ Γ}           → Instr ss new
         → {new-ss : Δ' ⊆ new} {old-ss : Δ'' ⊆ Δ} → Block (⊆-++ new-ss old-ss) new'
         → Block (⊆-trans old-ss ss) (Δ' ++ new')

  NewBlk = Σ RegFileTypes (λ Γ → Σ RegFileTypes (λ Δ → Σ (Δ ⊆ Γ) (λ free → Σ RegFileTypes (Block free))))

  postulate deref : ∀ {l} → l ✴ ∈ Ψ → l ∈ Ψ
  postulate load : ∀ {l} → l ∈ Ψ → Value l

  loadblk : ∀ {Γ} → blk Γ ∈ Ψ → NewBlk
  loadblk f with load f
  loadblk f | function x = _ , _ , _ , _ , x

  postulate loadblk-≡ : ∀ {Γ A} → (f : blk Γ ∈ Ψ) → loadblk f ≡ Γ , A

  CallStack = List NewBlk
  CallCtx = CallStack × NewBlk
  
  -- На самом деле это тоже часть определения ControlInstr, ибо определяет
  -- семантику каждой конкретной инструкции, но если засунуть что-нибудь
  -- похожее в определение типа или конструкторы, сломается strict positivity
  -- :(
  -- Ограничение на стек хорошо бы засунуть в определение типа, потому что
  -- без него инструкция `ret` может быть поставлена в неправильное место
  exec-control : ∀ {Γ} → CallCtx → ControlInstr Γ → CallCtx
  exec-control (cs , ret) (call f) = ret ∷ cs , loadblk f
  exec-control (cs , ret) jmp[ f ] = cs , loadblk (deref f)
  exec-control (cs , ret) (jmp f)  = cs , loadblk f

  exec-blk : ∀ {Γ Δ Δ'} → {ss : Δ ⊆ Δ'} → CallCtx → Block ss Γ → CallCtx
  exec-blk {Δ' = Γ} (cs , ret) halt = cs , Γ , _ , _ , _ , halt
  exec-blk cc (↝ x) = exec-control cc x
  exec-blk cc (i ∙ b) = exec-blk cc b
  
  -- Два блока считаются эквивалентными в одном контексте исполнения, если
  -- они в итоге приводят к одному и тому же блоку с одинаковым контекстом
  -- исполнения
  data BlockEq (CC : CallCtx) :
    {Γ₁ Γ₂ Δ₁ Δ₂ new₁ new₂ : RegFileTypes} →
    {free₁ : Δ₁ ⊆ Γ₁} {free₂ : Δ₂ ⊆ Γ₂} →
    Block free₁ new₁ → Block free₂ new₂ → Set where
    eq : ∀ {Γ Δ new} → {free : Δ ⊆ Γ} → {B : Block free new} → BlockEq CC B B
    nr : ∀ {Δ₁ Δ₂ Δ₃ Γ₁ Γ₂ Γ₃ new₁ new₂ new₃} → {free₁ : Δ₁ ⊆ Γ₁} {free₂ : Δ₂ ⊆ Γ₂} {free₃ : Δ₃ ⊆ Γ₃} → {A : Block free₁ new₁} → {B : Block free₂ new₂} → {C : Block free₃ new₃} → projr (exec-blk CC C) ≡ _ , _ , _ , _ , A → BlockEq CC A B → BlockEq CC C B
    nl : ∀ {Δ₁ Δ₂ Δ₃ Γ₁ Γ₂ Γ₃ new₁ new₂ new₃} → {free₁ : Δ₁ ⊆ Γ₁} {free₂ : Δ₂ ⊆ Γ₂} {free₃ : Δ₃ ⊆ Γ₃} → {A : Block free₁ new₁} → {B : Block free₂ new₂} → {C : Block free₃ new₃} → projr (exec-blk CC C) ≡ _ , _ , _ , _ , B → BlockEq CC A B → BlockEq CC A C
    cc : ∀ {Δ₁ Δ₂ Δ₁' Δ₂' Γ₁ Γ₂ Γ₁' Γ₂' new₁ new₂ new₁' new₂'} → {free₁ : Δ₁ ⊆ Γ₁} {free₂ : Δ₂ ⊆ Γ₂} {free₁' : Δ₁' ⊆ Γ₁'} {free₂' : Δ₂' ⊆ Γ₂'} → {B' : Block free₂' new₂'} → {A : Block free₁ new₁} → {B : Block free₂ new₂} {A' : Block free₁' new₁'} → {CC' : CallCtx} → (exec-blk CC A) ≡ projl CC' , _ , _ , _ , _ , A' → exec-blk CC B ≡ projl CC' , _ , _ , _ , _ , B' → BlockEq CC' A' B' → BlockEq CC A B

open FixedHeap public

module PLTize where

-- plt состоит всего из одной инструкции, потому что я рассчитываю на то,
-- что весь нужный код уже загружен в память, и got заполнен
plt-stub : ∀ {Γ Ψ} → (blk Γ) ✴ ∈ Ψ → Block Ψ {Γ = Γ} id []
plt-stub label = ↝ (jmp[ label ])

-- Вот это полная дрянь, я задаю, значения какого типа добавятся в heap,
-- но не указываю, какие именно это будут значения, хотя надо бы
pltize-heap : HeapTypes → HeapTypes
-- На каждый блок в heap добавляются соответствующие got и plt (который,
-- очевидно, имеет тот же тип, что и сам блок)
pltize-heap (blk Γ ∷ Ψ) = blk Γ ∷ blk Γ ✴ ∷ blk Γ ∷ Ψ
-- Всё остальное остаётся неизменным
pltize-heap Ψ = Ψ

pltize-⊆ : ∀ {Ψ} → Ψ ⊆ pltize-heap Ψ
pltize-⊆ {x = blk Γ} (Data-Any.here refl) = Data-Any.there $ Data-Any.there (Data-Any.here refl)
pltize-⊆ {x = x ✴} (Data-Any.here refl) = Data-Any.here refl
pltize-⊆ {x = any} (Data-Any.here refl) = Data-Any.here refl
pltize-⊆ {ψ ∷ ψs} {blk Γ} (Data-Any.there i) = {!!}
pltize-⊆ {ψ ∷ ψs} {x ✴} (Data-Any.there i) = {!!}
pltize-⊆ {ψ ∷ ψs} {any} (Data-Any.there i) = {!!}

plt : ∀ {Γ Ψ} → (blk Γ) ∈ Ψ → (blk Γ) ∈ pltize-heap Ψ
plt = {!!}

got : ∀ {Γ Ψ} → (blk Γ) ∈ Ψ → (blk Γ) ✴ ∈ pltize-heap Ψ
got = {!!}

∈-⊆ : ∀ {x A B} → x ∈ A → A ⊆ B → x ∈ B
∈-⊆ = {!!}

wk-instr : ∀ {Ψ Ψ' Γ Δ Δ'} → {ss : Δ ⊆ Δ'} → Ψ ⊆ Ψ' → Instr Ψ ss Γ → Instr Ψ' ss Γ
wk-instr = {!!}

wk-blk : ∀ {Ψ Ψ' Γ Δ Δ'} → {ss : Δ ⊆ Δ'} → Ψ ⊆ Ψ' → Block Ψ ss Γ → Block Ψ' ss Γ
wk-blk = {!!}

pltize-code : ∀ {Ψ Γ Δ Δ'} → {ss : Δ' ⊆ Δ} → Block Ψ ss Γ → Block (pltize-heap Ψ) ss Γ
pltize-code halt = halt
pltize-code (↝ (call f)) = ↝ (call (∈-⊆ f pltize-⊆))
pltize-code (↝ (jmp[_] f)) = ↝ (jmp[ ∈-⊆ f pltize-⊆ ])
pltize-code (↝ (jmp f)) = ↝ (jmp (∈-⊆ f pltize-⊆ ))
pltize-code (i ∙ b) = wk-instr pltize-⊆ i ∙ pltize-code b

jmp[]-proof : ∀ {Ψ Γ Δ new} → {CC : CallCtx Ψ}
           → {free : Δ ⊆ Γ}
           → {A : Block Ψ free new}
           → (f : (blk Γ) ✴ ∈ Ψ)
           → loadblk Ψ (deref Ψ f) ≡ _ , _ , _ , _ , A
           → BlockEq Ψ CC A (↝ jmp[ f ])
jmp[]-proof {Ψ} {CC = CC} {A = A} f p = nl (loadblk-≡ Ψ (deref Ψ f)) eq

call-proof : ∀ {Ψ Γ} → (CC : CallCtx Ψ) → {A : NewBlk Ψ}
           → (f : (blk Γ) ∈ Ψ)
           → loadblk Ψ f ≡ A
           → exec-blk Ψ CC (↝ (call f)) ≡ ((projr CC ∷ projl CC) , A)
call-proof CC f p rewrite p = refl

proof : ∀ {Γ Ψ}
      → (f : blk Γ ∈ Ψ)
      → (cc : CallCtx (pltize-heap Ψ))
      → BlockEq (pltize-heap Ψ) cc (wk-blk pltize-⊆ (↝ (call f))) (↝ (call (plt f)))
proof {Ψ = Ψ} f ctx = cc (call-proof ctx (∈-⊆ f pltize-⊆) (loadblk-≡ (pltize-heap Ψ) (∈-⊆ f pltize-⊆))) (call-proof ctx (plt f) (loadblk-≡ (pltize-heap Ψ) (plt f))) (jmp[]-proof (got f) (loadblk-≡ (pltize-heap Ψ) (deref (pltize-heap Ψ) (got f))))
