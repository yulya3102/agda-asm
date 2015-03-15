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

open Membership {A = Type} _≡_

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

    Блок задаёт, на какой контекст регистров Γ он рассчитывает, и какие
    новые регистры Δ добавляет к этому контексту.
  -}
  data Block (Γ : RegFileTypes) : (Δ : RegFileTypes) → Set

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
    function : {Γ Δ : RegFileTypes} → Block Γ Δ → Value (blk Γ)
    ptr      : ∀ {τ} → τ ∈ Ψ → Value (τ ✴)

  data Instr (Γ : RegFileTypes) : (Δ : RegFileTypes) → Set where
    any  : ∀ Δ → Instr Γ Δ
    mov  : ∀ {τ} → Value τ → Instr Γ [ τ ]

  data Block (Γ : RegFileTypes) where
    halt : Block Γ []
    ↝    : ControlInstr Γ → Block Γ []
    _∙_  : ∀ {Γ' Δ} → Instr Γ Γ' → Block (Γ ++ Γ') Δ → Block Γ (Δ ++ Γ')

  NewBlk = Σ RegFileTypes (λ Γ → Σ RegFileTypes (λ Δ → Block Γ Δ))

  postulate deref : ∀ {l} → l ✴ ∈ Ψ → l ∈ Ψ
  postulate load : ∀ {l} → l ∈ Ψ → Value l

  loadblk : ∀ {Γ} → blk Γ ∈ Ψ → NewBlk
  loadblk f with load f
  loadblk f | function x = _ , _ , x

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

  exec-blk : ∀ {Γ Δ} → CallCtx → Block Γ Δ → CallCtx
  exec-blk {Γ} (cs , ret) halt = cs , Γ , _ , halt
  exec-blk cc (↝ x) = exec-control cc x
  exec-blk cc (i ∙ b) = exec-blk cc b
  
open FixedHeap public

-- Два блока считаются эквивалентными в одном контексте исполнения, если
-- они в итоге приводят к одному и тому же блоку с одинаковым контекстом
-- исполнения
data BlockEq {Ψ : HeapTypes} (CC : CallCtx Ψ) : {Γ₁ Γ₂ Δ₁ Δ₂ : RegFileTypes} → Block Ψ Γ₁ Δ₁ → Block Ψ Γ₂ Δ₂ → Set where
  equal  : ∀ {Γ Δ} → {B : Block Ψ Γ Δ} → BlockEq CC B B
  left   : ∀ {Δ₁ Δ₂ Δ₃ Γ₁ Γ₂ Γ₃}
         → {A : Block Ψ Γ₁ Δ₁} → {B : Block Ψ Γ₂ Δ₂} → {C : Block Ψ Γ₃ Δ₃}
         → projr (exec-blk Ψ CC C) ≡ _ , _ , A
         → BlockEq CC A B
         → BlockEq CC C B
  right  : ∀ {Δ₁ Δ₂ Δ₃ Γ₁ Γ₂ Γ₃}
         → {A : Block Ψ Γ₁ Δ₁} → {B : Block Ψ Γ₂ Δ₂} → {C : Block Ψ Γ₃ Δ₃}
         → projr (exec-blk Ψ CC C) ≡ _ , _ , B
         → BlockEq CC A B
         → BlockEq CC A C
  ⟨_⟩_≅_ : ∀ {Δ₁ Δ₂ Δ₁' Δ₂' Γ₁ Γ₂ Γ₁' Γ₂'}
         → {CC' : CallCtx Ψ}
         → {A' : Block Ψ Γ₁' Δ₁'} {B' : Block Ψ Γ₂' Δ₂'}
         → BlockEq CC' A' B'
         → {A : Block Ψ Γ₁ Δ₁}
         → exec-blk Ψ CC A ≡ projl CC' , _ , _ , A'
         → {B : Block Ψ Γ₂ Δ₂} 
         → exec-blk Ψ CC B ≡ projl CC' , _ , _ , B'
         → BlockEq CC A B

module PLTize where

-- plt состоит всего из одной инструкции, потому что я рассчитываю на то,
-- что весь нужный код уже загружен в память, и got заполнен
plt-stub : ∀ {Γ Ψ} → (blk Γ) ✴ ∈ Ψ → Block Ψ Γ []
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

wk-∈ : ∀ {x A B} → x ∈ A → A ⊆ B → x ∈ B
wk-∈ = {!!}

wk-instr : ∀ {Ψ Ψ' Γ Δ} → Ψ ⊆ Ψ' → Instr Ψ Γ Δ → Instr Ψ' Γ Δ
wk-instr = {!!}

wk-blk : ∀ {Ψ Ψ' Γ Δ} → Ψ ⊆ Ψ' → Block Ψ Γ Δ → Block Ψ' Γ Δ
wk-blk = {!!}

pltize-code : ∀ {Ψ Γ Δ} → Block Ψ Γ Δ → Block (pltize-heap Ψ) Γ Δ
pltize-code halt = halt
pltize-code (↝ (call f)) = ↝ (call (plt f))
pltize-code (↝ (jmp[_] f)) = ↝ (jmp[ wk-∈ f pltize-⊆ ])
pltize-code (↝ (jmp f)) = ↝ (jmp (wk-∈ f pltize-⊆ ))
pltize-code (i ∙ b) = wk-instr pltize-⊆ i ∙ pltize-code b

jmp[]-proof : ∀ {Ψ Γ Δ} → {CC : CallCtx Ψ}
           → {A : Block Ψ Γ Δ}
           → (f : (blk Γ) ✴ ∈ Ψ)
           → loadblk Ψ (deref Ψ f) ≡ _ , _ , A
           → BlockEq CC A (↝ jmp[ f ])
jmp[]-proof {Ψ} {CC = CC} {A = A} f p = right (loadblk-≡ Ψ (deref Ψ f)) equal

call-proof : ∀ {Ψ Γ} → (CC : CallCtx Ψ) → {A : NewBlk Ψ}
           → (f : (blk Γ) ∈ Ψ)
           → loadblk Ψ f ≡ A
           → exec-blk Ψ CC (↝ (call f)) ≡ ((projr CC ∷ projl CC) , A)
call-proof CC f p rewrite p = refl

proof : ∀ {Γ Ψ}
      → (f : blk Γ ∈ Ψ)
      → (cc : CallCtx (pltize-heap Ψ))
      → BlockEq cc (wk-blk pltize-⊆ (↝ (call f))) (↝ (call (plt f)))
proof {Ψ = Ψ} f ctx = ⟨ (jmp[]-proof (got f) (loadblk-≡ (pltize-heap Ψ) (deref (pltize-heap Ψ) (got f)))) ⟩
    call-proof ctx (wk-∈ f pltize-⊆) (loadblk-≡ (pltize-heap Ψ) (wk-∈ f pltize-⊆)) ≅ call-proof ctx (plt f) (loadblk-≡ (pltize-heap Ψ) (plt f))
