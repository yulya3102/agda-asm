Все первичные определения остаются неизменными.

\begin{code}
module Assembler where

open import OXIj.BrutalDepTypes
open Data-List
open Data-Any

data Type : Set

RegFileTypes = List Type
HeapTypes    = List Type

data Type where
  _*  : Type → Type
  blk : RegFileTypes → Type

open Membership {A = Type} _≡_
\end{code}

Независимо от конкретных инструкций все языки ассемблера имеют общий набор
сущностей. Нижеприведенный модуль определяет эти сущности.

\begin{code}
module Meta where
\end{code}

В этой версии память больше не считается неизменной, поэтому текущее
состояние должно описывать не только регистры, но и память.

\begin{code}
  record State : Set where
    constructor state
    field
      heap : HeapTypes
      regs : RegFileTypes
  open State public
\end{code}

Далее следует определение набора изменений регистров, приведенное в предыдущей
секции.

\begin{code}
  module Diffs where
    data Chg (Γ : List Type) : Set where
      chg : ∀ {τ} → τ ∈ Γ → Type → Chg Γ

    chgapply : (Γ : List Type) → Chg Γ → List Type
    chgapply (_ ∷ Γ) (chg (here refl) σ) = σ ∷ Γ
    chgapply (τ ∷ Γ) (chg (there p)   σ) = τ ∷ chgapply Γ (chg p σ)

    data Diff (Γ : List Type) : Set where
      dempty : Diff Γ
      dchg   : (c : Chg Γ) → Diff (chgapply Γ c) → Diff Γ

    dapply : (Γ : List Type) → Diff Γ → List Type
    dapply Γ dempty = Γ
    dapply Γ (dchg c d) = dapply (chgapply Γ c) d

    dappend : ∀ {Γ} → (d : Diff Γ) → Diff (dapply Γ d) → Diff Γ
    dappend dempty d' = d'
    dappend (dchg c d) d' = dchg c (dappend d d')
\end{code}

Так как почти нигде в коде не используется применение изменений к набору
регистров отдельно от всего контекста, удобно определить функцию для
применения изменений сразу ко всему контексту.

\begin{code}
    sdapply : (S : State) → Diff (regs S) → State
    sdapply (state h r) d = state h (dapply r d)

    SDiff = λ S → Diff (regs S)
  open Diffs public
\end{code}

Теперь можно определить, что такое блок. Определение блока использует
определения различных видов инструкций. Они зависят от конкретного ассемблера,
но имеют заранее известные не зависящие от ассемблера типы, поэтому их
можно принимать как параметры.

\begin{code}
  module Blocks
    (ControlInstr : State → Set)
    (Instr : (S : State) → Diff (regs S) → Set)
    where
\end{code}

Определение блока аналогично приведенным в предыдущих секциях.

\begin{code}
    data Block (S : State) : Diff (regs S) → Set where
      halt : Block S dempty
      ↝    : ControlInstr S → Block S dempty
      _∙_  : ∀ {d d'} → Instr S d → Block (sdapply S d) d'
           → Block S (dappend d d')
\end{code}

\textbf{TODO}

\begin{code}
  module Exec-Context (Ψ : HeapTypes) where
    IPRFT = λ Γ → blk Γ ∈ Ψ
    IP = Σ RegFileTypes IPRFT
    CallStack = List IP
    CallCtx = IP × CallStack
  open Exec-Context public

  module Values
    (Block : (S : State) → Diff (regs S) → Set)
    where
    data Value (Ψ : HeapTypes) : Type → Set where
      ptr : ∀ {τ} → τ ∈ Ψ → Value Ψ (τ *)
      fun : ∀ {Γ} → {d : Diff Γ} → Block (state Ψ Γ) d → Value Ψ (blk Γ) 
  
    data IHeap (Ψ : HeapTypes) : HeapTypes → Set where
      []  : IHeap Ψ []
      _∷_ : ∀ {τ Δ} → Value Ψ τ → IHeap Ψ Δ → IHeap Ψ (τ ∷ Δ)

    lemma : {A : Set} (a : A) (as bs : List A) → as ++ a ∷ bs ≡ (as ++ [ a ]) ++ bs
    lemma a [] bs = refl
    lemma a (x ∷ as) bs rewrite lemma a as bs = refl

    iload : ∀ {Ψ τ} ψs → τ ∈ Ψ → IHeap (ψs ++ Ψ) Ψ → Value (ψs ++ Ψ) τ
    iload ψs (here refl) (x ∷ _) = x
    iload {ψ ∷ Ψ} ψs (there p) (x ∷ h)
      rewrite lemma ψ ψs Ψ = iload (ψs ++ [ ψ ]) p h

    Heap : HeapTypes → Set
    Heap Ψ = IHeap Ψ Ψ

    _++H_ : ∀ {A B} → Heap A → Heap B → Heap (A ++ B)
    as ++H bs = {!!}

    data IRegisters (Ψ : HeapTypes) : RegFileTypes → Set where
      []  : IRegisters Ψ []
      _∷_ : ∀ {τ τs} → Value Ψ τ → IRegisters Ψ τs → IRegisters Ψ (τ ∷ τs)

    Registers : State → Set
    Registers S = IRegisters (heap S) (regs S)

    load : ∀ {Ψ τ} → τ ∈ Ψ → Heap Ψ → Value Ψ τ
    load p heap = iload [] p heap

    unptr : ∀ {Ψ τ} → Value Ψ (τ *) → τ ∈ Ψ
    unptr (ptr x) = x

    unfun : ∀ {Ψ Γ} → Value Ψ (blk Γ) → Σ (Diff Γ) (Block (state Ψ Γ))
    unfun (fun x) = _ , x

    _∈B_ : ∀ {S d} → Block S d → Heap (heap S) → Set
    _∈B_ {S} b Ψ = Σ (blk (regs S) ∈ heap S) $ λ ptr → (unfun (load ptr Ψ)) ≡ _ , b

  module Eq
    (Block : (S : State) → Diff (regs S) → Set)
    (exec-blk : {S : State} {d : Diff (regs S)} {b : Block S d}
              → (Ψ : Values.Heap Block (heap S))
              → Values._∈B_ Block b Ψ
              → Values.Registers Block S → CallStack (heap S)
              → (Σ (Diff $ dapply (regs S) d) (Block $ sdapply S d))
              × (Values.Heap Block (heap $ sdapply S d)
              × (Values.Registers Block (sdapply S d)
              × CallStack (heap $ sdapply S d))))
    where
    open Values Block
    module InState (S : State) where
      SHeap = Heap (heap S)
      SCallStack = CallStack (heap S)
    open InState

    data BlockEq :
      {S₁ S₂ : State} → {d₁ : SDiff S₁} {d₂ : SDiff S₂} →
      (Ψ₁ : SHeap S₁) (Ψ₂ : SHeap S₂) →
      (Γ₁ : Registers S₁) (Γ₂ : Registers S₂) →
      (CC₁ : SCallStack S₁) (CC₂ : SCallStack S₂) →
      Block S₁ d₁ → Block S₂ d₂ → Set
      where
      equal : ∀ {S} {d : SDiff S}
            → {Ψ : SHeap S} {CC : SCallStack S} {B : Block S d} {Γ : Registers S}
            → BlockEq Ψ Ψ Γ Γ CC CC B B
      left  : ∀ {S₁ S} {d₁ : SDiff S₁} {d₂ : SDiff (sdapply S₁ d₁)} {d : SDiff S}
            → {A₁ : Block S₁ d₁} {A₂ : Block (sdapply S₁ d₁) d₂} {B : Block S d}
            → (Ψ₁ : SHeap S₁) (Ψ₂ : SHeap (sdapply S₁ d₁)) (Ψ : SHeap S)
            → (ip₁ : A₁ ∈B Ψ₁) (ip₂ : A₂ ∈B Ψ₂) (ip : B ∈B Ψ)
            → (Γ₁ : Registers S₁) (Γ₂ : Registers (sdapply S₁ d₁)) (Γ : Registers S)
            → (CC₁ : SCallStack S₁) (CC₂ : SCallStack (sdapply S₁ d₁)) (CC : SCallStack S)
            → exec-blk Ψ₁ ip₁ Γ₁ CC₁ ≡ (_ , A₂) , Ψ₂ , Γ₂ , CC₂
            → BlockEq Ψ₁ Ψ Γ₁ Γ CC₁ CC A₁ B
            → BlockEq Ψ₂ Ψ Γ₂ Γ CC₂ CC A₂ B
      right : ∀ {S₁ S} {d₁ : SDiff S₁} {d₂ : SDiff (sdapply S₁ d₁)} {d : SDiff S}
            → {A₁ : Block S₁ d₁} {A₂ : Block (sdapply S₁ d₁) d₂} {B : Block S d}
            → (Ψ₁ : SHeap S₁) (Ψ₂ : SHeap (sdapply S₁ d₁)) (Ψ : SHeap S)
            → (ip₁ : A₁ ∈B Ψ₁) (ip₂ : A₂ ∈B Ψ₂) (ip : B ∈B Ψ)
            → (Γ₁ : Registers S₁) (Γ₂ : Registers (sdapply S₁ d₁)) (Γ : Registers S)
            → (CC₁ : SCallStack S₁) (CC₂ : SCallStack (sdapply S₁ d₁)) (CC : SCallStack S)
            → exec-blk Ψ₁ ip₁ Γ₁ CC₁ ≡ (_ , A₂) , Ψ₂ , Γ₂ , CC₂
            → BlockEq Ψ Ψ₁ Γ Γ₁ CC CC₁ B A₁
            → BlockEq Ψ Ψ₂ Γ Γ₂ CC CC₂ B A₂

  module Exec
    (ControlInstr : State → Set)
    (Instr : (S : State) → SDiff S → Set)
    (exec-instr : {S : State}
                → {d : SDiff S} → Instr S d
                → Values.Heap (Blocks.Block ControlInstr Instr) (heap S)
                → Values.Registers (Blocks.Block ControlInstr Instr) S
                → Values.Heap (Blocks.Block ControlInstr Instr) (heap $ sdapply S d)
                × Values.Registers (Blocks.Block ControlInstr Instr) (sdapply S d))
    (exec-control : {S : State}
                  → ControlInstr S
                  → Values.Heap (Blocks.Block ControlInstr Instr) (heap S)
                  → CallStack (heap S) → IP (heap S)
                  → CallStack (heap S) × IPRFT (heap S) (regs S))
    where
    open Blocks ControlInstr Instr public
    open Values Block public

    dapply-lemma : ∀ {Γ} d d'
           → dapply Γ (dappend d d') ≡ dapply (dapply Γ d) d'
    dapply-lemma d d' = {!!}

    exec-blk : {S : State} {d : Diff (regs S)} {b : Block S d}
             → (Ψ : Heap (heap S))
             → b ∈B Ψ
             → Registers S → CallStack (heap S)
             → (Σ (Diff $ dapply (regs S) d) (Block $ sdapply S d))
             × (Heap (heap $ sdapply S d)
             × (Registers (sdapply S d)
             × CallStack (heap $ sdapply S d)))
    exec-blk {b = b} Ψ p Γ cs = exec-blk-next-ip b {!!} Ψ Γ cs
      where
      find-next-block : ∀ {Ψ} → IP Ψ → IP Ψ
      find-next-block = {!!}
      exec-blk-next-ip : {S : State} {d : Diff (regs S)} → Block S d → IP (heap S)
                       → Heap (heap S) → Registers S → CallStack (heap S)
                       → (Σ (Diff $ dapply (regs S) d) (Block $ sdapply S d))
                       × (Heap (heap $ sdapply S d)
                       × (Registers (sdapply S d)
                       × CallStack (heap $ sdapply S d)))
      exec-blk-next-ip Blocks.halt ip Ψ Γ cs = (_ , halt) , (Ψ , Γ , cs)
      exec-blk-next-ip {S} (Blocks.↝ i) ip Ψ Γ cs = next-block , Ψ , Γ , next-cs
        where
        next-state : CallStack (heap S) × IPRFT (heap S) (regs S)
        next-state = exec-control i Ψ cs ip
        next-cs : CallStack (heap S)
        next-cs = projl next-state
        next-ip : blk (regs S) ∈ (heap S)
        next-ip = projr next-state
        next-block : Σ (Diff (regs S)) (Block S)
        next-block = unfun $ load next-ip Ψ
      exec-blk-next-ip {S} (Blocks._∙_ {d} {d'} i b) ip Ψ Γ cs
        rewrite dapply-lemma d d' = exec-blk-next-ip b ip next-heap next-regs cs
        where
        next-state : Heap (heap $ sdapply S d) × Registers (sdapply S d)
        next-state = exec-instr i Ψ Γ
        next-heap = projl next-state
        next-regs = projr next-state

    open Eq Block exec-blk public
open Meta
\end{code}
\begin{code}

module x86-64 where
  data ControlInstr (S : State) : Set where
    jmp call : blk (regs S) ∈ heap S → ControlInstr S
    jmp[_]   : blk (regs S) * ∈ heap S → ControlInstr S
    -- :(
    -- ret      : ? → ControlInstr S

  data Instr (S : State) : SDiff S → Set where
    mov_,_ : ∀ {τ σ} → (r : σ ∈ regs S) → Values.Value (Blocks.Block ControlInstr Instr) (heap S) τ → Instr S (dchg (chg r τ) dempty)

  exec-instr : {S : State}
             → {d : SDiff S} → Instr S d
             → Values.Heap (Blocks.Block ControlInstr Instr) (heap S)
             → Values.Registers (Blocks.Block ControlInstr Instr) S
             → Values.Heap (Blocks.Block ControlInstr Instr) (heap $ sdapply S d)
             × Values.Registers (Blocks.Block ControlInstr Instr) (sdapply S d)
  
  exec-control : {S : State}
               → ControlInstr S
               → Values.Heap (Blocks.Block ControlInstr Instr) (heap S)
               → CallStack (heap S) → IP (heap S)
               → CallStack (heap S) × IPRFT (heap S) (regs S)

  exec-instr = {!!}

  exec-control {state heap regs} (jmp x) Ψ cs ip = cs , x
  exec-control {state heap regs} (call x) Ψ cs ip = ip ∷ cs , x
  exec-control {state heap regs} (jmp[ x ]) Ψ cs ip = cs , (Values.unptr (Blocks.Block ControlInstr Instr) $ Values.load (Blocks.Block ControlInstr Instr) x Ψ)

  open Exec ControlInstr Instr exec-instr exec-control

  module Binary where
    record Binary : Set where
      constructor bin
      field
        Ψ         : HeapTypes
        memory    : Heap Ψ

    EntryPoint : HeapTypes → Set
    EntryPoint Ψ = Σ RegFileTypes $ λ Γ → (Registers (state Ψ Γ) × (blk Γ ∈ Ψ))

    record Program : Set where
      constructor exec
      field
        binary    : Binary
        start     : EntryPoint (Binary.Ψ binary)

    static : Binary → Binary → Binary
    static a b = bin (Binary.Ψ a ++ Binary.Ψ b) (Binary.memory a ++H Binary.memory b)

    infixr 7 _∷,_ _∷
    infixr 5 _∙ _∙~_

    _∷,_ : ∀ {S d d'} → Instr S d → Block (sdapply S d) d' → Block S (dappend d d')
    _∷,_ = _∙_

    _∷ : ∀ {S} → ControlInstr S → Block S dempty
    _∷ = ↝

    data Code (S : State) : Set where
      _∙  : ∀ {d} → Block S d → Code S
      _∙~_ : ∀ {d} → Block S d → Code (sdapply S d) → Code S

    plt-stub : ∀ {S τ} → (rax : τ ∈ regs S) → (linker : blk {!!} ∈ heap S) → (got : ((blk $ regs S) *) ∈ heap S) → (id : Value (heap S) {!!}) → Code S
    plt-stub rax linker got id =
        jmp[ got ] ∷ ∙~

        mov rax , id ∷,
        call linker ∷ ∙~
        
        {!jmp[ got ] ∷ ∙!}

\end{code}
