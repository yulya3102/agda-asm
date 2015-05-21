module Functions where

open import OXIj.BrutalDepTypes
open Data-List
open Data-Any

data RegType : Set
data Type : Set

RegTypes      = List RegType
DataType      = List Type
DataStackType = List RegType
CallStackType = List (RegTypes × DataStackType)

record StateType : Set where
  constructor statetype
  field
    registers : RegTypes
    memory    : DataType
    datastack : DataStackType
    callstack : CallStackType

data RegType where
  _✴  : Type → RegType
  int : RegType

data Type where
  atom : RegType → Type
  func : RegTypes → DataStackType → CallStackType → Type

open Membership {A = Type} _≡_
_∈R_ = Membership._∈_ {A = RegType} _≡_

-- надо перестать страдать фигнёй и переехать на agda-stdlib
data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A

module Meta where
  module Diffs where
    module RegDiff where
      data Chg (Γ : RegTypes) : Set where
        chg : ∀ {τ} → τ ∈R Γ → RegType → Chg Γ
  
      chgapply : (Γ : RegTypes) → Chg Γ → RegTypes
      chgapply (_ ∷ Γ) (chg (here refl) σ) = σ ∷ Γ
      chgapply (τ ∷ Γ) (chg (there p)   σ) = τ ∷ chgapply Γ (chg p σ)
  
      data Diff (Γ : RegTypes) : Set where
        dempty : Diff Γ
        dchg   : (c : Chg Γ) → Diff (chgapply Γ c) → Diff Γ

      dc : ∀ {Γ} → Chg Γ → Diff Γ
      dc c = dchg c dempty
  
      dapply : (Γ : RegTypes) → Diff Γ → RegTypes
      dapply Γ dempty = Γ
      dapply Γ (dchg c d) = dapply (chgapply Γ c) d
  
      dappend : ∀ {Γ} → (d : Diff Γ) → Diff (dapply Γ d) → Diff Γ
      dappend dempty d' = d'
      dappend (dchg c d) d' = dchg c (dappend d d')

      dappend-dempty-lemma : ∀ {Γ} → (d : Diff Γ) → dappend d dempty ≡ d
      dappend-dempty-lemma dempty = refl
      dappend-dempty-lemma (dchg c d) rewrite dappend-dempty-lemma d = refl

      dappend-dapply-lemma : ∀ S → (d₁ : Diff S) → (d₂ : Diff (dapply S d₁))
                           → dapply S (dappend d₁ d₂) ≡ dapply (dapply S d₁) d₂
      dappend-dapply-lemma S dempty d₂ = refl
      dappend-dapply-lemma S (dchg c d₁) d₂
        = dappend-dapply-lemma (chgapply S c) d₁ d₂

    module StackDiff (A : Set) where
      data Chg (S : List A) : Set where
        push : (i : A) → Chg S
        pop  : ∀ {Γ S'} → S ≡ Γ ∷ S' → Chg S

      chgapply : (S : List A) → Chg S → List A
      chgapply cs (push x) = x ∷ cs
      chgapply (._ ∷ S') (pop refl) = S'

      data Diff (S : List A) : Set where
        dempty : Diff S
        dchg   : (c : Chg S) → Diff (chgapply S c) → Diff S

      dc : ∀ {S} → Chg S → Diff S
      dc c = dchg c dempty

      dmaybe : ∀ {S} → Maybe (Chg S) → Diff S
      dmaybe (just x) = dc x
      dmaybe nothing = dempty
  
      dapply : (S : List A) → Diff S → List A
      dapply S dempty = S
      dapply S (dchg c d) = dapply (chgapply S c) d

      dappend : ∀ {S} → (d : Diff S) → Diff (dapply S d) → Diff S
      dappend dempty d' = d'
      dappend (dchg c d) d' = dchg c (dappend d d')

      dappend-dapply-lemma : ∀ S → (d₁ : Diff S) → (d₂ : Diff (dapply S d₁))
                           → dapply S (dappend d₁ d₂) ≡ dapply (dapply S d₁) d₂
      dappend-dapply-lemma S dempty d₂ = refl
      dappend-dapply-lemma S (dchg c d₁) d₂
        = dappend-dapply-lemma (chgapply S c) d₁ d₂

    record Diff (S : StateType) : Set where
      constructor diff
      field
        rdiff  : RegDiff.Diff (StateType.registers S)
        dsdiff : StackDiff.Diff RegType (StateType.datastack S)
        csdiff : StackDiff.Diff (RegTypes × DataStackType) (StateType.callstack S)
    open Diff public

    dempty : ∀ {S} → Diff S
    dempty = diff (RegDiff.dempty) (StackDiff.dempty) StackDiff.dempty

    dapply : (S : StateType) → Diff S → StateType
    dapply (statetype r m d c) (diff rd dd cd) =
        statetype
        (RegDiff.dapply r rd)
        m
        (StackDiff.dapply RegType d dd)
        (StackDiff.dapply (RegTypes × DataStackType) c cd)

    dappend : ∀ {S} → (d : Diff S) → Diff (dapply S d) → Diff S
    dappend (diff rd dd cd) (diff rd' dd' cd') =
        diff
        (RegDiff.dappend rd rd')
        (StackDiff.dappend RegType dd dd')
        (StackDiff.dappend (RegTypes × DataStackType) cd cd')

    DataStackChg : StateType → Set
    DataStackChg S = StackDiff.Chg (RegType) (StateType.datastack S)

    CallStackChg : StateType → Set
    CallStackChg S = StackDiff.Chg (RegTypes × DataStackType) (StateType.callstack S)

    RegChg : StateType → Set
    RegChg S = RegDiff.Chg (StateType.registers S)

    data SmallChg (S : StateType) : Set where
      onlyreg   : RegChg S → SmallChg S
      onlystack : DataStackChg S → SmallChg S
      regstack  : RegChg S → DataStackChg S → SmallChg S

    regChg : ∀ {S} → RegChg S → Diff S
    regChg c =
        diff
        (RegDiff.dchg c RegDiff.dempty)
        StackDiff.dempty
        StackDiff.dempty

    dsChg : ∀ {S} → DataStackChg S → Diff S
    dsChg c =
      diff
      RegDiff.dempty
      (StackDiff.dchg c StackDiff.dempty)
      StackDiff.dempty

    sChg : ∀ {S} → SmallChg S → Diff S
    sChg (onlyreg r) = regChg r
    sChg (onlystack d) = dsChg d
    sChg (regstack r d) =
      diff
      (RegDiff.dchg r RegDiff.dempty)
      (StackDiff.dchg d StackDiff.dempty)
      StackDiff.dempty

    csChg : ∀ S → Maybe (CallStackChg S) → Diff S
    csChg S nothing = dempty
    csChg S (just c) =
        diff
        RegDiff.dempty
        StackDiff.dempty
        (StackDiff.dchg c StackDiff.dempty)
  open Diffs

  module Blocks
    -- вообще-то, стек может и не меняться (например, при jump)
    (ControlInstr : (S : StateType) → Maybe (CallStackChg S) → Set)
    (Instr : (S : StateType) → SmallChg S → Set)
    where
    data Block (S : StateType) : Diff S → Set where
      _∙ : ∀ {c} → ControlInstr S c → Block S (csChg S c)
      _∙~_ : ∀ {c d} → Instr S c → Block (dapply S (sChg c)) d → Block S (dappend (sChg c) d)

  module Values
    (Block : (S : StateType) → Diff S → Set)
    where
    data RegValue (Ψ : DataType) : RegType → Set where
      ptr : ∀ {τ} → τ ∈ Ψ → RegValue Ψ (τ ✴)
      int : ℕ → RegValue Ψ int

    data Value (Ψ : DataType) : Type → Set where
      atom : ∀ {τ} → RegValue Ψ τ → Value Ψ (atom τ)
      func : ∀ {Γ DS CS d} → Block (statetype Γ Ψ DS CS) d → Value Ψ (func Γ DS CS)

    unfunc : ∀ {Ψ Γ DS CS} → Value Ψ (func Γ DS CS)
           → (Σ (Diff (statetype Γ Ψ DS CS)) (Block (statetype Γ Ψ DS CS)))
    unfunc (func b) = _ , b

    unptr : ∀ {Ψ τ} → Value Ψ (atom (τ ✴)) → τ ∈ Ψ
    unptr (atom (ptr x)) = x
      
    data Registers (Ψ : DataType) : RegTypes → Set where
      []  : Registers Ψ []
      _∷_ : ∀ {τ τs} → RegValue Ψ τ → Registers Ψ τs → Registers Ψ (τ ∷ τs)

    fromreg : ∀ {Ψ Γ τ} → Registers Ψ Γ → τ ∈R Γ → RegValue Ψ τ
    fromreg (x ∷ Γ) (here refl) = x
    fromreg (x ∷ Γ) (there p) = fromreg Γ p

    toreg : ∀ {Ψ Γ σ τ} → Registers Ψ Γ → (r : σ ∈R Γ) → RegValue Ψ τ → Registers Ψ (RegDiff.chgapply Γ (RegDiff.chg r τ))
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

    loadfunc : ∀ {Ψ Γ CS DS} → Data Ψ → func Γ DS CS ∈ Ψ
             → Σ (Diff (statetype Γ Ψ DS CS)) (Block (statetype Γ Ψ DS CS))
    loadfunc Ψ f = unfunc $ load Ψ f

    loadptr : ∀ {Ψ τ} → Data Ψ → atom (τ ✴) ∈ Ψ → τ ∈ Ψ
    loadptr Ψ p = unptr $ load Ψ p

    data Stack {I : Set} {A : I → Set} (Ψ : DataType) : List I → Set where
      []   : Stack Ψ []
      _∷_  : ∀ {τ S} → A τ → Stack {A = A} Ψ S → Stack Ψ (τ ∷ S)

    IPRT : DataType → RegTypes → DataStackType → CallStackType → Set
    IPRT Ψ Γ DS CS = func Γ DS CS ∈ Ψ

    DataStack = λ Ψ → Stack {A = RegValue Ψ} Ψ

    data CallStack (Ψ : DataType) : CallStackType → Set where
      []  : CallStack Ψ []
      _∷_ : ∀ {Γ DS CS} → IPRT Ψ Γ DS CS → CallStack Ψ CS
          → CallStack Ψ ((Γ , DS) ∷ CS)

    record State (S : StateType) : Set where
      constructor state
      field
        registers : Registers (StateType.memory S) (StateType.registers S)
        memory    : Data (StateType.memory S)
        datastack : DataStack (StateType.memory S) (StateType.datastack S)
        callstack : CallStack (StateType.memory S) (StateType.callstack S)

  module Eq
    (Block : (S : StateType) → Diff S → Set)
    (exec-block : ∀ {ST d} → Values.State Block ST → Block ST d
                → Values.State Block (dapply ST d)
                × Σ (Diff (dapply ST d)) (Block (dapply ST d)))
    where
    open Values Block

    data BlockEq (Ψ : DataType)
      : {ST₁ ST₂ : StateType}
      → {d₁ : Diff ST₁} {d₂ : Diff ST₂}
      → (S₁ : State ST₁) (S₂ : State ST₂)
      → Block ST₁ d₁ → Block ST₂ d₂
      → Set
      where
      equal : ∀ {ST} → {S : State ST} {d : Diff ST} {A : Block ST d}
            → BlockEq Ψ S S A A
      left  : ∀ {ST₁ ST}
            → {d₁ : Diff ST₁} {d₂ : Diff (dapply ST₁ d₁)} {d : Diff ST}
            → {S₁ : State ST₁} {S₂ : State (dapply ST₁ d₁)} {S : State ST}
            → {A₁ : Block ST₁ d₁} {A₂ : Block (dapply ST₁ d₁) d₂} {B : Block ST d}
            → exec-block S₁ A₁ ≡ S₂ , d₂ , A₂
            → BlockEq Ψ S₂ S A₂ B
            → BlockEq Ψ S₁ S A₁ B
      right : ∀ {ST₁ ST}
            → {d₁ : Diff ST₁} {d₂ : Diff (dapply ST₁ d₁)} {d : Diff ST}
            → {S₁ : State ST₁} {S₂ : State (dapply ST₁ d₁)} {S : State ST}
            → {A₁ : Block ST₁ d₁} {A₂ : Block (dapply ST₁ d₁) d₂} {B : Block ST d}
            → exec-block S₁ A₁ ≡ S₂ , d₂ , A₂
            → BlockEq Ψ S S₂ B A₂
            → BlockEq Ψ S S₁ B A₁

module 2Meta
  (ControlInstr : (S : StateType) → Maybe (Meta.Diffs.CallStackChg S) → Set)
  (Instr : (S : StateType) → Meta.Diffs.SmallChg S → Set)
  (exec-control : ∀ {S c}
               → Meta.Values.State (Meta.Blocks.Block ControlInstr Instr) S
               → ControlInstr S c
               → Meta.Values.CallStack
                (Meta.Blocks.Block ControlInstr Instr)
                (StateType.memory S)
                (StateType.callstack (Meta.Diffs.dapply S (Meta.Diffs.csChg S c)))
               × Σ (Meta.Diffs.Diff (Meta.Diffs.dapply S (Meta.Diffs.csChg S c)))
                   (Meta.Blocks.Block ControlInstr Instr
                     (Meta.Diffs.dapply S (Meta.Diffs.csChg S c))))
  (exec-instr : ∀ {S c}
              → Meta.Values.State (Meta.Blocks.Block ControlInstr Instr) S
              → Instr S c
              → Meta.Values.Registers
               (Meta.Blocks.Block ControlInstr Instr)
               (StateType.memory S)
               (StateType.registers (Meta.Diffs.dapply S (Meta.Diffs.sChg c)))
              × (Meta.Values.Data
                (Meta.Blocks.Block ControlInstr Instr) (StateType.memory S)
              × Meta.Values.DataStack
               (Meta.Blocks.Block ControlInstr Instr)
               (StateType.memory S)
               (StateType.datastack (Meta.Diffs.dapply S (Meta.Diffs.sChg c)))))
  where
  open Meta
  open Diffs
  open Blocks ControlInstr Instr
  open Values Block

  -- вот эти леммы куда-нибудь подвинуть надо бы
  reg-const : ∀ S → (c : Maybe (CallStackChg S)) → rdiff (csChg S c) ≡ RegDiff.dempty
  reg-const S (just c) = refl
  reg-const S nothing = refl

  ds-const : ∀ S → (c : Maybe (CallStackChg S)) → dsdiff (csChg S c) ≡ StackDiff.dempty
  ds-const S (just x) = refl
  ds-const S nothing = refl

  cs-lemma : ∀ S → (c : SmallChg S) → csdiff (sChg c) ≡ StackDiff.dempty
  cs-lemma S (onlyreg x) = refl
  cs-lemma S (onlystack x) = refl
  cs-lemma S (regstack x x₁) = refl

  dapply-csChg : ∀ S → (c : Maybe (CallStackChg S))
               → dapply S (csChg S c) ≡ statetype (StateType.registers S) (StateType.memory S) (StateType.datastack S)
                (StackDiff.dapply (RegTypes × DataStackType) (StateType.callstack S) (csdiff (csChg S c)))
  dapply-csChg S (just x) = refl
  dapply-csChg S nothing = refl

  open ≡-Prop

  exec-block : ∀ {ST d} → State ST → Block ST d
             → State (dapply ST d)
             × Σ (Diff (dapply ST d)) (Block (dapply ST d))
  exec-block {S} (state Γ Ψ DS CS) (Blocks._∙ {c} ci)
    rewrite reg-const S c | ds-const S c
    = (state Γ Ψ DS CS') , blk
    where
    ecr = exec-control (state Γ Ψ DS CS) ci
    CS' = projl ecr
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
    blk rewrite sym (dapply-csChg S c) = projr ecr
  exec-block {S} (state Γ Ψ DS CS) (Blocks._∙~_ {c} {d} i b)
    rewrite cs-lemma S c
          | RegDiff.dappend-dapply-lemma (StateType.registers S) (rdiff (sChg c)) (rdiff d)
          | StackDiff.dappend-dapply-lemma RegType (StateType.datastack S) (dsdiff (sChg c)) (dsdiff d)
          = exec-block (state Γ' Ψ' DS' CS) b
    where
    eir = exec-instr (state Γ Ψ DS CS) i
    Γ'  = projl eir
    Ψ'  = projl (projr eir)
    DS' = projr (projr eir)

  open Eq Block exec-block public

module AMD64 where
  open Meta
  open Diffs

  data ControlInstr (S : StateType) : Maybe (CallStackChg S) → Set
  data Instr (S : StateType) : SmallChg S → Set

  open Blocks ControlInstr Instr
  open Values Block
  
  data ControlInstr (S : StateType) where
    -- везде, где требуется сакральное знание о том, что расположено в памяти
    -- за этой инструкцией, я принимаю дополнительный аргумент
    -- это сделано для упрощения себе жизни
    -- в реальный ассемблер это отобразится одним лишним jump
    call : ∀ {Γ DS}
         → (f : func
           (StateType.registers S)
           (StateType.datastack S)
           ((Γ , DS) ∷ StateType.callstack S)
           ∈ StateType.memory S)
         -- по-хорошему, ниже должно быть не memory S, а что-то другое
         -- но мне плевать, потому что память неизменна
         → (cont : func Γ DS (StateType.callstack S) ∈ StateType.memory S)
         → ControlInstr S (just $ StackDiff.push (Γ , DS))
         -- вот тут atom выглядит как говно :(
    ijmp : (ptr : atom
           (func
           (StateType.registers S)
           (StateType.datastack S)
           (StateType.callstack S) ✴)
           ∈ StateType.memory S)
         → ControlInstr S nothing
    jump : (f : func
           (StateType.registers S)
           (StateType.datastack S)
           (StateType.callstack S)
           ∈ StateType.memory S)
         → ControlInstr S nothing
         -- мне сильно не нравится аргумент ret
    ret  : ∀ {CS}
         → (p : StateType.callstack S ≡ (StateType.registers S , StateType.datastack S) ∷ CS)
         → ControlInstr S (just (StackDiff.pop p))

  data Instr (S : StateType) where
    mov  : ∀ {σ τ}
         → (r : σ ∈R StateType.registers S)
         → RegValue (StateType.memory S) τ
         → Instr S (onlyreg (RegDiff.chg r τ))
    push : ∀ {τ}
         → τ ∈R StateType.registers S
         → Instr S (onlystack (StackDiff.push τ))
    -- pop меняет одновременно и стек, и регистры
    -- тут было три варианта:
    -- * засунуть в тип дифф, а не чендж
    -- * разбить эту инструкцию на мув и поп
    -- * сделать, как сделано
    -- в первом случае можно будет пилить ЖИРНЫЕ инструкции, и это говно
    -- во втором надо будет делать огромную кучу разных видов мувов
    -- третий наименьшее зло, хотя непонятно, пригодится ли это ещё где-то
    pop  : ∀ {σ τ DS}
         → (r : σ ∈R StateType.registers S)
         -- этот аргумент мне сильно не нравится
         → (p : StateType.datastack S ≡ τ ∷ DS)
         → Instr S (regstack (RegDiff.chg r τ) (StackDiff.pop p))

  exec-control : ∀ {S c}
               → State S
               → ControlInstr S c
               → CallStack (StateType.memory S)
                           (StateType.callstack (dapply S (csChg S c)))
               × Σ (Diff (dapply S (csChg S c))) (Block (dapply S (csChg S c)))
  exec-control (state Γ Ψ DS CS) (call f cont) = cont ∷ CS , loadfunc Ψ f
  exec-control (state Γ Ψ DS CS) (ijmp p) = CS , loadfunc Ψ (loadptr Ψ p)
  exec-control (state Γ Ψ DS CS) (jump f) = CS , loadfunc Ψ f
  exec-control (state Γ Ψ DS (f ∷ CS)) (ret refl) = CS , loadfunc Ψ f

  exec-instr : ∀ {S c}
             → State S
             → Instr S c
             → Registers (StateType.memory S)
                         (StateType.registers (dapply S (sChg c)))
             × (Data (StateType.memory S)
             × DataStack (StateType.memory S)
                         (StateType.datastack (dapply S (sChg c))))
  exec-instr (state Γ Ψ DS CS) (mov r x) = toreg Γ r x , Ψ , DS
  exec-instr (state Γ Ψ DS CS) (push r) = Γ , Ψ , fromreg Γ r ∷ DS
  exec-instr (state Γ Ψ (v ∷ DS) CS) (pop r refl) = toreg Γ r v , Ψ , DS
  
  open 2Meta ControlInstr Instr exec-control exec-instr

  module Linkers where
    pltize : DataType → DataType
    pltize [] = []
    pltize (atom x ∷ Ψ) = atom x ∷ pltize Ψ
    pltize (func Γ DS CS ∷ Ψ)
      -- первое — plt, второе — got, третье — сама функция
      = func Γ DS CS ∷ (atom (func Γ DS CS ✴) ∷ (func Γ DS CS ∷ pltize Ψ))

    -- вообще-то тут результатом является не функция в измененном хипе,
    -- а plt-шный блок, соответствующий функции из старого хипа
    -- но у функции и plt-шного блока одинаковые типы (что логично),
    -- потому эта сигнатура выглядит как говно :(
    plt : ∀ {Γ Ψ DS CS} → func Γ DS CS ∈ Ψ → func Γ DS CS ∈ pltize Ψ
    plt (here refl) = here refl
    plt {Ψ = atom x ∷ Ψ} (there f) = there $ plt f
    plt {Ψ = func Γ DS CS ∷ Ψ} (there f) = there (there (there (plt f)))

    got : ∀ {Γ Ψ DS CS} → func Γ DS CS ∈ Ψ → atom (func Γ DS CS ✴) ∈ pltize Ψ
    got (here refl) = there (here refl)
    got {Ψ = atom x ∷ Ψ} (there f) = there $ got f
    got {Ψ = func Γ DS CS ∷ Ψ} (there f) = there (there (there (got f)))

    -- вот эту часть, по-хорошему, надо заимплементить по-другому
    -- ибо по-любому где-нибудь вылезет необходимость доказать, что Ψ ⊆ pltize Ψ
    -- и эта функция является следствием из этого факта
    blk : ∀ {Γ Ψ DS CS} → func Γ DS CS ∈ Ψ → func Γ DS CS ∈ pltize Ψ
    blk (here refl) = there (there (here refl))
    blk {Ψ = atom x ∷ Ψ} (there f) = there $ blk f
    blk {Ψ = func Γ DS CS ∷ Ψ} (there f) = there (there (there (blk f)))

    plt-stub : ∀ {Γ Ψ DS CS} → atom (func Γ DS CS ✴) ∈ Ψ
             -- внимание на дифф!
             → Block (statetype Γ Ψ DS CS) dempty
    plt-stub got = ijmp got ∙

    exec-ijmp : ∀ {ST} → (S : State ST)
              → (p : atom (func
                   (StateType.registers ST)
                   (StateType.datastack ST)
                   (StateType.callstack ST)
                 ✴) ∈ StateType.memory ST)
              → exec-block S (ijmp p ∙)
              ≡ S , loadfunc (State.memory S) (loadptr (State.memory S) p)
    exec-ijmp S p = refl

    open ≡-Prop

    exec-plt : ∀ {Γ Ψ DS CS}
             → (f : func Γ DS CS ∈ Ψ)
             → (S : State (statetype Γ (pltize Ψ) DS CS))
             → loadptr (State.memory S) (got f) ≡ blk f
             → exec-block S (plt-stub (got f))
             ≡ S , loadfunc (State.memory S) (blk f)
    exec-plt f S p rewrite sym p = exec-ijmp S (got f)

    proof : ∀ {Γ Ψ DS CS}
          → (f : func Γ DS CS ∈ Ψ)
          → (S : State (statetype Γ (pltize Ψ) DS CS))
          -- если GOT заполнен корректно, то
          → loadptr (State.memory S) (got f) ≡ blk f
          -- в любом стейте S эквивалентны
          → BlockEq Ψ S S
          -- PLTшный стаб, дергающий нужный GOT
            (plt-stub (got f))
          -- и сама функция
            (projr $ loadfunc (State.memory S) (blk f))
    proof f S p = left (exec-plt f S p) equal
