\ignore{
\begin{code}
module Asm where

open import Data.Maybe
open import Data.Product
open import Data.List
open import Data.List.Any
open Membership-≡
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Function

open import Core public
open import MetaAsm public

open Meta public
open import Diffs public

data ControlInstr (S : StateType) : Maybe (CallStackChg S) → Set
data Instr (S : StateType) : SmallChg S → Set

open Blocks ControlInstr Instr public
open Values Block public

data ControlInstr (S : StateType) where
  call : ∀ {Γ DS}
       → (f : code
         (StateType.registers S)
         (StateType.datastack S)
         ((Γ , DS) ∷ StateType.callstack S)
         ∈ StateType.memory S)
       → (cont : code Γ DS (StateType.callstack S)
               ∈ StateType.memory S)
       → ControlInstr S (Maybe.just $ StackDiff.push (Γ , DS))
  jmp[_] : (ptr : atom
         (code
         (StateType.registers S)
         (StateType.datastack S)
         (StateType.callstack S) *)
         ∈ StateType.memory S)
       → ControlInstr S nothing
  jmp : (f : code
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
  mov   : ∀ {σ τ}
        → (r : σ ∈ StateType.registers S)
        → RegValue (StateType.memory S) τ
        → Instr S (onlyreg (RegDiff.chg r τ))
  push  : ∀ {τ}
        → τ ∈ StateType.registers S
        → Instr S (onlystack (StackDiff.push τ))
  pushc : ∀ {τ} → RegValue (StateType.memory S) τ
        → Instr S (onlystack (StackDiff.push τ))
        -- TODO: still possible to push values from registers using pushc
  pop   : ∀ {σ τ DS}
        → (r : σ ∈ StateType.registers S)
        → (p : StateType.datastack S ≡ τ ∷ DS)
        → Instr S (regstack (RegDiff.chg r τ) (StackDiff.pop p))

control-instr-semantics : ∀ {S c}
             → State S
             → ControlInstr S c
             → CallStack
               (StateType.memory S)
               (StateType.callstack (dapply S (csChg S c)))
             × Σ (Diff (dapply S (csChg S c)))
                 (Block (dapply S (csChg S c)))
control-instr-semantics (state Γ Ψ DS CS) (call f cont)
  = cont ∷ CS , loadblock Ψ f
control-instr-semantics (state Γ Ψ DS CS) (jmp f)
  = CS , loadblock Ψ f
control-instr-semantics (state Γ Ψ DS (f ∷ CS)) (ret refl)
  = CS , loadblock Ψ f
\end{code}
}

Для описания семантики динамической линковки необходима семантика только
инструкции непрямого перехода \C{jmp[\_]}. Потому описание семантики других
инструкций мы не рассматриваем.
\iftoggle{russian-draft}{
Для этой инструкции семантика определена следующим образом:
}{
TODO

The important part of dynamic linking is branch instructions and its
semantics, in particular, indirect jump instruction \C{jmp[\_]}. Its
semantics is defined like this:
}

\begin{code}
control-instr-semantics S (jmp[ p ])
  = State.callstack S
  , loadblock (State.memory S)
    (loadptr (State.memory S) p)
\end{code}

\iftoggle{russian-draft}{
В состоянии исполнителя \AgdaBound{S} исполнение инструкции непрямого
перехода по указателю \AgdaBound{p} оставит стек вызовов прежним,
\F{State.callstack} \AgdaBound{S}, а исполнение перейдет на
последовательность инструкций, загруженную из памяти \F{State.memory}
\AgdaBound{S} по указателю, загруженному из ячейки \AgdaBound{p}.
}{
Execution of indirect jump to the pointer \AgdaBound{p} in machine state
\AgdaBound{S} does not change call stack \F{State.callstack} \AgdaBound{S},
and execution will be continued from instruction sequence loaded from
\F{State.memory} \AgdaBound{S} by pointer loaded from memory by
\AgdaBound{p}.
}

\ignore{
\begin{code}
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
exec-instr (state Γ Ψ DS CS) (pushc i)
  = Γ , Ψ , i ∷ DS
exec-instr (state Γ Ψ (v ∷ DS) CS) (pop r refl)
  = toreg Γ r v , Ψ , DS

open ExecBlk Instr ControlInstr exec-instr control-instr-semantics public
open import BlockEq Block exec-block public
\end{code}
}
