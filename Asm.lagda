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

open import MetaAsm public

open Meta public
open Diffs public
\end{code}

Using framework described above, we can define subset of assembly language
large enough to formalise dynamic linking ABI. This assembly language looks
almost like x86-84 assembly language that makes it suitable for reasoning
about linkers. This language differs from actual x86-64 assembly language
in instructions that involve control flow and concept of basic blocks.

TODO

\begin{code}
data ControlInstr (S : StateType) : Maybe (CallStackChg S) → Set
data Instr (S : StateType) : SmallChg S → Set

open Blocks ControlInstr Instr public
open Values Block public
\end{code}
}

Используемая в динамической линковке инструкция `indirect jump` принимает
аргументом адрес ячейки памяти, в которой лежит указатель на тот блок кода,
управление на который хочется передать. `nothing` в типе результируюшего
ControlInstr указывает на то, что эта инструкция никак не меняет стек
вызовов.

\begin{code}
data ControlInstr (S : StateType) where
\end{code}

\ignore{
\begin{code}
  call : ∀ {Γ DS}
       → (f : block
         (StateType.registers S)
         (StateType.datastack S)
         ((Γ , DS) ∷ StateType.callstack S)
         ∈ StateType.memory S)
       → (cont : block Γ DS (StateType.callstack S)
               ∈ StateType.memory S)
       → ControlInstr S (Maybe.just $ StackDiff.push (Γ , DS))
\end{code}
}

\begin{code}
  jmp[_] : (ptr : atom
         (block
         (StateType.registers S)
         (StateType.datastack S)
         (StateType.callstack S) *)
         ∈ StateType.memory S)
       → ControlInstr S nothing
\end{code}

\ignore{
\begin{code}
  jmp : (f : block
        (StateType.registers S)
        (StateType.datastack S)
        (StateType.callstack S)
        ∈ StateType.memory S)
      → ControlInstr S nothing
  ret  : ∀ {CS}
       → (p : StateType.callstack S
       ≡ (StateType.registers S , StateType.datastack S) ∷ CS)
       → ControlInstr S (just (StackDiff.pop p))
\end{code}
}

\ignore{
Определенные инструкции являются примером того, как можно реализовать
работу с регистрами и стеком данных.

\begin{code}
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
\end{code}
}

Семантика управляющих инструкций в этой формализации определяется так:
результатом исполнения управляющей инструкции в определенном стейте
является пара из обновленного стека вызовов и блока, на который передастся
управление после исполнения инструкции.

\begin{code}
exec-control : ∀ {S c}
             → State S
             → ControlInstr S c
             → CallStack
               (StateType.memory S)
               (StateType.callstack (dapply S (csChg S c)))
             × Σ (Diff (dapply S (csChg S c)))
                 (Block (dapply S (csChg S c)))
\end{code}

Семантика исполнения интересной нам инструкции `indirect jump` такова:
стек вызовов остается прежним, а управление передается на блок, адрес
которого записан в ячейке, указанной аргументом инструкции.

\begin{code}
exec-control (state Γ Ψ DS CS) (jmp[ p ])
  = CS , loadblock Ψ (loadptr Ψ p)
\end{code}

\ignore{
\begin{code}
exec-control (state Γ Ψ DS CS) (call f cont)
  = cont ∷ CS , loadblock Ψ f
exec-control (state Γ Ψ DS CS) (jmp f)
  = CS , loadblock Ψ f
exec-control (state Γ Ψ DS (f ∷ CS)) (ret refl)
  = CS , loadblock Ψ f

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

open ExecBlk Instr ControlInstr exec-instr exec-control public
open import BlockEq Block exec-block public
\end{code}
}
