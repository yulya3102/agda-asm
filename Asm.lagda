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

\ignore{
\begin{code}
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

\begin{code}
control-instr-semantics : ∀ {S c}
             → State S
             → ControlInstr S c
             → CallStack
               (StateType.memory S)
               (StateType.callstack (dapply S (csChg S c)))
             × Σ (Diff (dapply S (csChg S c)))
                 (Block (dapply S (csChg S c)))
\end{code}
}

Важной частью динамической линковки являются инструкции перехода и их
семантика, в частности, инструкция непрямого перехода \C{jmp[\_]}.
В используемой формализации управляющие инструкции могут менять только стек
вызовов, и семантика этих инструкций определяет, как именно инструкция
меняет стек вызовов и какая последовательность инструкций будет исполняться
следующей.

Так, для инструкции \C{jmp[\_]} семантика определена следующим образом:

\begin{code}
control-instr-semantics (state Γ Ψ DS CS) (jmp[ p ])
  = CS , loadblock Ψ (loadptr Ψ p)
\end{code}

В состоянии исполнителя с состоянием регистров \AgdaBound{\Gamma},
состоянием памяти \AgdaBound{\Psi}, стеком данных \AgdaBound{DS} и стеком
вызовов \AgdaBound{CS} исполнение инструкции непрямого перехода по
указателю \AgdaBound{p} не изменит стек вызовов (он останется тем же, каким
и был -- \AgdaBound{CS}), а исполнение перейдет на последовательность
инструкций, загруженную из памяти \AgdaBound{\Psi} по указателю,
загруженному из ячейки \AgdaBound{p} памяти \AgdaBound{\Psi}.

\ignore{
\begin{code}
control-instr-semantics (state Γ Ψ DS CS) (call f cont)
  = cont ∷ CS , loadblock Ψ f
control-instr-semantics (state Γ Ψ DS CS) (jmp f)
  = CS , loadblock Ψ f
control-instr-semantics (state Γ Ψ DS (f ∷ CS)) (ret refl)
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

open ExecBlk Instr ControlInstr exec-instr control-instr-semantics public
open import BlockEq Block exec-block public
\end{code}
}
