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

data BranchInstr (S : StateType) : Maybe (CallStackChg S) → Set
data Instr (S : StateType) : SmallChg S → Set

open Blocks BranchInstr Instr public
open Values Block public

data BranchInstr (S : StateType) where
  call : ∀ {Γ DS}
       → (f : code
         (StateType.registers S)
         (StateType.datastack S)
         ((Γ , DS) ∷ StateType.callstack S)
         ∈ StateType.memory S)
       → (cont : code Γ DS (StateType.callstack S)
               ∈ StateType.memory S)
       → BranchInstr S (Maybe.just $ StackDiff.push (Γ , DS))
  jmp[_] : (ptr : atom
         (code
         (StateType.registers S)
         (StateType.datastack S)
         (StateType.callstack S) *)
         ∈ StateType.memory S)
       → BranchInstr S nothing
  jmp : (f : code
        (StateType.registers S)
        (StateType.datastack S)
        (StateType.callstack S)
        ∈ StateType.memory S)
      → BranchInstr S nothing
  ret  : ∀ {CS}
       → (p : StateType.callstack S
       ≡ (StateType.registers S , StateType.datastack S) ∷ CS)
       → BranchInstr S (just (StackDiff.pop p))

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

branch-instr-semantics : ∀ {S c}
             → State S
             → BranchInstr S c
             → CallStack
               (StateType.memory S)
               (StateType.callstack (dapply S (csChg c)))
             × Σ (TypeDiff (dapply S (csChg c)))
                 (Block (dapply S (csChg c)))
branch-instr-semantics (state Γ Ψ DS CS) (call f cont)
  = cont ∷ CS , loadblock Ψ f
branch-instr-semantics (state Γ Ψ DS CS) (jmp f)
  = CS , loadblock Ψ f
branch-instr-semantics (state Γ Ψ DS (f ∷ CS)) (ret refl)
  = CS , loadblock Ψ f
\end{code}
}

\labeledfigure{fig:ijmp-semantics}{Indirect jump instruction semantics}{
\begin{code}
branch-instr-semantics S (jmp[ p ])
  = State.callstack S
  , loadblock (State.memory S)
    (loadptr (State.memory S) p)
\end{code}
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

open ExecBlk Instr BranchInstr exec-instr branch-instr-semantics public
open import BlockEq Block exec-block public
\end{code}
}
