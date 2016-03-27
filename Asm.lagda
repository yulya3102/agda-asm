## Ассемблер x86-64

\ignore{
\begin{code}
module Asm where

open import Data.Product
open import Data.List
open import Data.List.Any
open Membership-≡
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Function

open import Functions public

open Meta public
open Diffs public
\end{code}
}

\begin{code}
data ControlInstr (S : StateType) : Maybe (CallStackChg S) → Set
data Instr (S : StateType) : SmallChg S → Set

open Blocks ControlInstr Instr public
open Values Block public
\end{code}

Как было сказано ранее, определяемые инструкции могут не совпадать с
имеющимися в реальном ассемблере. Такой инструкцией является, например,
инструкция `call`. Дополнительным параметром она принимает указатель на
блок, который будет добавлен на стек вызовов. В реальный ассемблер эта
инструкция может быть транслироваться двумя инструкциями: `call` нужного
блока, за которым следует `jmp` на второй указанный блок.

Многие реализованные инструкции не требуются для реализации блока PLT и
приведены здесь, чтобы показать возможность корректного определения
подобных инструкций.

\begin{code}
data ControlInstr (S : StateType) where
  call : ∀ {Γ DS}
       → (f : block
         (StateType.registers S)
         (StateType.datastack S)
         ((Γ , DS) ∷ StateType.callstack S)
         ∈ StateType.memory S)
       → (cont : block Γ DS (StateType.callstack S)
               ∈ StateType.memory S)
       → ControlInstr S (just $ StackDiff.push (Γ , DS))
  jmp[_] : (ptr : atom
         (block
         (StateType.registers S)
         (StateType.datastack S)
         (StateType.callstack S) *)
         ∈ StateType.memory S)
       → ControlInstr S nothing
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

Определенные инструкции являются примером того, как можно реализовать
работу с регистрами и стеком данных.

\begin{code}
data Instr (S : StateType) where
  mov  : ∀ {σ τ}
       → (r : σ ∈ StateType.registers S)
       → RegValue (StateType.memory S) τ
       → Instr S (onlyreg (RegDiff.chg r τ))
  push : ∀ {τ}
       → τ ∈ StateType.registers S
       → Instr S (onlystack (StackDiff.push τ))
  pop  : ∀ {σ τ DS}
       → (r : σ ∈ StateType.registers S)
       → (p : StateType.datastack S ≡ τ ∷ DS)
       → Instr S (regstack (RegDiff.chg r τ) (StackDiff.pop p))
\end{code}

Функции, определяющие результаты исполнения заданных инструкций, определяются
тривиально.

\begin{code}
exec-control : ∀ {S c}
             → State S
             → ControlInstr S c
             → CallStack
               (StateType.memory S)
               (StateType.callstack (dapply S (csChg S c)))
             × Σ (Diff (dapply S (csChg S c)))
                 (Block (dapply S (csChg S c)))
exec-control (state Γ Ψ DS CS) (call f cont)
  = cont ∷ CS , loadblock Ψ f
exec-control (state Γ Ψ DS CS) (jmp[ p ])
  = CS , loadblock Ψ (loadptr Ψ p)
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
exec-instr (state Γ Ψ (v ∷ DS) CS) (pop r refl)
  = toreg Γ r v , Ψ , DS

open ExecBlk Instr ControlInstr exec-instr exec-control public
open Eq Block exec-block public
\end{code}
