\begin{code}
module Programs where

open import MetaAsm
open import Asm

record Program (ST : StateType) : Set where
  constructor program
  field
    memory : Data (StateType.memory ST)
    start  : IPRT (StateType.memory ST)
                  (StateType.registers ST)
                  (StateType.datastack ST)
                  (StateType.callstack ST)

record ProgramEq {ST : StateType} (P₁ P₂ : Program ST) : Set₁ where
  constructor program-eq
  field
    start-eq : BlockEq (Program.start P₁)
                       (Program.start P₂)
\end{code}
