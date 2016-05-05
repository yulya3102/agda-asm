\ignore{
\begin{code}
module Programs where

open import MetaAsm
open import Asm
\end{code}

We will think of program as of binary loaded to memory. Due to this
assumption we can ignore memory mapping problems. With this assumption, we
can say that *program* is pair of memory state (with code and data) and
start block.

\begin{code}
record Program (ST : StateType) : Set where
  constructor program
  field
    memory : Data (StateType.memory ST)
    start  : IPRT (StateType.memory ST)
                  (StateType.registers ST)
                  (StateType.datastack ST)
                  (StateType.callstack ST)
\end{code}

"The program" is a set of blocks with given start block. Two programs are
equivalent, if their start blocks are equivalent.

\begin{code}
record ProgramEq {ST : StateType} (P₁ P₂ : Program ST) : Set₁ where
  constructor program-eq
  field
    start-eq : BlockEq (Program.start P₁)
                       (Program.start P₂)
\end{code}

Defined block equivalence is special case of bisimulation relation. This
relation is substitutive, so a block can be replaced with equivalent block
without changing the result of execution.

}
