## Basic block equivalence and program equivalence

The main goal of this paper is formalisation of some program equivalence.
But which programs should be considered equivalent? Consider following
example:

```asm
    main:
        mov rax, 1
        ret
```

This program puts `1` integer value to the `rax` register. Let's change it
a bit:

```asm
    main:
        call f
        mov rax, 1
        ret

    f:
        nop
        ret
```

These two programs are executed identically in some way: they transform
machine state in the same way, producing same results from same initial
machine states. To define program equivalence this way, let us define
block equivalence first. In given two programs, `main` blocks will be
equivalent in the same way: they produce same results from same initial
states.

Note that block type is machine state type required to correcly execute
this block, and machine state type includes memory type. For different
programs memory type will probably be different, therefore, blocks in
different programs will have different types and can't be equivalent. So,
technically, it will make sense to formalise blocks equivalence only inside
one program. However, we can think of two different programs `A` and `B` as
one big program `C` with blocks from `A` program and `B` program, and speak
of block equivalence inside program `C`.

\ignore{
\begin{code}
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import MetaAsm
open Diffs
open Meta
\end{code}

\begin{code}
module BlockEq
  (Block : (S : StateType) → Diff S → Set)
  (exec-block : ∀ {ST d} → Values.State Block ST → Block ST d
              → Values.State Block (dapply ST d)
              × Σ (Diff (dapply ST d)) (Block (dapply ST d)))
  where
\end{code}
\begin{code}
  open Values Block
\end{code}
}

Auxiliary defintion: "executable block of type `T`" is a pair of block of
type `T` and machine state of the same type `T`. Execution of this block
has exactly one result, even if there are conditional execution in blocks.
Uniqueness of the block execution result allows us to reason about
executable blocks.

\begin{code}
  record ExecutableBlock (ST : StateType) : Set where
    constructor block
    field
      {exdiff} : Diff ST
      exblock  : Block ST exdiff
      exstate  : State ST
\end{code}

\ignore{
\begin{code}
    exec-exblock : ExecutableBlock (dapply ST exdiff)
    exec-exblock = record { exblock = next-block ; exstate = next-state }
      where
      r : State (dapply ST exdiff) ×
          Σ (Diff (dapply ST exdiff)) (Block (dapply ST exdiff))
      r = exec-block exstate exblock
      next-state = proj₁ r
      next-block = proj₂ (proj₂ r)
  open ExecutableBlock

  exec-block-≡ : ∀ {ST}
               → {d₁ : Diff ST}     → {d₂ : Diff (dapply ST d₁)}
               → (b₁ : Block ST d₁) → (b₂ : Block (dapply ST d₁) d₂)
               → (S₁ : State ST)    → (S₂ : State (dapply ST d₁))
               → exec-block S₁ b₁ ≡ S₂ , d₂ , b₂
               → exec-exblock (block b₁ S₁) ≡ block b₂ S₂
  exec-block-≡ _ _ _ _ refl = refl
\end{code}
}

Two executable blocks `A` and `B` are equivalent, if there exists two
execution sequences starting from `A` and `B`, leading to same executable
block `C`. For example, two following blocks can be equivalent for some
initial machine states.

```asm
    f:
        mov rax, 2
        ret
```

```asm
    f:
        mov rbx, 1
        ret
```

In previous example, executable blocks `main` will be equivalent for any
equivalent initial machine states. This gives us the definition of blocks
equivalence: two blocks are equivalent, if for any equivalent initial
machine states there exist execution sequences leading to the same
executable block:

\begin{code}
  data ExBlockEq
    : {ST₁ ST₂ : StateType}
    → ExecutableBlock ST₁
    → ExecutableBlock ST₂
    → Set
    where
\end{code}

*   execution sequence can be empty if executable blocks are already same;

\begin{code}
    equal : ∀ {ST}
          → {A : ExecutableBlock ST}
          → ExBlockEq A A
\end{code}

*   execution sequence include execution of the first block if second block
    and result of execution of the first block are equivalent;

\begin{code}
    left  : ∀ {ST₁ ST}
          → {A₁ : ExecutableBlock ST₁}
          → {A₂ : ExecutableBlock (dapply ST₁ (exdiff A₁))}
          → {B : ExecutableBlock ST}
          → exec-exblock A₁ ≡ A₂
          → ExBlockEq A₂ B
          → ExBlockEq A₁ B
\end{code}

*   and vice versa, execution sequence include execution of the second
    block if first block and result of execution of the second block are
    equivalent.

\begin{code}
    right : ∀ {ST₁ ST}
          → {A₁ : ExecutableBlock ST₁}
          → {A₂ : ExecutableBlock (dapply ST₁ (exdiff A₁))}
          → {B : ExecutableBlock ST}
          → exec-exblock A₁ ≡ A₂
          → ExBlockEq B A₂
          → ExBlockEq B A₁
\end{code}
