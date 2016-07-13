# Эквивалентность блоков кода

Одна из целей настоящей работы - показать эквивалентность семантик вызова
статически слинкованной функции и динамически слинкованной функции. Но
какие блоки кода должны считаться эквивалентными?

\ignore{
The main goal of this paper is formalisation of some program equivalence.
But which programs should be considered equivalent? Consider following
example:
}

\labeledfigure{fig:eq-blocks-example}{Пример эквивалентных функций}{
\lstinputlisting[style=asm]{eq-blocks-example.asm}
}

Функции \texttt{f} и \texttt{g} в листинге \ref{fig:eq-blocks-example} обе
кладут число $1$ в регистр \texttt{rax}. Эти функции исполняются одинаково
в смысле семантики большого шага:
одинаковые начальные состояния исполнителя они преобразуют в одинаковые
конечные состояния исполнителя. Определим эквивалентность функций как
эквивалентность их входных блоков.

\ignore{
These two programs are executed identically in some way: they transform
machine state in the same way, producing same results from same initial
machine states. To define program equivalence this way, let us define
block equivalence first. In given two programs, `main` blocks will be
equivalent in the same way: they produce same results from same initial
states.

\begin{code}
open import Data.Product
open import Data.List.Any
open Membership-≡
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Binary
open import Function

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

Auxiliary defintion: "executable block of type $T$" is a pair of block of
type $T$ and machine state of the same type $T$. Execution of this block
has exactly one result, even if there are conditional execution in blocks.
Uniqueness of the block execution result allows us to reason about
executable blocks.
}

Введем вспомогательное определение: *исполняемый блок* - это пара из
блока и состояния исполнителя соответствующего типа. Смысл этого
определения в том, что
блок, исполняемый в заданном состоянии исполнителя, будет давать ровно один
результат, даже если сам блок содержит условные переходы. Единственность
результата позволяет рассуждать об исполнении блоков. Определение
*исполняемого блока* приведено в листинге \ref{fig:ExecutableBlock}.

\labeledfigure{fig:ExecutableBlock}{Определение исполняемого блока}{
\begin{code}
  record ExecutableBlock (ST : StateType) : Set
    where
    constructor block
    field
      {exdiff} : Diff ST
      exblock  : Block ST exdiff
      exstate  : State ST
\end{code}
}

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
               → exec-block S₁ b₁ ≡ (S₂ , d₂ , b₂)
               → exec-exblock (block b₁ S₁) ≡ block b₂ S₂
  exec-block-≡ _ _ _ _ refl = refl

  construct-exblock : ∀ {ST} → IPST ST → State ST → ExecutableBlock ST
  construct-exblock B S = block (proj₂ $ loadblock (State.memory S) B) S
\end{code}
}

Два исполняемых блока $A$ и $B$ эквивалентны, если существует две
последовательности исполнения $AC$ и $BC$, начинающиеся из $A$ и $B$
соответственно, приводящие к одному и тому же блоку $C$.

\ignore{
Two executable blocks $A$ and $B$ are equivalent, if there exists two
execution sequences starting from $A$ and $B$, leading to same executable
block $C$.
}

\ignore{
For example, two following blocks can be equivalent for some
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
*   execution sequence can be empty if executable blocks are already same;
*   execution sequence include execution of the first block if second block
    and result of execution of the first block are equivalent;
*   and vice versa, execution sequence include execution of the second
    block if first block and result of execution of the second block are
    equivalent.
}

В листинге \ref{fig:ExBlockEq} приведено определение *эквивалентности
исполняемых блоков*. Оно имеет три конструктора, позволяющих показать
эквивалентность двух исполняемых блоков в разных случаях:

*   \C{equal} - исполняемый блок $A$ эквивалентнен сам себе;
*   \C{left} - результатом исполнения исполняемого блока $A_1$ является
    блок $A_2$, и блок $A_2$ эквивалентнен блоку $B$, тогда блок $A_1$
    эквивалентнен блоку $B$;
*   \C{right} - симметрично предыдущему случаю, шаг исполнения для другого
    блока.

\labeledfigure{fig:ExBlockEq}{Определение эквивалентности исполняемых блоков}{
\begin{code}
  data ExBlockEq
    : {ST₁ ST₂ : StateType}
    → ExecutableBlock ST₁
    → ExecutableBlock ST₂
    → Set
    where
    equal : ∀ {ST}
          → {A : ExecutableBlock ST}
          → ExBlockEq A A
    left  : ∀ {ST₁ ST}
          → {A₁ : ExecutableBlock ST₁}
          → {A₂ : ExecutableBlock
                    (dapply ST₁ (exdiff A₁))}
          → {B : ExecutableBlock ST}
          → exec-exblock A₁ ≡ A₂
          → ExBlockEq A₂ B
          → ExBlockEq A₁ B
    right : ∀ {ST₁ ST}
          → {A₁ : ExecutableBlock ST₁}
          → {A₂ : ExecutableBlock
                    (dapply ST₁ (exdiff A₁))}
          → {B : ExecutableBlock ST}
          → exec-exblock A₁ ≡ A₂
          → ExBlockEq B A₂
          → ExBlockEq B A₁
\end{code}
}

Приведенное отношение действительно является отношением эквивалентности.
Доказательство требуемых свойств приведено в приложении
\ref{sec:is-equivalence}.

Но приведенное отношение не является желаемым отношением эквивалентности,
описанным ранее.
Например, если правильно подобрать начальные состояния для блоков, то
эквивалентными окажутся самые разные блоки. Такими, например, являются
блоки \texttt{rax1} и \texttt{rbx2} из листинга \ref{fig:eq-exblocks-example}.

\labeledfigure{fig:eq-exblocks-example}{Пример эквивалентных исполняемых блоков}{
\lstinputlisting[style=asm]{eq-exblocks-example.asm}
}

В листинге \ref{fig:eq-blocks-example} блоки \texttt{f} и \texttt{g} были
эквивалентными для любых начальных
состояний исполнителя. Определим эквивалентность блоков, используя
эквивалентность исполняемых блоков: два блока $f$ и $g$ эквивалентны, если
для любых начальных состояний $S$ исполняемые блоки $(f, S)$ и $(g, S)$
экививалентны. Определение такой эквивалентности приведено в листинге
\ref{fig:BlockEqAssuming}. Кроме того, приведенное определение позволяет
указать, в каком предположении эквивалентность блоков будет выполняться.
Это важно, поскольку доказательство эквивалентности вызова статически и
динамически слинкованных программ опирается на предположение о корректности
результата работы динамического загрузчика.

\labeledfigure{fig:BlockEqAssuming}{Определение эквивалентности блоков}{
\begin{code}
  record BlockEqAssuming
    {Γ : RegFileTypes}
    {Ψ : HeapTypes}
    {DS : DataStackType}
    {CS : CallStackType}
    (assumption
        : State (sttype Γ Ψ DS CS) → Set)
    (A : code Γ DS CS ∈ Ψ)
    (B : code Γ DS CS ∈ Ψ)
    : Set₁
    where
    constructor block-eq-assuming
    field
      eq : (S : State (sttype Γ Ψ DS CS))
         → assumption S
         → ExBlockEq
            (construct-exblock A S)
            (construct-exblock B S)
\end{code}
}

\ignore{
\begin{code}
  open BlockEqAssuming public

  BlockEq : {ST : StateType}
          → (A : IPST ST)
          → (B : IPST ST)
          → Set₁
  BlockEq A B = BlockEqAssuming (λ S → ⊤) A B

  block-eq : {ST : StateType}
           → {A : IPST ST}
           → {B : IPST ST}
           → ((S : State ST)
             → ExBlockEq (block (proj₂ $ loadblock (State.memory S) A) S)
                         (block (proj₂ $ loadblock (State.memory S) B) S))
           → BlockEq A B
  block-eq eq = block-eq-assuming (λ S _ → eq S)
\end{code}
}
