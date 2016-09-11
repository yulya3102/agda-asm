\iftoggle{russian-draft}{
\section{Эквивалентность блоков кода}
}{
\section{Block equivalence}
}

\iftoggle{russian-draft}{
Одна из целей настоящей работы - показать эквивалентность семантик вызова
статически слинкованной функции и динамически слинкованной функции. Но
какие блоки кода должны считаться эквивалентными?
}{
This paper focuses on proving semantic equivalence of call of statically
and dynamically linked functions.  But which blocks of code should be
considered equivalent?
}

\labeledfigure{fig:eq-blocks-example}{Пример эквивалентных функций}{
\lstinputlisting[style=asm]{eq-blocks-example.asm}
}

\iftoggle{russian-draft}{
Функции \texttt{f} и \texttt{g} в листинге \ref{fig:eq-blocks-example} обе
кладут число $1$ в регистр \texttt{rax}. Эти функции исполняются одинаково
в смысле семантики большого шага:
одинаковые начальные состояния исполнителя они преобразуют в одинаковые
конечные состояния исполнителя. Определим эквивалентность функций как
эквивалентность их входных блоков.
}{
Functions \texttt{f} and \texttt{g} from listing
\ref{fig:eq-blocks-example} both store integer $1$ in the \texttt{rax}
register. This functions are executed identically from big step
semantics point of view: they transform machine state in equivalent way,
producing equivalent results from equivalent initial machine states.
Let us define function equivalence as equivalence of their start blocks.
}

\ignore{
\begin{code}
open import Data.Product
open import Data.List.Any
open Membership-≡
open import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Relation.Binary
open import Function

open import Core
open import MetaAsm
open import Diffs
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

\iftoggle{russian-draft}{
Введем несколько вспомогательных определений.

\textbf{\emph{Исполняемый блок}} - это пара из блока и состояния исполнителя
соответствующего типа.

Преимущество от определения исполняемого блока как отдельной сущности в том,
что
блок, исполняемый в заданном состоянии исполнителя, будет давать ровно один
результат, даже если сам блок содержит условный переход. Единственность
результата позволяет рассуждать об исполнении блоков. Определение
Agda-типа \emph{исполняемого блока} приведено в листинге
\ref{fig:ExecutableBlock}.
}{
Let us define several auxiliary definitions.

\textbf{\emph{Executable block}} is a pair of block and machine state of
corresponding type.

The main benefit of this definition is that execution of executable block
can produce exactly one result, even if there are conditional execution in
block. Uniqueness of the block execution result allows us to reason about
executable blocks. Definition of \emph{executable block} is shown in listing
\ref{fig:ExecutableBlock}.
}

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

\iftoggle{russian-draft}{
\textbf{\emph{Эквивалентность исполняемых блоков}}.
Два исполняемых блока $A$ и $B$ эквивалентны, если существует две
последовательности исполнения $AC$ и $BC$, начинающиеся из $A$ и $B$
соответственно, приводящие к одному и тому же блоку $C$.

В листинге \ref{fig:ExBlockEq} приведено определение Agda-типа
\emph{эквивалентности
исполняемых блоков}. Оно имеет три конструктора, позволяющих показать
эквивалентность двух исполняемых блоков в разных случаях:
}{
\textbf{\emph{Executable blocks equivalence}}.
Two executable blocks $A$ and $B$ are equivalent, if there exists two
execution sequences starting from $A$ and $B$, leading to same executable
block $C$.

Listing \ref{fig:ExBlockEq} shows the definition of the \emph{executable
blocks equivalence}. It has three constructors, each for different case:
}

\begin{itemize}
\tightlist
\item
\iftoggle{russian-draft}{
    \C{equal} - исполняемый блок $A$ эквивалентнен сам себе;
}{
    \C{equal} - executable block $A$ is equivalent to itself;
}
\item
\iftoggle{russian-draft}{
    \C{left} - результатом исполнения исполняемого блока $A_1$ является
    блок $A_2$, и блок $A_2$ эквивалентнен блоку $B$, тогда блок $A_1$
    эквивалентнен блоку $B$;
}{
    \C{left} - execution of the executable block $A_1$ results in a block
    $A_2$, and the block $A_2$ is equivalent to the block $B$;
}
\item
\iftoggle{russian-draft}{
    \C{right} - симметрично предыдущему случаю, шаг исполнения для другого
    блока.
}{
    \C{right} - simmetric to the previous case, execution step for the
    second block.
}
\end{itemize}

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

\iftoggle{russian-draft}{
Приведенное отношение действительно является отношением эквивалентности.
Доказательство требуемых свойств приведено в приложении
\ref{sec:is-equivalence}.

Но приведенное отношение не является желаемым отношением эквивалентности,
описанным ранее.
Например, если правильно подобрать начальные состояния для блоков, то
эквивалентными окажутся самые разные блоки. Такими, например, являются
блоки \texttt{rax1} и \texttt{rbx2} из листинга \ref{fig:eq-exblocks-example}.
}{
This definition meets axioms for equivalence relation, as proven in
appendix \ref{sec:is-equivalence}.

But this definition is not the desired definition of blocks equivalence,
described earlier. For example, for some initial machine states completely
different code blocks can be equivalent. For example, blocks \texttt{rax1}
and \texttt{rbx2} from listing {fig:eq-exblocks-example} are equivalent for
some specific initial machine states.
}

\labeledfigure{fig:eq-exblocks-example}{Пример эквивалентных исполняемых блоков}{
\lstinputlisting[style=asm]{eq-exblocks-example.asm}
}

\iftoggle{russian-draft}{
В листинге \ref{fig:eq-blocks-example} блоки \texttt{f} и \texttt{g} были
эквивалентными для любых начальных
состояний исполнителя. Определим эквивалентность блоков, используя
эквивалентность исполняемых блоков.

\textbf{\emph{Эквивалентность блоков}}. Два блока $f$ и $g$ эквивалентны, если
для любых начальных состояний $S$ исполняемые блоки $(f, S)$ и $(g, S)$
экививалентны.

Определение такой эквивалентности приведено в листинге
\ref{fig:BlockEqAssuming}. Кроме того, приведенное определение позволяет
указать, в каком предположении эквивалентность блоков будет выполняться.
Это важно, поскольку доказательство эквивалентности вызова статически и
динамически слинкованных программ опирается на предположение о корректности
результата работы динамического загрузчика.
}{
Blocks \texttt{f} and \texttt{g} from listing \ref{fig:eq-blocks-example}
are equivalent for any equivalent initial machine states. Let us define
blocks equivalence using executable blocks equivalence.

\textbf{\emph{Blocks equivalence}}. Two blocks $f$ and $g$ are equivalent,
if for any initial machine state $S$ executable blocks $(f, S)$ and $(g,
S)$ are equivalent.

Definition of blocks equivalence is shown in listing
\ref{fig:BlockEqAssuming}. Moreover, this definition allows to use
specified assumption to construct blocks equivalence. It's important
because proof of semantic equivalence of call of statically and
dynamically linked functions relies on assumption of dynamic loader
correctness.
}

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
