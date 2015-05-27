\begin{code}
module NotSSA where

open import Core
\end{code}

Ранее для описания типа инструкций использовался список добавляемых к
контексту регистров. Это приводило к тому, что никакая инструкция не
могла изменить уже добавленные ранее регистры. Указанную проблему
можно решить, введя тип, описывающий изменение контекста, и соответственно
изменив тип инструкции.

\begin{code}
module Diffs where
\end{code}

Определим тип, описывающий одно изменение списка фиксированной длины:
в таком списке можно только менять элементы, что и требуется от регистров.
Так как не любое изменение можно применить к произвольному списку, его
тип должен ограничивать, к какому списку его можно применять.

\begin{code}
  data Chg (Γ : List Type) : Set where
\end{code}

Для того, чтобы описать изменение элемента в списке, необходимо указать,
какая позиция меняется и на что.

\begin{code}
    chg : ∀ {τ} → τ ∈ Γ → Type → Chg Γ
\end{code}

Сами по себе изменения не несут особого смысла: необходимо указать, как
они применяются к спискам.

\begin{code}
  chgapply : (Γ : List Type) → Chg Γ → List Type
  chgapply (_ ∷ Γ) (chg (here refl) σ) = σ ∷ Γ
  chgapply (τ ∷ Γ) (chg (there p)   σ) = τ ∷ chgapply Γ (chg p σ)
\end{code}

Блок кода последовательно применяет изменения к контексту регистров. Для
того, чтобы описать набор изменений, делаемый блоком кода, введем еще один
тип:

\begin{code}
  data Diff (Γ : List Type) : Set where
\end{code}

\begin{itemize}

  \item
    набор изменений может быть пустым (например, если блок состоит из одной
    управляющей инструкции)

\begin{code}
    dempty  : Diff Γ
\end{code}

  \item
    либо это изменение, добавленное перед уже имеющимся набором

\begin{code}
    dchg    : (c : Chg Γ) → Diff (chgapply Γ c) → Diff Γ
\end{code}

\end{itemize}

Наборы изменений тоже применяются к спискам.

\begin{code}
  dapply : (Γ : List Type) → Diff Γ → List Type
  dapply Γ dempty = Γ
  dapply Γ (dchg c d) = dapply (chgapply Γ c) d
\end{code}

Два набора изменений можно применять последовательно:

\begin{code}
  dappend : ∀ {Γ} → (d : Diff Γ)
          → Diff (dapply Γ d) → Diff Γ
  dappend dempty b = b
  dappend (dchg c a) b = dchg c (dappend a b)

open Diffs
\end{code}

% вообще-то содержательная часть здесь заканчивается
% далее следует proof-of-concept

Используя определенный тип, переопределим типы блоков и инструкций.

\begin{code}
module FixedHeap (Ψ : HeapTypes) where
\end{code}

Ранее тип блока описывал список добавляемых регистров. Теперь он описывает
набор изменений, применяемых к уже имеющимся регистрам.

\begin{code}
  data Block (Γ : RegFileTypes) : Diff Γ → Set
\end{code}

Управляющие инструкции не меняют регистров, поэтому их определение останется
неизменным.

\begin{code}
  data ControlInstr (Γ : RegFileTypes) : Set
    where
    call   : (f : blk Γ ∈ Ψ) → ControlInstr Γ
    jmp[_] : (f : (blk Γ) * ∈ Ψ) → ControlInstr Γ
    jmp    : (f : blk Γ ∈ Ψ) → ControlInstr Γ
\end{code}

Тип инструкции изменим так же, как изменился тип блока: список добавляемых
к контексту регистров заменим на описание набора изменений.

\begin{code}
  data Instr (Γ : RegFileTypes) : Diff Γ → Set
\end{code}

Как и в прошлый раз, перед определением инструкций определим возможные
значения.

\begin{code}
  data Value : Type → Set where
    function : {Γ : RegFileTypes} → {d : Diff Γ} → Block Γ d
             → Value (blk Γ)
    ptr      : ∀ {τ} → τ ∈ Ψ → Value (τ *)
\end{code}
  
Теперь можно определить инструкцию, загружающую некоторое значение в регистр.
В этой реализации инструкция не добавляет регистр, а описывает изменение
конкретного регистра из списка на значение нового типа.

\begin{code}
  data Instr (Γ : RegFileTypes) where
    mov  : ∀ {r τ} → (r∈Γ : r ∈ Γ) → Value τ
         → Instr Γ (dchg (chg r∈Γ τ) dempty)
\end{code}

И, наконец, определим конструкторы блока.
  
\begin{code}
  data Block (Γ : RegFileTypes) where
    halt : Block Γ dempty
    ↝    : ControlInstr Γ → Block Γ dempty
    _∙_  : ∀ {d' d} → Instr Γ d' → Block (dapply Γ d') d
         → Block Γ (dappend d' d)
\end{code}
