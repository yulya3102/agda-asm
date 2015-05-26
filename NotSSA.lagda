Все начальные определения идентичны определениям из предыдущей версии.

\begin{code}
module NotSSA where

open import OXIj.BrutalDepTypes
open Data-List

data Type : Set
RegFileTypes : Set
HeapTypes : Set

RegFileTypes = List Type
HeapTypes    = List Type

data Type where
  _*  : Type → Type
  blk : (Γ : RegFileTypes) → Type

open Data-Any
open Membership {A = Type} _≡_
\end{code}

Ранее для описания типа инструкций использовался список добавляемых к
контексту регистров. Это приводило к тому, что никакая инструкция не
могла изменить уже добавленные ранее регистры. Указанную проблему
можно решить, введя тип, описывающий изменение контекста, и соответственно
изменив тип инструкции.

\begin{code}
module TDiffs where
\end{code}

Определим тип, описывающий одно изменение списка фиксированной длины:
в таком списке можно только менять элементы, что и требуется от регистров.
Так как не любое изменение можно применить к произвольному списку, его
тип должен ограничивать, к какому списку его можно применять.

\begin{code}
  data TChg (Γ : RegFileTypes) : Set where
\end{code}

Для того, чтобы описать изменение элемента в списке, необходимо указать,
какая позиция меняется и на что.

\begin{code}
    tchgcr : ∀ {r} → r ∈ Γ → (r' : Type) → TChg Γ
\end{code}

Сами по себе изменения не несут особого смысла: необходимо указать, как
они применяются к спискам.

\begin{code}
  appChg : (Γ : RegFileTypes) → TChg Γ → RegFileTypes
  appChg (_ ∷ Γ) (tchgcr (here refl) r') = r' ∷ Γ
  appChg (a ∷ Γ) (tchgcr (there r) r')
    = a ∷ appChg Γ (tchgcr r r')
\end{code}

Блок кода последовательно применяет изменения к контексту регистров. Для
того, чтобы описать набор изменений, делаемый блоком кода, введем еще один
тип:

\begin{code}
  data TDiff (Γ : RegFileTypes) : Set where
\end{code}

\begin{itemize}

  \item
    набор изменений может быть пустым (например, если блок состоит из одной
    управляющей инструкции)

\begin{code}
    tdempty  : TDiff Γ
\end{code}

  \item
    либо это изменение, добавленное перед уже имеющимся набором

\begin{code}
    tdchg    : (tchg : TChg Γ) → TDiff (appChg Γ tchg) → TDiff Γ
\end{code}

\end{itemize}

Наборы изменений тоже применяются к спискам.

\begin{code}
  tdapply : (Γ : RegFileTypes) → TDiff Γ → RegFileTypes
  tdapply Γ tdempty = Γ
  tdapply Γ (tdchg tchg td) = tdapply (appChg Γ tchg) td
\end{code}

Два набора изменений можно применять последовательно:

\begin{code}
  tdappend : ∀ {Γ} → (td : TDiff Γ)
           → TDiff (tdapply Γ td) → TDiff Γ
  tdappend tdempty b = b
  tdappend (tdchg tchg a) b = tdchg tchg (tdappend a b)

open TDiffs
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
  data Block (Γ : RegFileTypes) : TDiff Γ → Set
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
  data Instr (Γ : RegFileTypes) : TDiff Γ → Set
\end{code}

Как и в прошлый раз, перед определением инструкций определим возможные
значения.

\begin{code}
  data Value : Type → Set where
    function : {Γ : RegFileTypes} → {d : TDiff Γ} → Block Γ d
             → Value (blk Γ)
    ptr      : ∀ {τ} → τ ∈ Ψ → Value (τ *)
\end{code}
  
Теперь можно определить инструкцию, загружающую некоторое значение в регистр.
В этой реализации инструкция не добавляет регистр, а описывает изменение
конкретного регистра из списка на значение нового типа.

\begin{code}
  data Instr (Γ : RegFileTypes) where
    mov  : ∀ {r τ} → (r∈Γ : r ∈ Γ) → Value τ
         → Instr Γ (tdchg (tchgcr r∈Γ τ) tdempty)
\end{code}

И, наконец, определим конструкторы блока.
  
\begin{code}
  data Block (Γ : RegFileTypes) where
    halt : Block Γ tdempty
    ↝    : ControlInstr Γ → Block Γ tdempty
    _∙_  : ∀ {d' d} → Instr Γ d' → Block (tdapply Γ d') d
         → Block Γ (tdappend d' d)
\end{code}
