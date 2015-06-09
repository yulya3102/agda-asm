## Наборы изменений

Эта секция описывает, как решить первую из проблем предыдущей реализации.

\ignore{
\begin{code}
module NotSSA where

open import Data.List
open import Data.List.Any
open Membership-≡
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
\end{code}
}

Ранее для описания типа инструкций использовался список добавляемых к
контексту регистров. Это приводило к тому, что никакая инструкция не
могла изменить уже добавленные ранее регистры. Указанную проблему
можно решить, введя тип, описывающий изменение контекста, и соответственно
изменив тип инструкции.

### Описание изменений регистров

\ignore{
\begin{code}
module Diffs where
\end{code}
}

Определим тип, описывающий одно изменение списка фиксированной длины:
в таком списке можно только менять элементы, что и требуется от регистров.
Так как не любое изменение можно применить к произвольному списку, его
тип должен ограничивать, к какому списку его можно применять.

\begin{code}
  module ListChg (A : Set) where
    data Chg (Γ : List A) : Set where
\end{code}

Для того, чтобы описать изменение элемента в списке, необходимо указать,
какая позиция меняется и на что.

\begin{code}
      chg : ∀ {τ} → τ ∈ Γ → A → Chg Γ
\end{code}

Сами по себе изменения не несут особого смысла: необходимо указать, как
они применяются к спискам.

\begin{code}
    chgapply : (Γ : List A) → Chg Γ → List A
    chgapply (_ ∷ Γ) (chg (here refl) σ) = σ ∷ Γ
    chgapply (τ ∷ Γ) (chg (there p)   σ) = τ ∷ chgapply Γ (chg p σ)
\end{code}

Блок кода последовательно применяет изменения к контексту регистров,
значит, в его типе должен быть описан набор изменений.

Набор изменений является общим для изменений различных видов.

\begin{code}
  module Diff
    {Ctx : Set}
    {Chg : Ctx → Set}
    (chgapply : (Γ : Ctx) → Chg Γ → Ctx)
    where
\end{code}

Так же, как и для изменения, тип набора изменений ограничивает контекст, к
которому его можно применять.

\begin{code}
    data Diff (Γ : Ctx) : Set where
\end{code}

Набор изменений — это:

*   либо пустой набор;

\begin{code}
      dempty  : Diff Γ
\end{code}

*   либо это изменение, добавленное перед уже имеющимся набором.

\begin{code}
      dchg    : (c : Chg Γ) → Diff (chgapply Γ c) → Diff Γ
\end{code}

Для набора изменений определены несколько функций:

*   применение набора к контексту — это последовательное применение всех
    изменений из набора;

\begin{code}
    dapply : (Γ : Ctx) → Diff Γ → Ctx
    dapply Γ dempty = Γ
    dapply Γ (dchg c d) = dapply (chgapply Γ c) d
\end{code}

*   объединение двух наборов изменений;

\begin{code}
    dappend : ∀ {Γ} → (d : Diff Γ)
            → Diff (dapply Γ d) → Diff Γ
    dappend dempty b = b
    dappend (dchg c a) b = dchg c (dappend a b)
\end{code}

*   лемма, доказывающая, что объединение с пустым набором не меняет набор;

\begin{code}
    dappend-dempty-lemma : ∀ {Γ} → (d : Diff Γ)
                         → dappend d dempty ≡ d
    dappend-dempty-lemma dempty = refl
    dappend-dempty-lemma (dchg c d)
      rewrite dappend-dempty-lemma d = refl
\end{code}

*   лемма, доказывающая, что применение объединения наборов эквивалентно
    последовательному применению этих наборов.

\begin{code}
    dappend-dapply-lemma : ∀ S → (d₁ : Diff S)
                         → (d₂ : Diff (dapply S d₁))
                         → dapply S (dappend d₁ d₂)
                         ≡ dapply (dapply S d₁) d₂
    dappend-dapply-lemma S dempty d₂ = refl
    dappend-dapply-lemma S (dchg c d₁) d₂
      = dappend-dapply-lemma (chgapply S c) d₁ d₂
\end{code}

<!---
% вообще-то содержательная часть здесь заканчивается
% далее следует proof-of-concept
-->

### Блоки, инструкции и значения

Используя определенный тип, переопределим типы блоков и инструкций.

\ignore{
\begin{code}
open import DevCore
\end{code}
}

\begin{code}
module FixedHeap (Ψ : HeapTypes) where
\end{code}

\ignore{
\begin{code}
  open Diffs.ListChg Type
  open Diffs.Diff chgapply
\end{code}
}

Ранее тип блока описывал список добавляемых регистров. Теперь он описывает
набор изменений, применяемых к уже имеющимся регистрам.

\begin{code}
  data Block (Γ : RegFileTypes) : Diff Γ → Set
\end{code}

Управляющие инструкции не меняют регистров, поэтому их определение останется
неизменным.

\ignore{
\begin{code}
  data ControlInstr (Γ : RegFileTypes) : Set
    where
    call   : (f : blk Γ ∈ Ψ) → ControlInstr Γ
    jmp[_] : (f : (blk Γ) * ∈ Ψ) → ControlInstr Γ
    jmp    : (f : blk Γ ∈ Ψ) → ControlInstr Γ
\end{code}
}

Тип инструкции изменим так же, как изменился тип блока: список добавляемых
к контексту регистров заменим на описание набора изменений.

\begin{code}
  data Instr (Γ : RegFileTypes) : Chg Γ → Set
\end{code}

\ignore{
\begin{code}
  data Value : Type → Set where
    function : {Γ : RegFileTypes} → {d : Diff Γ} → Block Γ d
             → Value (blk Γ)
    ptr      : ∀ {τ} → τ ∈ Ψ → Value (τ *)
\end{code}
}
  
В этой реализации инструкция не добавляет регистр, а описывает изменение
конкретного регистра из списка на значение нового типа.

\begin{code}
  data Instr (Γ : RegFileTypes) where
    mov  : ∀ {r τ} → (r∈Γ : r ∈ Γ) → Value τ
         → Instr Γ (chg r∈Γ τ)
\end{code}

И, наконец, определим конструкторы блока.
  
\begin{code}
  data Block (Γ : RegFileTypes) where
    ↝    : ControlInstr Γ → Block Γ dempty
    _∙_  : ∀ {c d} → Instr Γ c → Block (chgapply Γ c) d
         → Block Γ (dchg c d)
\end{code}
