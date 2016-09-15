# Ленивая линковка

\ignore{
\begin{code}
module LazyLinkers where
\end{code}

**TODO: натырить сюда кода из написанного после бакалаврской**

\begin{code}
open import Function
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.List
open import Data.List.Any
open Membership-≡
open import Data.List.Any.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; trans)

open import MetaAsm
open import Asm
open import Programs
\end{code}
}

\begin{code}
pltize : HeapTypes → HeapTypes
pltize [] = []
pltize (atom x ∷ Ψ) = atom x ∷ pltize Ψ
pltize (code Γ DS CS ∷ Ψ)
  = code Γ DS CS
  ∷ (code Γ DS CS
  ∷ (atom (code Γ DS CS *)
  ∷ (code Γ DS CS
  ∷ pltize Ψ)))
\end{code}

\begin{code}
plt : ∀ {Γ Ψ DS CS} → code Γ DS CS ∈ Ψ
    → code Γ DS CS ∈ pltize Ψ
plt (here refl) = here refl
plt {Ψ = atom x ∷ Ψ} (there f) = there $ plt f
plt {Ψ = code Γ DS CS ∷ Ψ} (there f)
  = there $ there (there (there (plt f)))

plt-cont : ∀ {Γ Ψ DS CS} → code Γ DS CS ∈ Ψ
         → code Γ DS CS ∈ pltize Ψ
plt-cont (here refl) = there $ here refl
plt-cont {Ψ = atom x ∷ Ψ} (there f) = there $ plt-cont f
plt-cont {Ψ = code Γ DS CS ∷ Ψ} (there f)
  = there (there (there (there (plt-cont f))))
\end{code}

\begin{code}
got : ∀ {Γ Ψ DS CS} → code Γ DS CS ∈ Ψ
    → atom (code Γ DS CS *) ∈ pltize Ψ
got (here refl) = there $ there (here refl)
got {Ψ = atom x ∷ Ψ} (there f) = there $ got f
got {Ψ = code Γ DS CS ∷ Ψ} (there f)
  = there $ there (there (there (got f)))
\end{code}

\begin{code}
func : ∀ {Γ Ψ DS CS} → code Γ DS CS ∈ Ψ
    → code Γ DS CS ∈ pltize Ψ
func (here refl) = there $ there (there (here refl))
func {Ψ = atom x ∷ Ψ} (there f) = there $ func f
func {Ψ = code Γ DS CS ∷ Ψ} (there f)
  = there $ there (there (there (func f)))
\end{code}

\begin{code}
plt-stub : ∀ {Γ Ψ DS CS}
         → atom (code Γ DS CS *) ∈ Ψ
         → Block (sttype Γ Ψ DS CS) dempty
plt-stub got = ↝ jmp[ got ]

LinkerBlockS : StateType → StateType
LinkerBlockS (sttype Γ Ψ DS CS) = sttype Γ Ψ (int ∷ DS) CS

plt-stub-cont : ∀ {ST}
              → (id : ℕ)
              → (linker : IPST (LinkerBlockS ST))
              → Block ST (sChg (onlystack (StackDiff.push int)))
plt-stub-cont id linker =
  pushc (int id) ∙
  ↝ (jmp linker)
\end{code}

\begin{code}
GOT[_]-correctness : ∀ {Γ Ψ DS CS}
                   → (f : code Γ DS CS ∈ Ψ)
                   → (H : Data (pltize Ψ))
                   → Set
GOT[ f ]-correctness H
    = loadptr H (got f) ≡ func f

PLT[_]-correctness : ∀ {Γ Ψ DS CS}
                   → (f : code Γ DS CS ∈ Ψ)
                   → (H : Data (pltize Ψ))
                   → Set
PLT[ f ]-correctness H
    = loadblock H (plt f) ≡ (dempty , plt-stub (got f))

pltize-state : StateType → StateType
pltize-state ST = record ST { memory = pltize $ StateType.memory ST }

GOT[_]-laziness : ∀ {ST}
                  → (f : IPST ST)
                  → (H : Data (StateType.memory $ pltize-state ST))
                  → Set
GOT[ f ]-laziness H = loadptr H (got f) ≡ plt-cont f
\end{code}

TODO

\ignore{
\begin{code}
exec-ijmp : ∀ {ST} → (S : State ST)
          → (p : atom (code
               (StateType.registers ST)
               (StateType.datastack ST)
               (StateType.callstack ST)
             *) ∈ StateType.memory ST)
          → exec-block S (↝ jmp[ p ])
          ≡ (S
          , loadblock
            (State.memory S)
            (loadptr (State.memory S) p))
exec-ijmp (state Γ Ψ DS CS) p = refl
\end{code}

*   состояние исполнителя в момент непосредственного вызова функции
    эквивалентно состоянию исполнителя после исполнения соответствующего
    этой функции элемента PLT при условии корректно заполненного GOT;

\begin{code}
exec-plt : ∀ {Γ Ψ DS CS}
         → (f : code Γ DS CS ∈ Ψ)
         → (S : State (sttype Γ (pltize Ψ) DS CS))
         → GOT[ f ]-correctness (State.memory S)
         → exec-block S (plt-stub (got f))
         ≡ (S , loadblock (State.memory S) (func f))
exec-plt f S p rewrite sym p = exec-ijmp S (got f)
\end{code}

Используя эти леммы, можно доказать, что если GOT заполнен корректно,
то верна внешняя эквивалентность блока PLT, использующего соответствующий
функции элемент GOT, и самой функции:

\begin{code}
exblock-eq-proof : ∀ {Γ Ψ DS CS}
                 → (f : code Γ DS CS ∈ Ψ)
                 → (S : State (sttype Γ (pltize Ψ) DS CS))
                 → GOT[ f ]-correctness (State.memory S)
                 → ExBlockEq
                   (block (plt-stub (got f)) S)
                   (block (proj₂ $ loadblock (State.memory S) (func f)) S)
exblock-eq-proof f S p = left (exec-block-≡ (plt-stub (got f)) _ S S (exec-plt f S p)) equal
\end{code}
}

\begin{code}
block-eq-proof : ∀ {Γ Ψ DS CS}
               → (f : code Γ DS CS ∈ Ψ)
               → BlockEqAssuming
                 (λ S → (GOT[ f ]-correctness $ State.memory S)
                      × (PLT[ f ]-correctness $ State.memory S))
                 (plt f)
                 (func f)
block-eq-proof {Γ} {Ψ} {DS} {CS} f = block-eq-assuming lemma
  where
    ST = sttype Γ Ψ DS CS
    lemma : (S : State $ pltize-state ST)
          → (GOT[ f ]-correctness $ State.memory S)
          × (PLT[ f ]-correctness $ State.memory S)
          → ExBlockEq
            (construct-exblock (plt f) S)
            (construct-exblock (func f) S)
    lemma S (got-correctness , plt-correctness)
      rewrite plt-correctness = exblock-eq-proof f S got-correctness
\end{code}

\begin{code}
linker-diff : ∀ ST → Diff $ pltize-state $ LinkerBlockS ST
linker-diff ST = dsChg (StackDiff.pop refl)

LinkerS = pltize-state ∘ LinkerBlockS

exec-pushc-i : ∀ {Ψ StateΓ StateDS StateCS}
             → {τ : WordType} (value : RegValue Ψ τ)
             → (R : Registers Ψ StateΓ)
             → (M : Data Ψ)
             → (DS : DataStack Ψ StateDS)
             → (CS : CallStack Ψ StateCS)
             → exec-instr (state R M DS CS) (pushc value)
             ≡ (R , M , (value ∷ DS))
exec-pushc-i value R M D C = refl

exec-jmp : {ST : StateType}
         → (S : State ST)
         → (func : IPST ST)
         → exec-block S (↝ (jmp func))
         ≡ (S , (loadblock (State.memory S) func))
exec-jmp (state Γ Ψ DS CS) func = refl

SRegisters : StateType → Set
SRegisters (sttype Γ Ψ DS CS) = Registers Ψ Γ

SDataStack : StateType → Set
SDataStack (sttype Γ Ψ DS CS) = DataStack Ψ DS

SCallStack : StateType → Set
SCallStack (sttype Γ Ψ DS CS) = CallStack Ψ CS

record LinkerBase {ST : StateType} : Set where
  field
    linker : IPST $ LinkerS ST
    linker-diff-eq : (M : Data (pltize $ StateType.memory ST))
                   → proj₁ (loadblock M linker)
                   ≡ linker-diff ST
    function : ℕ → IPST ST

  {-
  Идентификатор заданной функции: некоторое число, такое, что линкер ему
  сопоставит заданную функцию.
  -}
  FuncID : IPST ST → Set
  FuncID f = Σ ℕ (λ id → function id ≡ f)

  {-
  Корректность указателя plt-cont: загруженный по нему блок
  действительно является продолжением plt-stub. Я не задаю
  конструктивно, какие действительно значения располагаются
  в памяти, потому мне приходится использовать это свойство
  как дополнительный аргумент всех доказательств, использующих
  указатель plt-cont
  -}
  PLT-cont[_]-correctness : {f : IPST ST} → FuncID f
                          → Data (pltize $ StateType.memory ST)
                          → Set
  PLT-cont[_]-correctness (id , refl) M
    = loadblock M (plt-cont $ function id)
    ≡ (_ , plt-stub-cont id linker)

  private
    {-
    Много вспомогательных доказательств про то, как изменятся конкретные
    куски исполнителя после вызова линкера.
    -}
    module Exec where
      regs-after-linker : (R : SRegisters (pltize-state ST))
                        → (M : Data (StateType.memory $ pltize-state ST))
                        → SRegisters $ dapply
                            (LinkerS ST)
                            (proj₁ $ loadblock M linker)
      regs-after-linker R M
        with proj₁ $ loadblock M linker | linker-diff-eq M
      ... | ._ | refl = R

      memory-after-linker : (M : Data (StateType.memory $ pltize-state ST))
                          → (d : Diff (LinkerS ST))
                          → (f : IPST ST)
                          → Data $ StateType.memory (dapply (LinkerS ST) d)
      memory-after-linker M d f
        rewrite sym $ DiffLemmas.mem-diff _ d
        = (store (got f) M (Value.atom $ ptr $ func f))

      datastack-after-linker : SDataStack (LinkerS ST)
                             → {d : Diff (LinkerS ST)}
                             → d ≡ linker-diff ST
                             → SDataStack (dapply (LinkerS ST) d)
      datastack-after-linker (x ∷ DS) refl = DS

      callstack-after-linker : SCallStack $ pltize-state ST
                             → {d : Diff (LinkerS ST)}
                             → d ≡ linker-diff ST
                             → SCallStack (dapply (LinkerS ST) d)
      callstack-after-linker CS refl = CS

      state-after-linker : (S : State $ LinkerS ST)
                         → State $ dapply (LinkerS ST) (proj₁ $ loadblock (State.memory S) linker)
      state-after-linker (state R M DS CS) = state
        (regs-after-linker R M)
        (memory-after-linker M (proj₁ $ loadblock M linker) $ function $ unint $ peek DS)
        (datastack-after-linker DS $ linker-diff-eq M)
        (callstack-after-linker CS $ linker-diff-eq M)
  open Exec public

  block-after-linker : (S : State $ LinkerS ST)
                     → IPST (dapply _
                            (proj₁ $ loadblock (State.memory S) linker))
  block-after-linker (state R M DS CS)
    rewrite linker-diff-eq M
    = func (function (unint $ peek DS))

  same-state-after-linker : (S : State $ LinkerS ST)
                          → State (pltize-state ST)
  same-state-after-linker (state R M DS CS)
    with state-after-linker (state R M DS CS)
  ... | S'
    rewrite linker-diff-eq M
    = S'

record Linker {ST : StateType} (L : LinkerBase {ST}) : Set where
  open LinkerBase L public
  field
    exec-linker : (S : State $ LinkerS ST)
                → exec-block S
                  (proj₂ $ loadblock (State.memory S) linker)
                ≡ (state-after-linker S
                , loadblock (State.memory (state-after-linker S))
                            (block-after-linker S))

  {-
  То, что исполняется после вызова линкера для функции, эквивалентно
  самой функции:
  -}
  func-after-linker-eq : (f : IPST ST)
                       → (id : FuncID f)
                       → (R : SRegisters $ LinkerS ST)
                       → (M : Data $ StateType.memory $ LinkerS ST)
                       → (DS : SDataStack $ LinkerS ST)
                       → (CS : SCallStack $ LinkerS ST)
                       → unint (peek DS) ≡ proj₁ id
                       → ExBlockEq
                         (construct-exblock
                           (func $ function $ proj₁ id)
                           (same-state-after-linker (state R M DS CS))
                           )
                         (construct-exblock
                           (func f)
                           (state R
                             (store (got f) M
                                       (Value.atom $ ptr $ func f))
                             (dspop DS) CS))
  func-after-linker-eq f (id , p) R M (int .id ∷ DS) CS refl
    with proj₁ $ loadblock M linker | linker-diff-eq M
  ... | ._ | refl rewrite p = equal

  {-
  Линкер для функции в стейте S эквивалентен самой функции
  в стейте S с заполненным элементом GOT и снятым значением с вершины
  стека данных:
  -}
  func-linker-eq : (f : IPST ST)
                 → (id : FuncID f)
                 → (R : SRegisters $ pltize-state ST)
                 → (M : Data $ StateType.memory $ pltize-state ST)
                 → (DS : SDataStack $ pltize-state ST)
                 → (CS : SCallStack $ pltize-state ST)
                 → ExBlockEq
                   (construct-exblock linker
                     (state R M (int (proj₁ id) ∷ DS) CS))
                   (construct-exblock (func f)
                    (state R (store (got f) M (Value.atom $ ptr $ func f)) DS CS))
  func-linker-eq f id R M DS CS 
    = left (exec-block-≡ (proj₂ $ loadblock M linker) _
                         (state R M (int (proj₁ id) ∷ DS) CS) _
                         (exec-linker (state R M (int (proj₁ id) ∷ DS) CS)))
           {!func-after-linker-eq f id R M (int (proj₁ id) ∷ DS) CS refl!}

  exec-plt-cont :
                -- Для идентификатора некоторой функции
                (id : ℕ)
                -- и стейта типа pltize-state ST
                → (R : SRegisters $ pltize-state ST)
                → (M : Data $ StateType.memory $ pltize-state ST)
                → (DS : SDataStack $ pltize-state ST)
                → (CS : SCallStack $ pltize-state ST)
                -- исполнение plt-stub-cont
                → exec-block (state R M DS CS)
                  (plt-stub-cont id linker)
                -- добавляет на вершину стека заданный идентификатор
                ≡ (state R M (int id ∷ DS) CS
                -- и переходит к исполнению линкера
                , (loadblock M linker))
  exec-plt-cont id R M DS CS
    rewrite exec-pushc-i (int id) R M DS CS
          | exec-jmp 
                     
                     (state R M (int id ∷ DS) CS)
                     linker
    = refl

  {-
  plt-stub-cont в стейте S эквивалентен функции в стейте S с заполненным
  GOT.
  -}
  func-plt-cont-eq : (f : IPST ST)
                   → (id : FuncID f)
                   → (S : State $ pltize-state ST)
                   → ExBlockEq
                     (block (plt-stub-cont (proj₁ id) linker) S)
                     (block
                     (proj₂ $ loadblock (State.memory S) (func f))
                     record S {
                       memory = (store (got f) (State.memory S)
                                 (Value.atom $ ptr $ func f))
                     })
  func-plt-cont-eq f (id , p) (state R M DS CS)
    = {!left (exec-plt-cont id R M DS CS)
           (func-linker-eq f (id , p) R M DS CS)!}

  {-
  plt-stub функции при "ленивом" GOT и корректном указателе plt-cont
  эквивалентен самой функции при заполненном GOT:
  -}
  func-plt-lazy-eq : (f : IPST ST)
                   → (id : FuncID f)
                   → (S : State $ pltize-state ST)
                   → GOT[ f ]-laziness $ State.memory S
                   → PLT-cont[ id ]-correctness $ State.memory S
                   → ExBlockEq
                     (block (plt-stub (got f)) S)
                     (block (proj₂ $ loadblock (State.memory S) (func f))
                     record S {
                       memory = store
                         (got f)
                         (State.memory S)
                         (Value.atom $ ptr $ func f)
                     })
  func-plt-lazy-eq ._ (id , refl) S p1 p2
    = {!left (trans (exec-ijmp S (got $ function id))
                  (cong (λ b → S , b)
                        (trans (cong (loadblock $ State.memory S) p1) p2)))
           (func-plt-cont-eq (function id) (id , refl) S)!}

open Linker

{-
При заполненном GOT или "ленивом" GOT и корректном plt-cont
plt-stub для функции эквивалентен самой функции при заполненном GOT
-}
lazy-proof : ∀ {ST}
           → (f : IPST ST)
           → (S : State (pltize-state ST))
           → {L : LinkerBase {ST}}
           → (l : Linker L)
           → (id : FuncID l f)
           → GOT[ f ]-correctness (State.memory S)
           ⊎ GOT[ f ]-laziness (State.memory S)
           × PLT-cont[_]-correctness l id (State.memory S)
           → ExBlockEq
             (block (plt-stub (got f)) S)
             (block (proj₂ $ loadblock (State.memory S) (func f))
                     (record S {
                       memory = store (got f)
                                         (State.memory S)
                                          (Value.atom (ptr (func f)))
                     }))
lazy-proof f S l id (inj₁ x)
  rewrite store-loaded-ptr (State.memory S) (got f) x
  = exblock-eq-proof f S x
lazy-proof f S l id (inj₂ (x , y))
  = func-plt-lazy-eq l f id S x y
\end{code}
