\ignore{
\begin{code}
module SSA where

open import DevCore

open import Data.List
open import Data.Product
open import Data.List.Any
open Membership-≡
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function
\end{code}
}

### Блоки, инструкции и значения

Как говорилось ранее, значения, лежащие в памяти, никогда не изменяются.
При этом все определения, касающиеся кода, могут на ссылаться на память,
потому целесообразно поместить эти определения в модуль с фиксированным
состоянием памяти.

\begin{code}
module FixedHeap (Ψ : DataType) where
\end{code}

Не все инструкции изменяют одинаковые части состояния исполнителя.
Некоторые инструкции изменяют состояние регистров, некоторые определяют,
какой код будет исполняться дальше. Второй тип инструкций будем называть
управляющими инструкциями.

Принимая во внимание тот факт, что с точки зрения компоновки необходимо
рассматривать лишь переходы между различными частями загруженного в
память кода, удобно ввести понятие базового блока кода — последовательности
инструкций, не содержащей никаких переходов, и впоследствии рассматривать
лишь переходы между этими блоками. В терминах различных видов инструкций
определение блока описывается как последовательность инструкций, меняющих
регистры, заканчивающаяся управляющей инструкцией.

Блок должен описывать, в каком состоянии исполнителя он будет корректно
исполнен и как он его изменит. Изменением состояния исполнителя является
список добавляемых регистров.

\begin{code}
  data Block (Γ : RegTypes) : (Δ : RegTypes) → Set
\end{code}

Управляющая инструкция должна знать, при состоянии регистров она
исполняется, чтобы гарантировать, что блок, на который происходит переход,
будет исполнен корректно.

\begin{code}
  data ControlInstr (Γ : RegTypes) : Set
    where
\end{code}

Определим несколько управляющих инструкций, которые понадобятся в дальнейшем:

*   call соответствующего блока кода, находящегося в памяти по данному
    адресу;

\begin{code}
    call   : (f : block Γ ∈ Ψ) → ControlInstr Γ
\end{code}

*   передача управления на блок кода, адрес которого записан в ячейке
    памяти по данному адресу;

\begin{code}
    jmp[_] : (f : (block Γ) * ∈ Ψ) → ControlInstr Γ
\end{code}

*   передача управления на блок кода, расположенный в памяти по данному
    адресу.

\begin{code}
    jmp    : (f : block Γ ∈ Ψ) → ControlInstr Γ
\end{code}

Стоит отметить, что последняя инструкция не требуется для реализации простой
динамической компоновки и приведена здесь в качестве примера возможной
инструкции.

<!---
% Вот тут мне хочется написать что-то вроде "ой, смотрите, у call и jmp
% сигнатуры одинаковые, это неспроста!" и дальше свести к тому, что это на
% самом деле проблема и это будет оговорено в дальнейшем в секции "проблемы
% этого решения"
-->

Определим тип, описывающий инструкции. Инструкция, как и управляющая
инструкция, должна знать, при каком состоянии регистров она исполняется.
Но, в отличие от управляющей инструкции, она может его менять. Поэтому тип
инструкции должен дополнительно описывать, как он меняет состояние
регистров. В данном случае это будет описываться списком регистров,
добавляемых к уже имеющимся.

\begin{code}
  data Instr (Γ : RegTypes) : (Δ : RegTypes) → Set
\end{code}

Для реализации простой динамической компоновки требуются только управляющие
инструкции, описанные выше. Тем не менее, стоит определить хотя бы одну
инструкцию для демонстрации того, как код может выглядеть в данной реализации.
В качестве такой инструкции была выбрана инструкция загрузки значения в
регистр. Но для ее описания требуется определить, чем же являются значения.

<!---
% Вот тут на меня люто нападает тупняк, и все, что мной формулируется — это
% различные вариации на тему "тип значения должен описывать его тип", и это
% как-то абсолютно ужасно звучит. Тем не менее, надо сказать, почему сигнатура
% типа Value именно такая
-->

\begin{code}
  data Value : Type → Set where
\end{code}

Как уже говорилось ранее, возможными значениями являются:

*   блоки кода;

\begin{code}
    block : {Γ Δ : RegTypes} → Block Γ Δ → Value (block Γ)
\end{code}

*   указатели на значения, лежащие в памяти.

\begin{code}
    ptr      : ∀ {τ} → τ ∈ Ψ → Value (τ *)
\end{code}

Теперь можно определить описанную выше инструкцию. Она принимает произвольное
значение типа τ и добавляет к имеющимся регистрам один регистр этого типа.

\begin{code}
  data Instr (Γ : RegTypes) where
    mov  : ∀ {τ} → Value τ → Instr Γ [ τ ]
\end{code}

Опишем конструирование базовых блоков кода.

\begin{code}
  data Block (Γ : RegTypes) where
\end{code}

Базовый блок — это конструкция, построенная из следующих примитивов:

*   блок, совершающий переход куда-либо в соответствии с результатом
    исполнения управляющей инструкции;

\begin{code}
    ↝    : ControlInstr Γ → Block Γ []
\end{code}

*   блок, исполняющий инструкцию и продолжающий исполнение заданным
    блоком в измененном состоянии исполнителя.

\begin{code}
    _∙_  : ∀ {Δ₁ Δ₂} → Instr Γ Δ₁ → Block (Γ ++ Δ₁) Δ₂
         → Block Γ (Δ₂ ++ Δ₁)
\end{code}

Для удобства определим тип блока, для которого заранее не известно,
на какое состояние исполнителя он рассчитывает и как он его меняет. Это
может быть полезным, например, при определении функции, загружающей
произвольный блок кода из памяти.

\begin{code}
  NewBlk = Σ RegTypes (λ Γ → Σ RegTypes (Block Γ))
\end{code}

\ignore{
\begin{code}
open FixedHeap
\end{code}
}

### Память

Определим структуру, представляющую память. Тип этой структуры
описывает, значения каких типов и на каких позициях находятся в памяти.

\begin{code}
data Data : DataType → Set where
\end{code}

Определение памяти практически аналогично определению односвязного списка.
Разница состоит только в том, что значение, добавляемое к списку,
может ссылаться на какие-либо значения из этого списка, что указано в его
типе.

\begin{code}
  []  : Data []
  _,_ : ∀ {τ Ψ} → (H : Data Ψ) → Value Ψ τ → Data (τ ∷ Ψ)
\end{code}

Для работы с памятью необходимо определить разыменование указателя, то есть
получение значения по указателю на него:

\begin{code}
deref : ∀ {l Ψ} → Data Ψ → l * ∈ Ψ → l ∈ Ψ
deref [] ()
deref (vs , block x) (here ())
deref (vs , ptr p)   (here refl) = there p
deref (vs , x)       (there p)   = there (deref vs p)
\end{code}

Для каждой возможной сущности в старом наборе данных определено
корректное преобразование в сущность в новом наборе данных:

\begin{code}
module WeakeningLemmas {Ψ Ψ' : DataType} (ss : Ψ ⊆ Ψ') where
\end{code}

*   значение из старого набора данных корректно преобразуется в
    значение в новом наборе данных (реализация приведена ниже);

\begin{code}
  wk-value : ∀ {τ} → Value Ψ τ → Value Ψ' τ
\end{code}

*   инструкция из старого набора данных корректно преобразуется в
    инструкцию в новом наборе данных;

\begin{code}
  wk-instr : ∀ {Γ Δ} → Instr Ψ Γ Δ → Instr Ψ' Γ Δ
  wk-instr (mov x) = mov (wk-value x)
\end{code}

*   управляющая инструкция из старого набора данных корректно
    преобразуется в управляющую инструкцию в новом наборе данных;

\begin{code}
  wk-cinstr : ∀ {Γ} → ControlInstr Ψ Γ → ControlInstr Ψ' Γ
  wk-cinstr (call f) = call (ss f)
  wk-cinstr jmp[ f ] = jmp[ ss f ]
  wk-cinstr (jmp f) = jmp (ss f)
\end{code}

*   блок кода из старого набора данных корректно преобразуется в
    блок кода в новом наборе данных.

\begin{code}
  wk-block : ∀ {Γ Δ} → Block Ψ Γ Δ → Block Ψ' Γ Δ
  wk-block (↝ x) = ↝ (wk-cinstr x)
  wk-block (x ∙ b) = wk-instr x ∙ wk-block b
\end{code}

Реализация описанной выше функции `wk-value`:

\begin{code}
  wk-value (block x) = block (wk-block x)
  wk-value (ptr x)   = ptr (ss x)
\end{code}

\ignore{
\begin{code}
open WeakeningLemmas
\end{code}
}

Определим функцию для загрузки значения из памяти по указанному адресу:

\begin{code}
load : ∀ {l Ψ} → Data Ψ → l ∈ Ψ → Value Ψ l
load (vs , x) (here refl) = wk-value there x
load (vs , x) (there p)   = wk-value there (load vs p)
\end{code}

Так же для удобства определим функцию, загружающую произвольный блок кода:

\begin{code}
loadblk : ∀ {Γ Ψ} → Data Ψ → block Γ ∈ Ψ → NewBlk Ψ
loadblk Ψ f with load Ψ f
loadblk Ψ f | block x = _ , _ , x
\end{code}

### Исполнение кода

Далее определим, что происходит непосредственно во время исполнения кода.

Стек вызовов можно представить как список адресов блоков в памяти. Для
простоты определим его как список блоков, а не их адресов.

\begin{code}
CallStack : DataType → Set
CallStack Ψ = List (NewBlk Ψ)
\end{code}

_Контекстом исполнения_ назовем пару из стека вызовов и указателя на
блок, который должен исполняться вслед за текущим. Это важно, потому что
результат исполнения некоторых инструкций зависит от того, какой блок
расположен вслед за текущим. Например, такой инструкцией является вызов
функции, при котором на стеке вызовов оказывается адрес возврата.

\begin{code}
CallCtx : DataType → Set
CallCtx Ψ = CallStack Ψ × NewBlk Ψ
\end{code}

Теперь можно описать, что именно делают определенные выше инструкции в
некотором определенном контексте исполнения и фиксированном состоянии
памяти.

\begin{code}
module InCallCtx {Ψ : DataType} (H : Data Ψ) (cc : CallCtx Ψ)
  where
\end{code}

Результатом исполнения управляющей инструкции является измененный контекст
исполнения.

\begin{code}
  exec-control : ∀ {Γ} → ControlInstr Ψ Γ → CallCtx Ψ
\end{code}

Вызов функции добавляет адрес возврата на стек и следующим исполняемым
блоком делает загруженную из памяти функцию:

\begin{code}
  exec-control (call f) = proj₂ cc ∷ proj₁ cc , loadblk H f
\end{code}

Indirect jump не меняет стек и передает управление на блок, загруженный
из памяти по разыменованному указателю:

\begin{code}
  exec-control jmp[ f ] = proj₁ cc , loadblk H (deref H f)
\end{code}

Jump не меняет стек и передает управление так же, как это делает вызов
функции:

\begin{code}
  exec-control (jmp f) = proj₁ cc , loadblk H f
\end{code}

Результатом исполнения блока является не только измененный контекст
исполнения, но и измененное состояние регистров. Но в данной реализации
рассматриваются только переходы между блоками и никак не учитывается
состояние регистров, что отражено в описании результата исполнения блока
кода.

\begin{code}
  exec-block : ∀ {Γ Δ} → Block Ψ Γ Δ → CallCtx Ψ
  exec-block (↝ x) = exec-control x
  exec-block (i ∙ b) = exec-block b
\end{code}

\ignore{
\begin{code}
open InCallCtx
\end{code}
}

### Эквивалентность блоков кода

Используя описанные выше определения, можно ввести понятие эквивалентности
блоков кода: два блока считаются _эквивалентными в одном контексте
исполнения_, если для обоих блоков указана последовательность исполнения,
приводящая к одному и тому же блоку с одинаковым контекстом исполнения.

\begin{code}
data BlockEq {Ψ : DataType} (H : Data Ψ) (CC : CallCtx Ψ)
    : {Γ₁ Γ₂ Δ₁ Δ₂ : RegTypes}
    → Block Ψ Γ₁ Δ₁ → Block Ψ Γ₂ Δ₂ → Set
    where
\end{code}

Два блока эквивалентны, если:

*   они одинаковы;

\begin{code}
  equal  : ∀ {Γ Δ} → {B : Block Ψ Γ Δ} → BlockEq H CC B B
\end{code}

*   исполнение первого из них приводит к блоку, эквивалентному второму;

\begin{code}
  left   : ∀ {Δ₁ Δ₂ Δ₃ Γ₁ Γ₂ Γ₃}
         → {A : Block Ψ Γ₁ Δ₁} → {B : Block Ψ Γ₂ Δ₂}
         → {C : Block Ψ Γ₃ Δ₃}
         → proj₂ (exec-block H CC C) ≡ _ , _ , A
         → BlockEq H CC A B
         → BlockEq H CC C B
\end{code}

*   исполнение второго из них приводит к блоку, эквивалентному первому;

\begin{code}
  right  : ∀ {Δ₁ Δ₂ Δ₃ Γ₁ Γ₂ Γ₃}
         → {A : Block Ψ Γ₁ Δ₁} → {B : Block Ψ Γ₂ Δ₂}
         → {C : Block Ψ Γ₃ Δ₃}
         → proj₂ (exec-block H CC C) ≡ _ , _ , B
         → BlockEq H CC A B
         → BlockEq H CC A C
\end{code}

*   исполнение обоих блоков меняет контекст исполнения и приводит к
    эквивалентным блокам.

\begin{code}
  ctxchg : ∀ {Δ₁ Δ₂ Δ₁' Δ₂' Γ₁ Γ₂ Γ₁' Γ₂'}
         → {CC' : CallCtx Ψ}
         → {A' : Block Ψ Γ₁' Δ₁'} {B' : Block Ψ Γ₂' Δ₂'}
         → BlockEq H CC' A' B'
         → {A : Block Ψ Γ₁ Δ₁}
         → exec-block H CC A ≡ proj₁ CC' , _ , _ , A'
         → {B : Block Ψ Γ₂ Δ₂} 
         → exec-block H CC B ≡ proj₁ CC' , _ , _ , B'
         → BlockEq H CC A B
\end{code}

### Компоновка кода

В случае простой динамической компоновки все используемые функции уже
загружены в память и GOT корректно заполнен, поэтому PLT состоит всего из
одной инструкции.

\begin{code}
plt-stub : ∀ {Γ Ψ} → (block Γ) * ∈ Ψ → Block Ψ Γ []
plt-stub got = ↝ (jmp[ got ])
\end{code}

При динамической компоновке в память добавляются дополнительные значения.
Сначала опишем их типы.

\begin{code}
pltize : DataType → DataType
\end{code}

На каждый блок кода компоновщиком генерируются:

\begin{code}
pltize (block Γ ∷ Ψ)
\end{code}

*   блок PLT, тип которого совпадает с типом блока, на который происходит
    переход;

\begin{code}
    = block Γ
\end{code}

*   элемент GOT, тип которого — указатель на блок, на который происходит
    переход.

\begin{code}
    ∷ block Γ *
\end{code}

При этом сам блок кода остается на месте.

\begin{code}
    ∷ block Γ ∷ (pltize Ψ)
\end{code}

Все остальное при этом остается неизменным.

\begin{code}
pltize (x ∷ Ψ) = x ∷ (pltize Ψ)
pltize [] = []
\end{code}

При этом все, что загружалось в память при статической компоновке, будет
загружено и при динамической компоновке.

\begin{code}
plt-⊆ : ∀ {Ψ} → Ψ ⊆ pltize Ψ
plt-⊆ {x = block Γ} (here refl) = there $ there (here refl)
plt-⊆ {x = x * } (here refl) = here refl
plt-⊆ {block Γ ∷ ψs} (there i) = there $ there (there (plt-⊆ i))
plt-⊆ {ψ * ∷ ψs} (there i) = there (plt-⊆ i)
\end{code}

Опишем, какие значения определенных выше типов появляются в памяти.

\begin{code}
pltize-data : ∀ {Ψ} → Data Ψ → Data (pltize Ψ)
pltize-data [] = []
\end{code}

На каждый блок кода из исходного набора значений, находящихся в памяти, 
генерируется:

\begin{code}
pltize-data (vs , block f) = ((pltize-data vs
\end{code}

*   сам блок кода;

\begin{code}
    , block (wk-block plt-⊆ f))
\end{code}

*   элемент GOT, указывающий на блок, лежащий перед ним в памяти;

\begin{code}
    , ptr (here refl))
\end{code}

*   блок PLT, ссылающийся на элемент GOT, лежащий перед ним в памяти.

\begin{code}
    , block (plt-stub (here refl))
\end{code}

Указатели на значения корректно преобразуются при добавлении в память
таблиц GOT и PLT.

\begin{code}
pltize-data (vs , ptr x) = pltize-data vs , ptr (plt-⊆ x)
\end{code}

Зная адрес, по которому блок располагался в памяти при статической компоновке,
можно получить адрес, по которому при динамической компоновке будут
располагаться соответствующие ему:

*   элемент таблицы PLT;

\begin{code}
plt : ∀ {Γ Ψ} → (block Γ) ∈ Ψ → (block Γ) ∈ pltize Ψ
plt (here refl) = here refl
plt {Ψ = block Δ ∷ Ψ} (there f) = there (there (there (plt f)))
plt {Ψ = x * ∷ Ψ} (there f) = there (plt f)
\end{code}

*   элемент таблицы GOT.

\begin{code}
got : ∀ {Γ Ψ} → (block Γ) ∈ Ψ → (block Γ) * ∈ pltize Ψ
got (here refl) = there (here refl)
got {Ψ = block Δ ∷ Ψ} (there f) = there (there (there (got f)))
got {Ψ = x * ∷ Ψ} (there f) = there (got f)
\end{code}

При смене компоновки со статической на динамическую меняется и код. Все
вызовы функций заменяются на вызовы соответствующих элементов PLT, а для
каждого перехода исправляется адрес перехода в соответствии с изменением
адреса функции.

\begin{code}
pltize-code : ∀ {Ψ Γ Δ} → Block Ψ Γ Δ → Block (pltize Ψ) Γ Δ
pltize-code (↝ (call f)) = ↝ (call (plt f))
pltize-code (↝ jmp[ f ]) = ↝ (jmp[ plt-⊆ f ])
pltize-code (↝ (jmp f)) = ↝ (jmp (plt-⊆ f ))
pltize-code (i ∙ b) = wk-instr plt-⊆ i ∙ pltize-code b
\end{code}

### Доказательства

Все требуемые примитивы определены, теперь можно доказывать эквивалентность
различных видов компоновки. Сначала докажем несколько лемм.

Блок кода эквивалентен indirect jump-у, если по указанному адресу находится
указатель на этот блок кода:

\begin{code}
jmp[]-proof : ∀ {Ψ Γ Δ} → {CC : CallCtx Ψ}
           → {H : Data Ψ}
           → {A : Block Ψ Γ Δ}
           → (f : (block Γ) * ∈ Ψ)
           → loadblk H (deref H f) ≡ _ , _ , A
           → BlockEq H CC A (↝ jmp[ f ])
jmp[]-proof {Ψ} {CC = CC} {H = H} {A = A} f p = right p equal
\end{code}

Вызов функции меняет контекст исполнения так, как ожидается: на стек
добавляется адрес возврата, а исполнение передается на вызываемый блок:

\begin{code}
call-proof : ∀ {Ψ Γ} → (CC : CallCtx Ψ) → {A : NewBlk Ψ}
           → {H : Data Ψ}
           → (f : (block Γ) ∈ Ψ)
           → loadblk H f ≡ A
           → exec-block H CC (↝ (call f))
           ≡ ((proj₂ CC ∷ proj₁ CC) , A)
call-proof CC f p rewrite p = refl
\end{code}

Загрузка блока PLT, относящегося к заданной функции, действительно загружает
блок PLT. К сожалению, из-за несовершенства определений эта лемма осталась
недоказанной.

\begin{code}
loadplt : ∀ {Ψ Γ} → (H : Data (pltize Ψ))
        → (f : block Γ ∈ Ψ)
        → loadblk H (plt f) ≡ Γ , [] , ↝ jmp[ got f ]
loadplt H f = {!!}
\end{code}

Блок PLT для любой функции выглядит заданным образом:

\begin{code}
jmp[]-plt-stub : ∀ {Ψ Γ} → (f : block Γ ∈ Ψ)
               → plt-stub (got f) ≡ ↝ jmp[ got f ]
jmp[]-plt-stub f = refl
\end{code}

Загрузка блока, в типе которого указано ограничение на состояние регистров,
загружает блок, который действительно ограничивает состояние регистров
именно так. Эта лемма тоже осталась недоказанной.

\begin{code}
loadblk-Γ : ∀ {Ψ Γ} → (H : Data Ψ) → (f : block Γ ∈ Ψ)
          → proj₁ (loadblk H f) ≡ Γ
loadblk-Γ H f = {!!}
\end{code}

Блок PLT эквивалентен самой функции. Эта лемма не доказана.

\begin{code}
plt-fun-eq : ∀ {Γ Ψ}
           → (H : Data (pltize Ψ))
           → (cc : CallCtx (pltize Ψ))
           → (f : block Γ ∈ Ψ)
           → BlockEq H cc
             (proj₂ $ proj₂ (loadblk H (plt-⊆ f)))
             (plt-stub (got f))
plt-fun-eq H cc f with jmp[]-plt-stub f | loadblk-Γ H (plt-⊆ f)
plt-fun-eq H cc f | refl | r = {!!}
\end{code}

И, наконец, доказательство того, что в любом контексте исполнения вызов
функции напрямую эквивалентен вызову соответствующего PLT.

\begin{code}
proof : ∀ {Γ Ψ}
      → (H : Data (pltize Ψ))
      → (f : block Γ ∈ Ψ)
      → (cc : CallCtx (pltize Ψ))
      → BlockEq H cc
        (wk-block plt-⊆ (↝ (call f)))
        (↝ (call (plt f)))
proof {Γ = Γ} {Ψ = Ψ} H f ctx = ctxchg after-call just-call plt-call
    where
    newblock-f   = loadblk H (plt-⊆ f)
    called-block = proj₂ $ proj₂ newblock-f

    just-call : exec-block H ctx (↝ (call $ plt-⊆ f)) ≡
                proj₂ ctx ∷ proj₁ ctx , newblock-f
    just-call = call-proof ctx (plt-⊆ f) refl

    plt-call : exec-block H ctx (↝ (call $ plt f)) ≡
               proj₂ ctx ∷ proj₁ ctx , _ , _ , ↝ jmp[ got f ]
    plt-call = call-proof ctx (plt f) (loadplt H f)

    after-call : BlockEq H (proj₂ ctx ∷ proj₁ ctx , newblock-f)
                 called-block
                 (↝ jmp[ got f ])
    after-call = plt-fun-eq H (proj₂ ctx ∷ proj₁ ctx , newblock-f) f
\end{code}
