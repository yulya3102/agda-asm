\begin{code}
module SSA where

open import Core
\end{code}

Как говорилось ранее, значения, лежащие в памяти, никогда не изменяются.
При этом все определения, касающиеся кода, могут на ссылаться на память,
потому целесообразно поместить эти определения в модуль с фиксированным
состоянием памяти.

\begin{code}
module FixedHeap (Ψ : HeapTypes) where
\end{code}

% не все йогурты одинаково полезны
Не все инструкции изменяют одинаковые части контекста исполнения.
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

Блок должен описывать, в каком контексте он будет корректно исполнен и
как он изменит этот контекст. Изменением контекста является список
добавляемых к этому контексту регистров.

\begin{code}
  data Block (Γ : RegFileTypes) : (Δ : RegFileTypes) → Set
\end{code}

Управляющая инструкция должна знать, в каком контексте она исполняется,
чтобы гарантировать, что блок, на который происходит переход, будет
исполнен корректно.

\begin{code}
  data ControlInstr (Γ : RegFileTypes) : Set
    where
\end{code}

Определим несколько управляющих инструкций, которые понадобятся в дальнейшем:

\begin{itemize}

    \item
        call соответствующего блока кода, находящегося в памяти по данному
        адресу;

\begin{code}
    call   : (f : blk Γ ∈ Ψ) → ControlInstr Γ
\end{code}

    \item
        передача управления на блок кода, адрес которого записан в ячейке
        памяти по данному адресу;

\begin{code}
    jmp[_] : (f : (blk Γ) * ∈ Ψ) → ControlInstr Γ
\end{code}

    \item
        передача управления на блок кода, расположенный в памяти по данному
        адресу.

\begin{code}
    jmp    : (f : blk Γ ∈ Ψ) → ControlInstr Γ
\end{code}

\end{itemize}

Стоит отметить, что последняя инструкция не требуется для реализации простой
динамической компоновки и приведена здесь в качестве примера возможной
инструкции.

% Вот тут мне хочется написать что-то вроде "ой, смотрите, у call и jmp
% сигнатуры одинаковые, это неспроста!" и дальше свести к тому, что это на
% самом деле проблема и это будет оговорено в дальнейшем в секции "проблемы
% этого решения"

Теперь определим тип, описывающий инструкции. Инструкция, как и управляющая
инструкция, должна знать, в каком контексте она исполняется. Но, в отличие
от управляющей инструкции, она может менять контекст. Поэтому тип
инструкции должен дополнительно описывать, как он меняет контекст. В данном
случае это будет описываться списком регистров, добавляемых к контексту.

\begin{code}
  data Instr (Γ : RegFileTypes) : (Δ : RegFileTypes) → Set
\end{code}

Для реализации простой динамической компоновки требуются только управляющие
инструкции, описанные выше. Тем не менее, стоит определить хотя бы одну
инструкцию для демонстрации, как код может выглядеть в данной реализации.
В качестве такой инструкции была выбрана инструкция загрузки значения в
регистр. Но для ее описания требуется определить, чем же являются значения.

% Вот тут на меня люто нападает тупняк, и все, что мной формулируется — это
% различные вариации на тему "тип значения должен описывать его тип", и это
% как-то абсолютно ужасно звучит. Тем не менее, надо сказать, почему сигнатура
% типа Value именно такая

\begin{code}
  data Value : Type → Set where
\end{code}

Как уже говорилось ранее, возможными значениями являются:

\begin{itemize}

    \item
        блоки кода;

\begin{code}
    function : {Γ Δ : RegFileTypes} → Block Γ Δ → Value (blk Γ)
\end{code}

    \item
        указатели на значения, лежащие в памяти.

\begin{code}
    ptr      : ∀ {τ} → τ ∈ Ψ → Value (τ *)
\end{code}

\end{itemize}

Теперь можно определить описанную выше инструкцию. Она берет произвольное
значение типа τ и добавляет к контексту один регистр этого типа.

\begin{code}
  data Instr (Γ : RegFileTypes) where
    mov  : ∀ {τ} → Value τ → Instr Γ [ τ ]
\end{code}

Опишем конструирование базовых блоков кода.

\begin{code}
  data Block (Γ : RegFileTypes) where
\end{code}

    Базовый блок — это конструкция, построенная из следующих примитивов:

\begin{itemize}

    \item
        блок, завершающий исполнение;

\begin{code}
    halt : Block Γ []
\end{code}

    \item
        блок, совершающий переход куда-либо в соответствии с результатом
        исполнения управляющей инструкции;

\begin{code}
    ↝    : ControlInstr Γ → Block Γ []
\end{code}

    \item
        блок, исполняющий инструкцию и продолжающий исполнение заданным
        блоком в измененном контексте.

\begin{code}
    _∙_  : ∀ {Γ' Δ} → Instr Γ Γ' → Block (Γ ++ Γ') Δ
         → Block Γ (Δ ++ Γ')
\end{code}

\end{itemize}

% Вероятно, сюда тоже стоит что-нибудь написать

\begin{code}
  NewBlk = Σ RegFileTypes (λ Γ → Σ RegFileTypes (Block Γ))

open FixedHeap
\end{code}

Теперь определим структуру, представляющую память. Тип этой структуры
описывает, какие именно значения находятся в памяти.

\begin{code}
data Heap : HeapTypes → Set where
\end{code}

Определение памяти практически аналогично определению односвязного списка.
Разница состоит только в том, что значение, добавляемое к списку,
может ссылаться на какие-либо значения из этого списка, что указано в его
типе.

\begin{code}
  []  : Heap []
  _,_ : ∀ {τ Ψ} → (H : Heap Ψ) → Value Ψ τ → Heap (τ ∷ Ψ)
\end{code}

Для работы с памятью необходимы, как минимум:

\begin{itemize}

    \item
        разыменование указателя, то есть получение значения по указателю
        на него;

    \item
        загрузка значения из памяти по адресу.

\end{itemize}

Так же необходимо доказать, что добавление чего-либо к списку значений,
расположенных в памяти, не нарушает корректности имеющихся значений. Это
понадобится при добавлении блоков PLT и элементов GOT.

Разыменование указателя:

\begin{code}
deref : ∀ {l Ψ} → Heap Ψ → l * ∈ Ψ → l ∈ Ψ
deref [] ()
deref (vs , function x) (here ())
deref (vs , ptr p)      (here refl) = there p
deref (vs , x)          (there p)   = there (deref vs p)
\end{code}

Леммы, доказывающие, что добавление новых значений в память не нарушает
корректности уже имеющегося в памяти:

\begin{code}
wk-value : ∀ {Ψ Ψ' τ} → Ψ ⊆ Ψ' → Value Ψ τ → Value Ψ' τ

wk-instr : ∀ {Ψ Ψ' Γ Δ} → Ψ ⊆ Ψ' → Instr Ψ Γ Δ → Instr Ψ' Γ Δ
wk-instr ss (mov x) = mov (wk-value ss x)

wk-cinstr : ∀ {Ψ Ψ' Γ} → Ψ ⊆ Ψ' → ControlInstr Ψ Γ
          → ControlInstr Ψ' Γ
wk-cinstr ss (call f) = call (ss f)
wk-cinstr ss jmp[ f ] = jmp[ ss f ]
wk-cinstr ss (jmp f) = jmp (ss f)

wk-blk : ∀ {Ψ Ψ' Γ Δ} → Ψ ⊆ Ψ' → Block Ψ Γ Δ → Block Ψ' Γ Δ
wk-blk ss halt = halt
wk-blk ss (↝ x) = ↝ (wk-cinstr ss x)
wk-blk ss (x ∙ b) = wk-instr ss x ∙ wk-blk ss b

wk-value ss (function x) = function (wk-blk ss x)
wk-value ss (ptr x)      = ptr (ss x)
\end{code}

Загрузка значения из памяти по адресу:

\begin{code}
load : ∀ {l Ψ} → Heap Ψ → l ∈ Ψ → Value Ψ l
load (vs , x) (here refl) = wk-value there x
load (vs , x) (there p)   = wk-value there (load vs p)

loadblk : ∀ {Γ Ψ} → Heap Ψ → blk Γ ∈ Ψ → NewBlk Ψ
loadblk Ψ f with load Ψ f
loadblk Ψ f | function x = _ , _ , x
\end{code}

Далее определим, что происходит непосредственно во время исполнения кода.

Стек вызовов можно представить как список адресов блоков в памяти. Для
простоты определим его как список блоков, а не их адресов.

\begin{code}
CallStack : HeapTypes → Set
CallStack Ψ = List (NewBlk Ψ)
\end{code}

Контекстом исполнения назовем пару из стека вызовов и указателя на
блок, который должен исполняться вслед за текущим. Это важно, потому что
результат исполнения некоторых инструкций зависит от того, какой блок
расположен вслед за текущим. Например, такой инструкцией является вызов
функции, при котором на стеке вызовов оказывается адрес возврата.

\begin{code}
CallCtx : HeapTypes → Set
CallCtx Ψ = CallStack Ψ × NewBlk Ψ
\end{code}

Теперь можно описать, что именно делают определенные выше инструкции.

\begin{code}
exec-control : ∀ {Γ Ψ} → Heap Ψ → CallCtx Ψ → ControlInstr Ψ Γ
             → CallCtx Ψ
\end{code}

Вызов функции добавляет адрес возврата на стек и следующим исполняемым
блоком делает загруженную из памяти функцию:

\begin{code}
exec-control H (cs , ret) (call f) = ret ∷ cs , loadblk H f
\end{code}

Indirect jump не меняет стек и передает управление на блок, загруженный
из памяти по разыменованному указателю:

\begin{code}
exec-control H (cs , ret) jmp[ f ] = cs , loadblk H (deref H f)
\end{code}

Jump не меняет стек и передает управление так же, как это делает вызов
функции:

\begin{code}
exec-control H (cs , ret) (jmp f)  = cs , loadblk H f
\end{code}

Так как я рассматриваю только переходы между блоками, я нигде не учитываю,
какие именно значения находятся в регистрах. Более того, я не учитываю, 
как инструкции влияют на контекст.

\begin{code}
exec-blk : ∀ {Γ Δ Ψ} → Heap Ψ → CallCtx Ψ → Block Ψ Γ Δ
         → CallCtx Ψ
exec-blk {Γ} H (cs , ret) halt = cs , Γ , _ , halt
exec-blk H cc (↝ x) = exec-control H cc x
exec-blk H cc (i ∙ b) = exec-blk H cc b
\end{code}

Используя описанные выше определения, можно ввести понятие эквивалентности
блоков кода: два блока считаются эквивалентными в одном контексте
исполнения, если они в итоге приводят к одному и тому же блоку с одинаковым
контекстом исполнения.

\begin{code}
data BlockEq {Ψ : HeapTypes} (H : Heap Ψ) (CC : CallCtx Ψ)
    : {Γ₁ Γ₂ Δ₁ Δ₂ : RegFileTypes}
    → Block Ψ Γ₁ Δ₁ → Block Ψ Γ₂ Δ₂ → Set
    where
\end{code}

Два блока эквивалентны, если:

\begin{itemize}

    \item
        они одинаковы;

\begin{code}
  equal  : ∀ {Γ Δ} → {B : Block Ψ Γ Δ} → BlockEq H CC B B
\end{code}

    \item
        исполнение первого из них приводит к блоку, эквивалентному второму;

\begin{code}
  left   : ∀ {Δ₁ Δ₂ Δ₃ Γ₁ Γ₂ Γ₃}
         → {A : Block Ψ Γ₁ Δ₁} → {B : Block Ψ Γ₂ Δ₂}
         → {C : Block Ψ Γ₃ Δ₃}
         → projr (exec-blk H CC C) ≡ _ , _ , A
         → BlockEq H CC A B
         → BlockEq H CC C B
\end{code}

    \item
        исполнение второго из них приводит к блоку, эквивалентному первому;

\begin{code}
  right  : ∀ {Δ₁ Δ₂ Δ₃ Γ₁ Γ₂ Γ₃}
         → {A : Block Ψ Γ₁ Δ₁} → {B : Block Ψ Γ₂ Δ₂}
         → {C : Block Ψ Γ₃ Δ₃}
         → projr (exec-blk H CC C) ≡ _ , _ , B
         → BlockEq H CC A B
         → BlockEq H CC A C
\end{code}

    \item
        исполнение обоих блоков меняет контекст исполнения и приводит к
        эквивалентным блокам.

\begin{code}
  ctxchg : ∀ {Δ₁ Δ₂ Δ₁' Δ₂' Γ₁ Γ₂ Γ₁' Γ₂'}
         → {CC' : CallCtx Ψ}
         → {A' : Block Ψ Γ₁' Δ₁'} {B' : Block Ψ Γ₂' Δ₂'}
         → BlockEq H CC' A' B'
         → {A : Block Ψ Γ₁ Δ₁}
         → exec-blk H CC A ≡ projl CC' , _ , _ , A'
         → {B : Block Ψ Γ₂ Δ₂} 
         → exec-blk H CC B ≡ projl CC' , _ , _ , B'
         → BlockEq H CC A B
\end{code}

\end{itemize}

Теперь можно описывать компоновку. В случае простой динамической компоновки
все используемые функции уже загружены в память и GOT корректно заполнен,
поэтому PLT состоит всего из одной инструкции.

\begin{code}
plt-stub : ∀ {Γ Ψ} → (blk Γ) * ∈ Ψ → Block Ψ Γ []
plt-stub label = ↝ (jmp[ label ])
\end{code}

По сравнению со статической компоновкой при динамической компоновке в память
добавляются дополнительные значения. Сначала опишем их типы.

\begin{code}
plt-heaptypes : HeapTypes → HeapTypes
\end{code}

На каждый блок кода компоновщиком генерируются:

\begin{code}
plt-heaptypes (blk Γ ∷ Ψ)
\end{code}

\begin{itemize}

    \item
        блок PLT, тип которого совпадает с типом блока, на который происходит
        переход;

\begin{code}
    = blk Γ
\end{code}

    \item
        элемент GOT, тип которого — указатель на блок, на который происходит
        переход.

\begin{code}
    ∷ blk Γ *
\end{code}

\end{itemize}

При этом сам блок кода остается на месте.

\begin{code}
    ∷ blk Γ ∷ (plt-heaptypes Ψ)
\end{code}

Все остальное при этом остается неизменным.

\begin{code}
plt-heaptypes (x ∷ Ψ) = x ∷ (plt-heaptypes Ψ)
plt-heaptypes [] = []
\end{code}

При этом все, что загружалось в память при статической компоновке, будет
загружено и при динамической компоновке.

\begin{code}
plt-⊆ : ∀ {Ψ} → Ψ ⊆ plt-heaptypes Ψ
plt-⊆ {x = blk Γ} (Data-Any.here refl)
    = Data-Any.there $ Data-Any.there (Data-Any.here refl)
plt-⊆ {x = x *} (Data-Any.here refl) = Data-Any.here refl
plt-⊆ {blk Γ ∷ ψs} (there i) = there (there (there (plt-⊆ i)))
plt-⊆ {ψ * ∷ ψs} (there i) = there (plt-⊆ i)
\end{code}

Опишем, какие значения определенных выше типов появляются в памяти.

\begin{code}
plt-heap : ∀ {Ψ} → Heap Ψ → Heap (plt-heaptypes Ψ)
plt-heap [] = []
\end{code}

На каждый блок кода из исходного набора значений, находящихся в памяти, 
генерируется:

\begin{code}
plt-heap (vs , function f) = ((plt-heap vs
\end{code}

\begin{itemize}

    \item
        сам блок кода;

\begin{code}
    , function (wk-blk plt-⊆ f))
\end{code}

    \item
        элемент GOT, указывающий на блок, лежащий перед ним в памяти;

\begin{code}
    , ptr (here refl))
\end{code}

    \item
        блок PLT, ссылающийся на элемент GOT, лежащий перед ним в памяти.

\begin{code}
    , function (plt-stub (here refl))
\end{code}

\end{itemize}

\begin{code}
plt-heap (vs , ptr x) = plt-heap vs , ptr (plt-⊆ x)
\end{code}

Зная адрес, по которому блок располагался в памяти при статической компоновке,
можно получить адрес, по которому при динамической компоновке будут
располагаться его элементы GOT и PLT.

\begin{code}
plt : ∀ {Γ Ψ} → (blk Γ) ∈ Ψ → (blk Γ) ∈ plt-heaptypes Ψ
plt (here refl) = here refl
plt {Ψ = blk Δ ∷ Ψ} (there f) = there (there (there (plt f)))
plt {Ψ = x * ∷ Ψ} (there f) = there (plt f)

got : ∀ {Γ Ψ} → (blk Γ) ∈ Ψ → (blk Γ) * ∈ plt-heaptypes Ψ
got (here refl) = there (here refl)
got {Ψ = blk Δ ∷ Ψ} (there f) = there (there (there (got f)))
got {Ψ = x * ∷ Ψ} (there f) = there (got f)
\end{code}

При смене компоновки со статической на динамическую меняется и код. Все
переходы на конкретные блоки заменяются на переходы на элементы PLT.

\begin{code}
plt-code : ∀ {Ψ Γ Δ} → Block Ψ Γ Δ → Block (plt-heaptypes Ψ) Γ Δ
plt-code halt = halt
plt-code (↝ (call f)) = ↝ (call (plt f))
plt-code (↝ (jmp[_] f)) = ↝ (jmp[ plt-⊆ f ])
plt-code (↝ (jmp f)) = ↝ (jmp (plt-⊆ f ))
plt-code (i ∙ b) = wk-instr plt-⊆ i ∙ plt-code b
\end{code}

Все требуемые примитивы определены, теперь можно доказывать эквивалентность
различных видов компоновки. Сначала докажем несколько лемм.

Блок кода эквивалентен indirect jump-у, если по указанному адресу находится
указатель на этот блок кода:

\begin{code}
jmp[]-proof : ∀ {Ψ Γ Δ} → {CC : CallCtx Ψ}
           → {H : Heap Ψ}
           → {A : Block Ψ Γ Δ}
           → (f : (blk Γ) * ∈ Ψ)
           → loadblk H (deref H f) ≡ _ , _ , A
           → BlockEq H CC A (↝ jmp[ f ])
jmp[]-proof {Ψ} {CC = CC} {H = H} {A = A} f p = right p equal
\end{code}

Вызов функции меняет контекст исполнения так, как ожидается: на стек
добавляется адрес возврата, а исполнение передается на вызываемый блок:

\begin{code}
call-proof : ∀ {Ψ Γ} → (CC : CallCtx Ψ) → {A : NewBlk Ψ}
           → {H : Heap Ψ}
           → (f : (blk Γ) ∈ Ψ)
           → loadblk H f ≡ A
           → exec-blk H CC (↝ (call f))
           ≡ ((projr CC ∷ projl CC) , A)
call-proof CC f p rewrite p = refl
\end{code}

Загрузка блока PLT, относящегося к заданной функции, действительно загружает
блок PLT. К сожалению, из-за несовершенства определений эта лемма осталась
недоказанной.

\begin{code}
loadplt : ∀ {Ψ Γ} → (H : Heap (plt-heaptypes Ψ))
        → (f : blk Γ ∈ Ψ)
        → loadblk H (plt f) ≡ Γ , [] , ↝ jmp[ got f ]
loadplt H f = {!!}
\end{code}

Блок PLT для любой функции выглядит заданным образом:

\begin{code}
jmp[]-plt-stub : ∀ {Ψ Γ} → (f : blk Γ ∈ Ψ)
               → plt-stub (got f) ≡ ↝ jmp[ got f ]
jmp[]-plt-stub f = refl
\end{code}

Загрузка блока, в типе которого указано ограничение на состояние регистров,
загружает блок, который действительно ограничивает состояние регистров
именно так. Эта лемма тоже осталась недоказанной.

\begin{code}
loadblk-Γ : ∀ {Ψ Γ} → (H : Heap Ψ) → (f : blk Γ ∈ Ψ)
          → projl (loadblk H f) ≡ Γ
loadblk-Γ H f = {!!}
\end{code}

Блок PLT эквивалентен самой функции. Эта лемма не доказана.

\begin{code}
plt-fun-eq : ∀ {Γ Ψ}
           → (H : Heap (plt-heaptypes Ψ))
           → (cc : CallCtx (plt-heaptypes Ψ))
           → (f : blk Γ ∈ Ψ)
           → BlockEq H cc
             (projr $ projr (loadblk H (plt-⊆ f)))
             (plt-stub (got f))
plt-fun-eq H cc f with jmp[]-plt-stub f | loadblk-Γ H (plt-⊆ f)
plt-fun-eq H cc f | refl | r = {!!}
\end{code}

И, наконец, доказательство того, что в любом контексте исполнения вызов
функции напрямую эквивалентен вызову соответствующего PLT.

\begin{code}
proof : ∀ {Γ Ψ}
      → (H : Heap (plt-heaptypes Ψ))
      → (f : blk Γ ∈ Ψ)
      → (cc : CallCtx (plt-heaptypes Ψ))
      → BlockEq H cc
        (wk-blk plt-⊆ (↝ (call f)))
        (↝ (call (plt f)))
proof {Γ = Γ} {Ψ = Ψ} H f ctx = ctxchg after-call just-call plt-call
    where
    newblock-f   = loadblk H (plt-⊆ f)
    called-block = projr $ projr newblock-f

    just-call : exec-blk H ctx (↝ (call $ plt-⊆ f)) ≡
                projr ctx ∷ projl ctx , newblock-f
    just-call = call-proof ctx (plt-⊆ f) refl

    plt-call : exec-blk H ctx (↝ (call $ plt f)) ≡
               projr ctx ∷ projl ctx , _ , _ , ↝ jmp[ got f ]
    plt-call = call-proof ctx (plt f) (loadplt H f)

    after-call : BlockEq H (projr ctx ∷ projl ctx , newblock-f)
                 called-block
                 (↝ jmp[ got f ])
    after-call = plt-fun-eq H (projr ctx ∷ projl ctx , newblock-f) f
\end{code}