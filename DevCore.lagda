В первую очередь стоит описывать, как определить корректность 
ассемблерного кода и какие типы должны быть использованы для этого.

Все значения, находящиеся либо в памяти, либо в регистрах, должны
иметь какой-либо тип. Так же стоит описывать состояние набора регистров,
потому что блоки кода могут рассчитывать на наличие в регистрах значений
конкретных типов. То же самое можно сказать и про состояние памяти.

\ignore{
\begin{code}
module DevCore where

open import Data.List
\end{code}
}

\begin{code}
data Type : Set
RegFileTypes : Set
HeapTypes : Set
\end{code}

Состояние регистров можно представить списком типов, причем каждому
регистру должен соответстовать элемент списка. В этом случае регистр
является индексом в этом списке.

Аналогичные рассуждения верны и для состояния памяти.

\begin{code}
RegFileTypes = List Type
HeapTypes    = List Type
\end{code}

Рассматриваемыми мной значениями являются только блоки кода и указатели
куда-либо. При этом корректность исполнения блока кода можно гарантировать,
ограничив состояние регистров и памяти, которые должны быть на момент начала
исполнения блока. Но для простоты считаем, что значения, находящиеся
в памяти, никогда не изменяются, поэтому тип блока описывает только
требуемое состояние регистров.

\begin{code}
data Type where
  _*  : Type → Type
  blk : (Γ : RegFileTypes) → Type
\end{code}
