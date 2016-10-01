\ignore{
\begin{code}
module Core where

open import Data.Nat
open import Data.List
open import Data.Product

data WordType : Set
data ArbitraryType : Set
DataStackType : Set
CallStackType : Set

RegFileTypes = List WordType
HeapTypes = List ArbitraryType
DataStackType = List WordType
CallStackType = List (RegFileTypes × DataStackType)
\end{code}
}

\labeledfigure{fig:types}{Supported data types}{
\begin{code}
data WordType
  where
  _*  : ArbitraryType → WordType
  int : WordType

data ArbitraryType
  where
  atom : WordType → ArbitraryType
  code : RegFileTypes
       → DataStackType → CallStackType
       → ArbitraryType
\end{code}
}

\labeledfigure{fig:statetype}{Machine state type}{
\begin{code}
record StateType : Set
  where
  constructor sttype
  field
    registers : RegFileTypes
    memory    : HeapTypes
    datastack : DataStackType
    callstack : CallStackType
\end{code}
}
