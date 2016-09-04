\ignore{
\begin{code}
module Core where

open import Data.Nat
open import Data.List
open import Data.Product

data RegType : Set
data Type : Set
DataStackType : Set
CallStackType : Set

RegFileTypes = List RegType
HeapTypes = List Type
DataStackType = List RegType
CallStackType = List (RegFileTypes × DataStackType)
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

\labeledfigure{fig:types}{Supported data types}{
\begin{code}
data RegType
  where
  _*  : Type → RegType
  int : RegType

data Type
  where
  atom : RegType → Type
  code : RegFileTypes
       → DataStackType → CallStackType
       → Type
\end{code}
}
