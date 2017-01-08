# Introduction

\iftoggle{russian-draft}{
Верификация программного обеспечения может быть трудной задачей, и потому
ей не всегда уделяют должное внимание. Тем не менее, для некоторого класса
программного обеспечения трудозатраты на верификацию могут оказаться
стоящими результата. Например, одним из таких классов являются инструменты
разработки (тулчейны), потому что, во-первых, ошибки в них труднонаходимы,
и во-вторых, тулчейны являются частоиспользуемым ПО, в том числе и в сферах
с высокой ценой ошибки.
}{
Software verification can be difficult and therefore neglected. Despite the
complexity of the task, it is worth verifying a certain range of software such
as development tools (toolchains), because errors in toolchains are
especially hard to find.
Moreover, toolchains are commonly used even in those areas where the cost
of failure is extremely high such as avionics or nuclear reactor control
systems.
}

\iftoggle{russian-draft}{
Разные группы исследователей работают над созданием верифицированных тулчейнов, но
пока человечество далеко от создания абсолютно надежного комплекса
инструментов разработки программ. Например, есть VeLLVM \citep{vellvm},
формализующий язык LLVM и производящий доказанно корректные оптимизации в
нем. Есть более близкий к реальным тулчейнам проект, компилятор языка C
CompCert \citep{compcert}, производящий оптимизации, доказанно сохраняющие
семантику програмы. Тем не менее, даже CompCert не покрывает сборку
программы целиком: он использует системный, не верифицированный, линковщик.
}{
Different groups of researchers try to develop verified toolchains, but it is still far
from completely reliable development tools. For example, VeLLVM
\citep{vellvm} formalizes LLVM intermediate language and performs formally
correct optimizations. Another project, CompCert \citep{compcert}, is
closer to realistic toolchains: it is a compiler of the C language that
performs optimizations which are proven to preserve the semantics of the
compiled program. However, even CompCert does not cover all steps of
compilation: for example, it uses a system linker which is not verified.
}

\iftoggle{russian-draft}{
Может показаться, что линковщик является достаточно простой программой, в
которой трудно ошибиться. Возможно, так и было до тех пор, пока не начали
производить оптимизации на этапе линковки. Эти оптимизации усложняют логику
линковщика, и в итоге он перестает быть простой программой. Возможность
наличия ошибок в коде линковщика подтверждается практикой: недавно
проводилось исследование \citep{ltostress}, в котором делали стресс-тесты для
линковщиков, и в итоге было найдено огромное количество ошибок на этапе
оптимизаций во время линковки. Это показывает, что верификацией линковщиков
не стоит пренебрегать.
}{
The linker might seem to be quite a simple program and it is hard to make a
mistake in its code. Probably, it has been that way until link-time
optimizations appeared. These optimizations make program logic more
complex, making it possible to introduce a bug in linker's source code.
Recent research proves it: stress-testing for linkers revealed a myriad of
bugs during link-time optimizations (LTO) phase \citep{ltostress}. It
shows that linker verification should not be neglected.
}

\iftoggle{russian-draft}{
Линковщик — достаточно низкоуровневая программа, которая работает с
скомпилированными в машинный код объектными файлами, а значит, для
рассуждений про него необходима формализация низкоуровнего языка, очень
близкого к машинному коду. Одной из заметных работ в этой области является
Bedrock \citep{bedrock}, являющийся библиотекой на Coq \citep{coq},
позволяющей оперировать абстракциями, ассоциированными с языком ассемблера,
и писать код в рамках этих абстракций. В рамках проекта Bedrock была
реализована поддержка линковки с внешними библиотеками \citep{bedrocklinkers},
но не было формализовано механизмов динамической линковки, широко
используемой в настоящее время.

Так же существует отличная формализация ассемблера — Typed Assembly
Language (TAL) \citep{tal}, описывающая некоторый низкоуровневый язык как
типизированный язык, поддерживающий высокоуровневые абстракции, такие как
переменные типов и кортежи. В этом направлении было сделано множество
работ, расширяющих язык TAL, покрывающих, например, работу со стеком (STAL)
\citep{stal}, практически настоящий язык ассемблера x86 (TALx86) \citep{talx86} и даже
раздельную компиляцию и работу с объектными файлами (MTAL) \citep{mtal}.
Последний из указанных языков семейства TAL, модульный язык ассемблера,
опирается на работу Luca Cardelli \citep{cardelli}, формализующую механизмы и
алгоритмы статической линковки для высокоуровневых языков. В работе,
описывающей MTAL, была описана статическая линковка различных объектных
файлов, но формализации механизмов динамической линковки, как и в Bedrock,
представлено не было.
}{
The linker is a low-level program that works with object files containing machine
code. Therefore, to reason about it, we need a formalization of a low-level
language that uses abstractions associated with the machine code, like
registers and stack. Bedrock \citep{bedrock}, one of the most
notable results in this area, is a Coq \citep{coq} library that allows
writing code using abstractions associated with assembly language. Within the
Bedrock project, support for linking with external libraries was
implemented \citep{bedrocklinkers}, but no formalizations of widely used
dynamic linking mechanisms were presented.

There also exists an excellent formalization of assembly language — Typed Assembly
Language (TAL) \citep{tal}. It describes low-level language with the static
type system that
supports high-level abstractions such as type variables and tuples. This
language has a variety of extensions that provide support for stack mechanisms
(STAL) \citep{stal}, realistic x86 assembly language (TALx86)
\citep{talx86} and even separate compilation and object files manipulation
(MTAL) \citep{mtal}. The latter, modular
assembly language, is based on Luca Cardelli's work \citep{cardelli} in
which mechanisms and algorithms of static linking for high-level
programming languages were formalized. MTAL describes static linking of
separate object
files, but as in Bedrock, it lacks dynamic linking formalizations.
}

\iftoggle{russian-draft}{
Для написания proof-carrying code используются современные proof
assistant-ы, опирающиеся на теорию типов и соответствие Карри-Говарда
\citep{sorensen2006lectures}. Среди них можно выделить Coq \citep{coq} и
Agda \citep{agda}
как наиболее близкие к высокоуровневым языкам программирования общего
назначения.  Coq использовался в таких крупных работах, как доказательство
теоремы о четырех красках \citep{gonthier2008formal} и компилятор языка C с
доказанно корректными оптимизациями \citep{compcert}, в то время как Agda
зачастую используется в работах, формализующих языки и их свойства
\citep{danielsson2006formalisation} \citep{hancock2013small}
\citep{mcbridedjinn}.
}{
Proof-carrying code is written with modern proof assistants which are
based on type theory and Curry-Howard correspondence
\citep{sorensen2006lectures}. Coq \citep{coq} and Agda \citep{agda} may be
noted as the closest to general purpose programming languages. Coq was used
to get significant results such as four color theorem proof
\citep{gonthier2008formal} and compiler of the C language that performs
formally correct optimizations \citep{compcert}. On the other hand, Agda is
used to formalize languages and their properties
\citep{danielsson2006formalisation} \citep{hancock2013small}
\citep{mcbridedjinn}.
}

\iftoggle{russian-draft}{
TAL является хорошей моделью для рассуждений про исполнение низкоуровневого
кода, но, к сожалению, существующие утилиты, реализуюущие работу с TAL,
написаны на ML, а все доказательства про работу программ на TAL приводились
в виде приложений в соответствующих статьях. В этой статье используется
формализация на Agda \citep{agda} абстрактного языка, близкого к TALx86 и STAL.
В рамках этого языка определяется, какие элементы добавляются в программу в
процессе динамической линковки, вводится понятие эквивалентности различных
блоков кода и доказывается, что при правильно работающем динамическом
загрузчике статически и динамически слинкованные функции оказываются
эквивалентными.
}{
TAL is a great model for reasoning about execution of low-level code, but
existing TAL tools are written in ML and all proofs about TAL programs
appear in appendixes of the corresponding papers. This paper uses
Agda \citep{agda} formalization of abstract language that is close to
TALx86 and STAL. We formalize what elements are appended to program code
during the dynamic linking process, introduce definition of code blocks
equivalence and prove that correct dynamic
loader implies the equivalence of statically and dynamically linked functions.
}

\iftoggle{russian-draft}{
Эту работу можно считать первыми шагами в области формализации динамической
линковки, из чего впоследствии можно получить верифицированный линковщик,
использующий внутри себя некоторую математическую модель, позволяющую
говорить о корректности производимых линковщиком преобразований программы.

Исходный код, описываемый в данной статье, находится по адресу
}{
This work can be considered as a first step in the area of dynamic linking
formalization. It can eventually result in verified linker that allows to
reason about the correctness of performed program transformations.

The source codes used in this paper are available at
}
\url{https://github.com/yulya3102/agda-asm}.
