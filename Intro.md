# Introduction

\iftoggle{russian-draft}{
Верификация программного обеспечения может быть трудной задачей, и потому
ей не всегда уделяют должное внимание. Тем не менее, для некоторого класса
программного обеспечения трудозатраты на верификацию могут оказаться
стоящими результата. Например, одним из таких классов являются инструменты
разработки (тулчейны), потому что, во-первых, ошибки в них труднонаходимы,
и во-вторых, тулчейны являются частоиспользуемым ПО, в том числе и в сферах
с высокой ценой ошибки.

В настоящее время ведутся работы по созданию верифицированных тулчейнов, но
пока человечество далеко от создания абсолютно надежного комплекса
инструментов разработки программ. Например, есть VeLLVM \citep{vellvm},
формализующий язык LLVM и производящий доказанно корректные оптимизации в
нем. Есть более близкий к реальным тулчейнам проект, компилятор языка C
CompCert \citep{compcert}, производящий оптимизации, доказанно сохраняющие
семантику програмы. Тем не менее, даже CompCert не покрывает сборку
программы целиком: он использует системный, не верифицированный, линковщик.

Может показаться, что линковщик является достаточно простой программой, в
которой трудно ошибиться. Возможно, так и было до тех пор, пока не начали
производить оптимизации на этапе линковки. Эти оптимизации усложняют логику
линковщика, и в итоге он перестает быть простой программой. Возможность
наличия ошибок в коде линковщика подтверждается практикой: недавно
проводилось исследование \citep{ltostress}, в котором делали стресс-тесты для
линковщиков, и в итоге было найдено огромное количество ошибок на этапе
оптимизаций во время линковки. Это показывает, что верификацией линковщиков
не стоит пренебрегать.

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
типизированный язык, поддерживающий высокоуровневые абстракции, таких как
переменные типов и кортежи. В этом направлении было сделано множество
работ, расширяющих язык TAL, покарывающих, например, работу со стеком (STAL)
\citep{stal}, практически настоящий язык ассемблера x86 (TALx86) \citep{talx86} и даже
раздельную компиляцию и работу с объектными файлами (MTAL) \citep{mtal}.
Последний из указанных языков семейства TAL, модульный язык ассемблера,
опирается на работу Luca Cardelli \citep{cardelli}, формализующую механизмы и
алгоритмы статической линковки для высокоуровневых языков. В работе,
описывающей MTAL, была описана статическая линковка различных объектных
файлов, но формализации механизмов динамической линковки, как и в Bedrock,
представлено не было.
}{
Software verification can be difficult and therefore neglected. However,
the complexity of verification may be worth the result for a certain range
of software. For example, development tools (toolchains) should be
verified, because errors in toolchains are especially hard to find.
Moreover, toolchains are commonly used even in those areas where the cost
of failure is extremely high.

Efforts are being made to develop verified toolchains, but it is still far
from creation of completely reliable development tools. For example, VeLLVM
\citep{vellvm} formalizes LLVM intermediate language and performes formally
correct optimizations. Another project, CompCert \citep{compcert}, is
closer to realistic toolchains: it's a compiler of the C language that
performs optimizations which are proven to preserve semantics of the
compiled program. However, even CompCert does not cover all steps of
compilation: it uses system linker, which is not verified.

Linker might seem to be quite simple program, and it's hard to make a
mistake in its code. Probably, it has been that way until link-time
optimizations appeared. These optimizations make program logic more
complex, making it possible to introduce a bug in linker's source code.
Recent research \citep{ltostress} proves it: stress-testing for linkers
revealed myriad of bugs during link-time optimizations (LTO) phase. It
shows that linker verification should not be neglected.

Linker is low-level program that works with object files containing machine
code. Therefore, to reason about it we need formalization of low-level
language close to machine code. Bedrock \citep{bedrock}, one of most
notable results in this area, is a Coq \citep{coq} library that allows to
write code using abstractions associated with assembly language. Within the
Bedrock project, support for linking with external libraries was
implemented \citep{bedrocklinkers}, but there were no formalizations of
widely used dynamic linking mechanisms.

There is also excellent formalization of assembly language — Typed Assembly
Language (TAL) \citep{tal}. It describes typed low-level language that
supports high-level abstractions such as type variables and tuples. This
language has variety of extensions, adding support of stack mechanisms
(STAL) \citep{stal}, realistic x86 assembly language (TALx86)
\citep{talx86} and even separate compilation and object files manipulation
(MTAL) \citep{mtal}. The last of aforementioned TAL extensions, modular
assembly language, is based on Luca Cardelli's work \citep{cardelli} that
formalizes mechanisms and algorithms of static linking for high-level
programming languages. MTAL describes static linking of separate object
files, but, same as Bedrock, it lacks formalizations of dynamic linking.
}

Для написания proof-carrying code используются современные proof
assistant-ы, опирающиеся на теорию типов и соответствие Карри-Говарда
[@sorensen2006lectures]. Среди них можно выделить Coq [@coq] и Agda [@agda]
как наиболее близкие к высокоуровневым языкам программирования общего
назначения.  Coq использовался в таких крупных работах, как доказательство
теоремы о четырех красках [@gonthier2008formal] и компилятор языка C с
доказанно корректными оптимизациями [@compcert], в то время как Agda
зачастую используется в работах, формализующих языки и их свойства
[@danielsson2006formalisation] [@hancock2013small] [@mcbridedjinn].

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
existing TAL tools are written in ML, and all proofs about TAL programs
appeared as appendixes in corresponding papers. This paper uses
Agda \citep{agda} formalization of abstract language that is close to
TALx86 and STAL. Using this language, this paper formalizes what elements
are appended to program code during dynamic linking process, introduces
definition of code blocks equivalence and proves that correct dynamic
loader implies equivalence of statically and dynamically linked functions.
}

\iftoggle{russian-draft}{
Эту работу можно считать первыми шагами в области формализации динамической
линковки, из чего впоследствии можно получить верифицированный линковщик,
использующий внутри себя некоторую математическую модель, позволяющую
говорить о корректности производимых линковщиком преобразований программы.

Исходный код, описываемый в данной статье, находится по адресу
}{
This work can be considered first steps in area of dynamic linking
formalization. It can eventually result in verified linker that allows to
reason about correctness of performed program transformations.

The sources used in this paper available at
}
\url{https://github.com/yulya3102/agda-asm}.
