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
инструментов разработки программ. Например,
существует несколько верифицированных компиляторов: CompCert
\citep{compcert} -- компилятор языка C, доказывающий сохранение семантики
при оптимизациях, CerCo \citep{cerco} -- компилятор языка C, доказывающий
сохранение вычислительной сложности программы, и CakeML \citep{cakeml} --
верифицированная имплементация ML. Кроме того, существует несколько работ,
не являющихся полноценными компиляторами, но тоже стоящих упоминания:
VeLLVM \citep{vellvm}
формализует язык LLVM и производит доказанно корректные оптимизации в
нем, а BedRock \citep{bedrock} позволяет писать на Coq \citep{coq},
оперируя абстракциями, ассоциированными с языком ассемблера.
}{
Different groups of researchers try to develop verified toolchains, but it is still far
from completely reliable development tools. For example,
CompCert \citep{compcert} is a compiler of the C language which proves to
preserve program semantics after optimizations. Another compiler of the C
language, CerCo \citep{cerco}, proves to preserve the complexity of the
program. Not only compilers of the C language are verified: CakeML
\citep{cakeml} is a verified implementation of ML, both compiler and
runtime. Aside from that, there are several non-compiler projects worth noting:
VeLLVM
\citep{vellvm} formalizes LLVM intermediate language and performs formally
correct optimizations, and Bedrock \citep{bedrock} allows to write
verified code in Coq \citep{Coq} using low-level abstractions such as stack
and registers.
}

\iftoggle{russian-draft}{
Но нужно ли верифицировать линковку? Линковщик занимается подстановкой
символов и может таким образом влиять на семантику программы. Значит, если
верифицированный компилятор полагается на не-верифицированный линковщик,
семантика результирующей программы может быть нарушена. В этом случае
полагаться на теоремы, предоставляемые верифицированным компилятором, стоит
с большой осторожностью.
Возможность
наличия некорректного кода в линковщике подтверждается практикой: недавно
проводилось исследование \citep{ltostress}, в котором делали стресс-тесты для
линковщиков, и в итоге было найдено огромное количество ошибок на этапе
оптимизаций во время линковки.
}{
But should we verify linkers? Linker does a lot of things aside from symbol
substitution, but even with only symbol substitution it can affect program
semantics. That is to say, if the verified compiler relies on non-verified
linker, the semantics of the program can be broken. In this case, the user
should rely on theorems provided by the compiler with great caution.
Recent research proves that linkers can break program semantics:
stress-testing for linkers revealed a myriad of
bugs during link-time optimizations (LTO) phase \citep{ltostress}.
}
\iftoggle{russian-draft}{
Кроме того, линковка сама по себе может служить источником уязвимостей.
Например, Thompson в известной Turing Award Speech \citep{thompson}
указывает, что целью подобной атаки может быть любая программа,
манипулирующая другими программами, в том числе и линковщик. Недавнее
исследование семантики динамической загрузки \citep{weirdmachines}
показывает, что в качестве средства атаки могут быть использованы даже
метаданные объектных файлов, обрабатываемые динамическим загрузчиком. That
is to say, линковка является не менее серьезной и небезопасной операцией,
что и компиляция.
Это показывает, что верификацией линковщиков
не стоит пренебрегать.
}{
Aside from that, the linking can be the source of vulnerability by itself.
For example, well-known Thompson's Turing Award speech \citep{thompson}
notes that any program that manipulates other programs can be the target of
a similar attack. Another example, recent research on dynamic linking in
\citep{weirdmachines} shows that attack can be orchestrated even by the
metadata of object files which are handled by the dynamic loader. That is
to say, the linking is no less serious and unsafe than the compilation
itself.
It
shows that linker verification should not be neglected.
}

\iftoggle{russian-draft}{
В связи с отсутствием верифицированного линковщика верифицированные
компиляторы вынуждены либо ограничивать поддержку до только одномодульных
программ (как это делают CerCo и CakeML), либо полностью или частично
полагаться на системный линковщик, возможно, с последующей проверкой
результата (как это делает CompCert без недавних расширений). Тем не менее,
попытки расширить верифицированную компиляцию и включить в нее линковку уже
предпринимались. Так, в CompCert сторонним расширением была добавлена
поддержка language-independent linking \citep{CompCompCert}. К сожалению,
это расширение требовало серьезных изменений в основной кодовой базе
CompCert. По этой причине было реализовано еще одно, менее heavyweight,
расширение CompCert, поддерживающее раздельную компиляцию только для одного компилятора
\citep{Lightweightverif}. Кроме CompCert и его расширений, раздельная
компиляция была так же заявлена в \citep{bedrocklinkers}, где реализовали
compositional компилятор из Cito, идеализированного C-подобного языка, в
Bedrock. Что касается линковки без привязки к конкретным языкам, недавно
была формализована \citep{elfsemantic} спецификация формата ELF (Executable
and Linkable format), наиболее распространенного среди UNIX-like систем, с
формализацией статической линковки файлов этого формата.
}{
Due to the lack of the verified linker, verified compilers are compelled to
either restrict acceptable input to single-module programs as CerCo and
CakeML do, or rely on the non-verified linker with possibly subsequent
sanity check as CompCert does. However, there were several attempts to
extend verified compilation and to include verified linking. Compositional
CompCert \citep{CompCompCert}, a third-party extension to CompCert, added
support for language-independent linking. Unfortunately, this extension
required significant changes to the main CompCert code. For that reason,
SepCompCert \citep{lightweightverif}, another third-party extension of
CompCert, was developed. It is much more lightweight compared to
Compositional CompCert, but it supports separate compilation only for one
compiler. Aside from CompCert and its extensions, the Bedrock project
implemented a compositional compiler from idealistic C-like language
into Bedrock language which supports separate compilation
\citep{bedrocklinkers}. As for the linking itself not being tied to
specific language, recent research formalized \citep{elfsemantic} ELF
(Executable and Linkable Format) specification and static linking within
it.
}

\iftoggle{russian-draft}{
Что касается формализации механизмов динамической линковки, ни в одной из
указанных выше работ они не были представлены. Тем не менее, в формализации
формата ELF \citep{elfsemantic} было указано, что формализовать основные для динамической
линковки механизмы GOT и PLT (их мы детально обсудим в секции
\ref{sec:background}) как часть спецификации ELF несложно, в то время как
их роль в процессе динамической загрузки требует куда больших усилий. В
нашей работе мы рассматриваем, как эти механизмы обеспечивают правильную
работу программы в рантайме.
}{
As for formalization of dynamic linking mechanisms, they were not presented
in projects mentioned above. However, in the ELF formalization
\citep{elfsemantic} it was noted that formalization of GOT and PLT (which
we will discuss in details in section \ref{sec:background}) as part of ELF
specification is rather simple, while formalization of their role in the
dynamic linking process requires much more effort. In contrast, in this
paper we formalize how these mechanisms ensure correct execution of the
program in runtime.
}

\iftoggle{russian-draft}{
Линковщик — достаточно низкоуровневая программа, которая работает с
скомпилированными в машинный код объектными файлами, а значит, для
рассуждений про него необходима формализация низкоуровнего языка, очень
близкого к машинному коду.
}{
The linker is a low-level program that works with object files containing machine
code. Therefore, to reason about it, we need a formalization of a low-level
language that uses abstractions associated with the machine code, like
registers and stack.
}

\iftoggle{russian-draft}{
Помимо указанного выше Bedrock,
существует формализация ассемблера — Typed Assembly
Language (TAL) \citep{tal}, описывающая некоторый низкоуровневый язык как
типизированный язык, поддерживающий высокоуровневые абстракции, такие как
переменные типов и кортежи. В этом направлении было сделано множество
работ, расширяющих язык TAL, покрывающих, например, работу со стеком (STAL)
\citep{stal}, практически настоящий язык ассемблера x86 (TALx86) \citep{talx86} и даже
раздельную компиляцию и работу с объектными файлами (MTAL) \citep{mtal}.
Последний из указанных языков семейства TAL, модульный язык ассемблера,
опирается на работу Luca Cardelli \citep{cardelli}, формализующую механизмы и
алгоритмы статической линковки для высокоуровневых языков. В \citep{mtal}
была описана статическая линковка различных объектных
файлов, но формализации механизмов динамической линковки, как и в
приведенных выше работах, представлено не было.
}{
Aside from the Bedrock which was already mentioned,
there also exists a formalization of assembly language — Typed Assembly
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
files, but as all of above, it lacks dynamic linking formalizations.
}

\iftoggle{russian-draft}{
TAL, как формальная система, выглядит наиболее интересным для доказательств
свойств кода на языке ассемблера.
К сожалению, существующие утилиты, реализуюущие работу с TAL,
написаны на ML, а все доказательства про работу программ на TAL приводились
в виде приложений в соответствующих статьях. В этой статье используется
формализация на Agda \citep{agda} абстрактного языка, близкого к TALx86 и STAL.
В рамках этого языка определяется, какие элементы добавляются в программу в
процессе динамической линковки, вводится понятие эквивалентности различных
блоков кода и доказывается, что при правильно работающем динамическом
загрузчике статически и динамически слинкованные функции оказываются
эквивалентными.
}{
As a formal system, TAL looks the most interesting to be used in proofs
of assembly code properties.
Existing TAL tools are written in ML and all proofs about TAL programs
appear in appendices of the corresponding papers. This paper uses
Agda \citep{agda} formalization of abstract language that is close to
TALx86 and STAL. We formalize what elements are appended to program code
during the dynamic linking process, introduce definition of code blocks
equivalence and prove that correct dynamic
loader implies the equivalence of statically and dynamically linked functions.
}

\iftoggle{russian-draft}{
Эту работу можно считать первыми шагами в области формализации динамической
линковки.
Дополнив впоследствии данную работу реализацией маппинга объектных файлов в
память и заполнением нужных ячеек GOT, можно получить модель простейшего
динамического загрузчика, для которого доказано сохранение семантики
программы.
}{
This work can be considered as a first step in the area of dynamic linking
formalization.
By adding formalizations of memory mapping and filling GOT elements, this
formalization can be extended to the model of simple dynamic loader which
is proven to preserve program semantics.
}
\iftoggle{russian-draft}{
Из этого впоследствии можно получить верифицированный realistic линковщик,
использующий внутри себя некоторую математическую модель, позволяющую
говорить о корректности производимых линковщиком преобразований программы.
}{
It can eventually result in verified realistic linker that allows to
reason about the correctness of performed program transformations.
}

\iftoggle{russian-draft}{
Исходный код, описываемый в данной статье, находится по адресу
}{
The source codes used in this paper are available at
}
\url{https://github.com/yulya3102/agda-asm}.
