# Linking primer
\label{sec:background}

\iftoggle{russian-draft}{
Данная работa формализует упрощенный вариант динамической линковки,
используемой в файлах ELF и описанной в \citep{dsohowto} и \citep{levine}.
Перед тем, как описывать используемую формализацию, познакомим читателя с
базовыми понятиями динамической линковки.
}{
This paper formalizes a simplified version of the dynamic linking process
that is used in ELF files and described in \citep{dsohowto} and
\citep{levine}.
Before describing the formalization used in this paper, we shall introduce
the reader to the basic terms of the dynamic linking.
}

\iftoggle{russian-draft}{
Внутри исходного кода функции используются по их символическим именам,
которые при компиляции заменяются соответствующими адресами \emph{символов}
объектного файла. Ссылки на внешние функции, не определенные в объектном
файле, остаются незаполненными и должны быть заполнены линкером. Эти
незаполненные ссылки на внешние символы называются \emph{релокациями}. Более
подробно об этих терминах можно прочитать в \citep{levine}.

Динамическую линковку можно поделить на два этапа. Первый из них происходит
до запуска программы и заключается в подготовке объектного файла к
линковке в рантайме. Во время этого этапа в объектный файл добавляются
дополнительные секции и метаинформация, обеспечивающие правильное
исполнение программы. Второй этап заключается в заполнении релокаций
в рантайме динамическим загрузчиком.
}{
In the source code function are used by their symbolic names which are
substituted with addresses of corresponding \emph{symbols} during
compilation. References to external functions are left empty and should be
filled by the linker. These empty references to external functions are called
\emph{relocations}. More details about these terms can be found in
\citep{levine}.

Dynamic linking can be split into two steps. The first of them takes place
before runtime and consists of preparing the object file for the act of
dynamic linking. During this step, the object file is extended with several
sections and metadata which ensure correct execution of the program. The
second step is the act of dynamic linking itself which consists of dynamic
loader filling relocations in runtime.
}

\iftoggle{russian-draft}{
Ниже мы рассмотрим, какие секции добавляются в объектный файл.
Среди них нас более всего интересуют секции GOT
(Global Offset Table) и PLT (Procedure Linkage Table), непосредственно
участвующие в вызове внешних функций.
}{
We discuss the details of the new object file sections below.
The GOT (Global Offset Table) and PLT (Procedure Linkage Table) are the most interesting for us among them, as they are directly involved in the external function calls.
}
\iftoggle{russian-draft}{
В секции GOT
на каждую внешнюю функцию $f$ генерируется статическая
ячейка памяти $got.f$. Эта секция должна заполняться в рантайме
динамическим загрузчиком.
После линковки в рантайме в ячейках GOT должны находиться адреса
соответствующих символов, загруженных динамическим загрузчиком.
}{
In GOT section for
every extern function $f$ variable $got.f$ is created in static memory. This
section should be filled in runtime by dynamic loader.
After the runtime linking, GOT elements should contain the addresses of
corresponding symbols which were loaded by dynamic loader.
}
\iftoggle{russian-draft}{
В секции PLT
на каждую внешнюю функцию $f$ генерируется процедура $plt.f$, а
релокации, ссылающиеся на $f$, заполняются адресом процедуры $plt.f$.
}{
In section PLT for every external function $f$ a procedure $plt.f$ is
generated and corresponding relocations are filled with $plt.f$
procedure address.
}
\iftoggle{russian-draft}{
Добавленные в секцию PLT процедуры $plt.f$ содержат в себе
код, позволяющий передать управление по адресу, находящемуся в
соответствующей ячейке GOT. В самом простом случае этот код представляет из
себя
}{
Procedures $plt.f$ added to the PLT section consist of
the code that allows continuing the execution by the address stored in
the corresponding GOT element. In the simplest case this code consists of
}
\iftoggle{russian-draft}{
единственную
инструкцию: indirect jump по указателю $got.f$. Если в $got.f$ находится
правильный адрес загруженной в память внешней функции $f$, то исполнение
процедуры $plt.f$ приведет к исполнению функции $f$.
В итоге динамически слинкованный объектный файл выглядит, как изображено на
Figure \ref{fig:objfile}.
}{
a single
instruction: indirect jump by the $got.f$ pointer. If the $got.f$ contains
the correct address of function $f$ loaded to memory, then the execution of the
$plt.f$ procedure will lead to the execution of the function $f$.
As a result, dynamically linked object file looks like shown in Figure
\ref{fig:objfile}.
}

\labeledfigure{fig:objfile}{Dynamically linked object file}{
\lstinputlisting[style=asm]{shared-object.asm}
}

\iftoggle{russian-draft}{
После такого преобразования для вызова внешней функции $f$ все еще
необходимо заполнить ячейку памяти $got.f$. Но это существенно
отличается от исходного неслинкованного объектного файла: заполнить
релокации исходного файла можно было только до запуска программы, в
то время как заполнить ячейку $got.f$ можно и в рантайме. В этом и
состоит важность инструкции indirect jump: она позволяет в рантайме менять
целевую точку инструкций перехода.
}{
After this transformation, there are still $got.f$ variables that need to
be filled. But this is significantly different from the original object
file which is unlinked: relocations could be filled only before running
program,
whereas $got.f$ variables can be filled in runtime. This is why indirect
jump instruction is so important: it allows to change the target point of jump
instructions in runtime.
}

\labeledfigure{fig:dynmem}{External function call in dynamically linked memory}{
\includegraphics[width=0.5\textwidth]{memory.jpg}
}

\iftoggle{russian-draft}{
После заполнения динамическим загрузчиком секции GOT вызов внешней функции
выглядит так, как изображено в \ref{fig:dynmem}. Сплошными стрелками
показана передача исполнения, а пунктирными стрелками показаны ссылки на
память.

При использовании дополнительного кода для вызова внешних функций встает
вопрос: как это влияет на семантику программы? Что происходит со стеком
вызовов и не происходит ли затирания значений в регистрах? Эти вопросы
становятся более актуальными, если используется динамическая линковка с
``ленивым связыванием'', при которой динамический загрузчик может
вызываться прямо из кода в PLT для загрузки отсутствующих библиотек.
}{
After the dynamic loader filled the GOT elements, the external function
call looks like shown in Figure \ref{fig:dynmem}. Bold arrows indicate
the transfer of execution, and the dashed arrows indicate memory
references.

When the additional code is used to call external functions, it is
reasonable to ask: how does it change program semantics? What happens to
the call stack and does this code erase values stored in registers? These
questions are becoming more relevant if the ``lazy binding'' is used,
during which the dynamic linker can be called to load missing libraries
right from the PLT code.
}

\iftoggle{russian-draft}{
В этой статье приведена формализация описанного варианта динамической
линковки, отвечающая на эти вопросы.
В этом упрощенном варианте динамической линковки поддерживается только
линковка внешних функций и не подерживаются
внешние переменные.
Линковка внешних переменных сопряжена с отдельными трудностями, связанными
с использованием релокаций копирования. Подробнее об этом можно прочитать в
\citep{levine}.
}{
This paper presents the formalization of the described version of the
dynamic linking and answers this questions.
In this simplified version of dynamic linking, we only support linking of
external functions and do not
support external variables.
There are difficulties with the linking of external variables caused by the use
of the copy relocations. More information on that can be found in
\citep{levine}.
}
