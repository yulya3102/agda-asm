# Linking primer

\iftoggle{russian-draft}{
Данная работa формализует упрощенный вариант динамической линковки,
используемой в файлах ELF и описанной в \citep{dsohowto} и \citep{levine}.
}{
This paper formalizes a simplified version of the dynamic linking process
that is used in ELF files and described in \citep{dsohowto} and
\citep{levine}.
}
Перед тем, как описывать используемую формализацию, познакомим читателя с
базовыми понятиями динамической линковки.

Внутри исходного кода функции используются по их символическим именам,
которые при компиляции заменяются соответствующими адресами ***символов***
объектного файла. Ссылки на внешние функции, не определенные в объектном
файле, остаются незаполненными и должны быть заполнены линкером. Эти
незаполненные ссылки на внешние символы называются ***релокациями***. Более
подробно об этих терминах можно прочитать в [@levine].

Динамическую линковку можно поделить на два этапа. Первый из них происходит
до запуска программы и заключается в подготовке объектного файла к
линковке в рантайме. Во время этого этапа в объектный файл добавляются
дополнительные секции и метаинформация, обеспечивающие правильное
исполнение программы. Второй этап заключается в заполнении релокаций
в рантайме динамическим загрузчиком.

\iftoggle{russian-draft}{
Ниже мы рассмотрим, какие секции добавляются в объектный файл.
}{
We discuss the details of the new object file sections below.
}
Среди них нас более всего интересуют секции GOT
(Global Offset Table) и PLT (Procedure Linkage Table), непосредственно
участвующие в вызове внешних функций.
\iftoggle{russian-draft}{
В секции GOT
на каждую внешнюю функцию $f$ генерируется статическая
ячейка памяти $got.f$. Эта секция должна заполняться в рантайме
динамическим загрузчиком.
}{
In GOT section for
every extern function $f$ variable $got.f$ is created in static memory. This
section should be filled in runtime by dynamic loader.
}
После линковки в рантайме в ячейках GOT должны находиться адреса
соответствующих символов, загруженных динамическим загрузчиком.
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
}{
Procedures $plt.f$ added to the PLT section consist of
}
код, позволяющий передать управление по адресу, находящемуся в
соответствующей ячейке GOT. В самом простом случае этот код представляет из
себя
\iftoggle{russian-draft}{
единственную
инструкцию: indirect jump по указателю $got.f$. Если в $got.f$ находится
правильный адрес загруженной в память внешней функции $f$, то исполнение
процедуры $plt.f$ приведет к исполнению функции $f$.
}{
a single
instruction: indirect jump by the $got.f$ pointer. If the $got.f$ contains
correct address of function $f$ loaded to memory, then the execution of the
$plt.f$ procedure will lead to the execution of the function $f$.
}
В итоге динамически слинкованный объектный файл выглядит, как изображено на
Figure \ref{fig:objfile}.

\labeledfigure{fig:objfile}{Dynamically linked object file}{
\includegraphics[width=0.5\textwidth]{objfile.jpg}
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

В этой статье приведена формализация описанного варианта динамической
линковки, отвечающая на эти вопросы.
\iftoggle{russian-draft}{
В этом упрощенном варианте динамической линковки поддерживается только
линковка внешних функций и не подерживаются
внешние переменные.
}{
In this simplified version of dynamic linking, we only support linking of
external functions and do not
support external variables.
}
Линковка внешних переменных сопряжена с отдельными трудностями, связанными
с использованием релокаций копирования. Подробнее об этом можно прочитать в
[@levine].
