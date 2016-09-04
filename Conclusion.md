# Discussion

\iftoggle{russian-draft}{
В этой статье формализована на Agda простая модель динамической линковки,
описывающая изменения кода программ и библиотек, производимые линкером. В
этой формализации сформулированы основные свойства динамического
линковщика:
}{
This paper formalizes in Agda simple model of dynamic linking. This model
describes how linker changes code of programs and libraries during the
linking process. This formalization states following properties of dynamic
linker:
}

\begin{itemize}
\tightlist
\item
\iftoggle{russian-draft}{
    Описано, как динамический линковщик меняет layout программы и какие
    элементы он в нее добавляет (функция \F{pltize}).
}{
    Dynamic linker changes layout of program in a specific way, adding
    certain elements to it (as described by function \F{pltize})
}
\item
\iftoggle{russian-draft}{
    Зная, по какому смещению в неслинкованном объектном файле располагался
    некоторый блок кода, динамический линковщик может сказать, где этот
    блок кода будет располагаться в динамически слинкованной библиотеке
    (функция \F{func}).
}{
    Dynamic linker knows where code block will be stored in linked object
    file by its offset in non-linked object file (as shown by function
    \F{func}).
}
\item
\iftoggle{russian-draft}{
    Зная идентификатор функции (в данной простой реализации это
    просто смещение в объектном файле), динамический линкер может указать
    на соответствующие этой функции элементы GOT и PLT (функции \F{got} и
    \F{plt}). Так как эта информация известна в link-time, становится
    возможным использовать их на этом этапе: заменять вызовы "неизвестных"
    функций на вызовы известных блоков PLT, выполнять link-time
    оптимизации.
}{
    Given function identificator (which in this formalization is simply
    offset in object file), dynamic linker can get corresponding GOT and
    PLT elements (as shown by functions \F{got} and \F{plt}). This
    information is available in link-time, therefore it can be used in
    linking process: linker can substitute "unknown" funciton calls with
    calls to their PLT blocks and perform link-time optimizations.
}
\item
\iftoggle{russian-draft}{
    Заранее известно, какой именно код динамический линковщик генерирует
    для каждой внешней функции (функция \F{plt-stub}), а значит, можно
    рассуждать про семантику этого кода.
}{
    Code of each PLT element if known in advance (it is shown in function
    \F{plt-stub}), so you can reason about its semantics.
}
\item
\iftoggle{russian-draft}{
    Корректность работы динамической линковки полагается на корректность
    работы динамического загрузчика, при этом явно формулируется,
    выполнение каких свойств требуется в рантайме (функции \F{GOT[ f
    ]-correctness}, \F{PLT[ f ]-correctness})
}{
    Correctness of dynamic linking relies on correctness of dynamic loader.
    Dynamic linker can explicitly state which properties of dynamic loader
    it needs (functions \F{GOT[ f ]-correctness} and \F{PLT[ f
    ]-correctness}).
}
\item
\iftoggle{russian-draft}{
    Доказано, что динамическая линковка не меняет семантику программы.
}{
    Dynamic linking does not change program semantics.
}
\end{itemize}

\iftoggle{russian-draft}{
Эти формальные требования позволяют говорить о корректности выполненной
динамической линковки библиотек и могут служить основой для написания
формально верифицированных динамического линковщика и динамического
загрузчика.

Проведенные исследования могут иметь продолжение в следующих направлениях:
(1) формализация ABI "ленивой" линковки, исползуемой в современных
библиотеках формата ELF; (2) формализация процесса заполнения релокаций
динамическим загрузчиком и его свойств, как это сделано в \citep{cardelli};
(3) формализация разбора бинарных файлов, загрузки кода в память и
взаимодействия с операционной системой, требуемых для получения realistic
dynamic linker/loader.

Описанные результаты могут повлиять на дальнейшие исследования, связанные
с:
}{
These formal specification allows to reason about correctness of dynamic
linking and can be used as basis for creating of formally verified dynamic
linker and dynamic loader.

This research can be continued in following directions: (1) formalization
of "lazy" linking ABI, used in modern ELF libraries; (2) formallization of
filling relocations process and its properties, as done by
\citep{cardelli}; (3) formallization of binary files parsing, memory
mapping and interaction with operating system, required for completing
realistic dynamic linker/loader.

Results described in this paper can influence on further research related
to:
}

\begin{itemize}
\tightlist
\item
    \textbf{\emph{Link-time optimizations}}.

\iftoggle{russian-draft}{
    Продложение этой работы может существенно повлиять на LTO, для которого
    формально описанная семантика в литературе не встречается.
    Кроме того, это позволило бы построить тулчейн с CompCert, покрывающий
    гарантиями не только трансляцию кода, но и линковку и связанные с ней
    оптимизации.
}{
    Further work can have a significant imact on LTO, which is currently
    to the best of my knowledge doesn't have any formal semantics.
    Moreover, it can form toolchain with CompCert, which can cover not only
    translation phase, but linking and related optimizations.
}
\item
    \textbf{\emph{Typed Assembly Language}}.

\iftoggle{russian-draft}{
    Одно из расширений TAL, описанное в \citep{mtal}, формализует типобезопасную
    статическую линковку. Продолжение данной работы могло бы расширить TAL еще
    сильнее, добавив формализацию типобезопасной динамической линковки.
}{
    One of TAL extensions, described in \citep{mtal}, formalizes type-safe
    static linking. Further work can extend TAL even more, adding
    formalization of type-safe dynamic linking.
}
\end{itemize}
