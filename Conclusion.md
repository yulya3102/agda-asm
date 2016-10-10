# Conclusion and future work

\iftoggle{russian-draft}{
В этой статье формализована на Agda простая модель динамической линковки,
описывающая изменения кода программ и библиотек, производимые линкером. В
этой формализации определены основные свойства динамического
линковщика:
}{
This paper formalizes a simple model of dynamic linking in Agda. This model
describes how linker changes the code of programs and libraries during the
linking process. This formalization states following properties of the
dynamic linker:
}

\begin{itemize}
\tightlist
\item
\iftoggle{russian-draft}{
    Описано, как динамический линковщик меняет layout программы и какие
    элементы он в нее добавляет.
}{
    The dynamic linker changes layout of a program in a specific way, adding
    certain elements to it.
}
\item
\iftoggle{russian-draft}{
    Зная, по какому смещению в неслинкованном объектном файле располагался
    некоторый блок кода, динамический линковщик может сказать, где этот
    блок кода будет располагаться в динамически слинкованной библиотеке.
}{
    The dynamic linker knows where the code block will be stored in a
    linked object
    file by its offset in non-linked object file.
}
\item
\iftoggle{russian-draft}{
    Зная идентификатор функции (в данной простой реализации это
    просто смещение в объектном файле), динамический линкер может указать
    на соответствующие этой функции элементы GOT и PLT. Так как эта
    информация известна в link-time, становится
    возможным использовать их на этом этапе: заменять вызовы ``неизвестных''
    функций на вызовы известных блоков PLT, выполнять link-time
    оптимизации.
}{
    Given function identifier (which in this formalization is simply an
    offset in object file), the dynamic linker can get corresponding GOT
    and PLT elements. This
    information is available in link-time, therefore it can be used in a
    linking process: the linker can substitute calls to PLT blocks of
    ``unknown'' functions for calls to ``unknown'' functions themselves and
    perform link-time optimizations.
}
\item
\iftoggle{russian-draft}{
    Заранее известно, какой именно код динамический линковщик генерирует
    для каждой внешней функции, а значит, можно
    рассуждать про семантику этого кода.
}{
    The code of each PLT element is known in advance, so you can reason
    about its semantics.
}
\item
\iftoggle{russian-draft}{
    Корректность работы динамической линковки полагается на корректность
    работы динамического загрузчика, при этом явно формулируется,
    выполнение каких свойств требуется в рантайме.
}{
    The correctness of the dynamic linking relies on the correctness of the
    dynamic loader.  The dynamic linker can explicitly state which
    properties of the dynamic loader.
}
\item
\iftoggle{russian-draft}{
    Доказано, что динамическая линковка не меняет семантику программы.
}{
    The dynamic linking does not change program semantics.
}
\end{itemize}

\iftoggle{russian-draft}{
Эти формальные требования позволяют говорить о корректности выполненной
динамической линковки библиотек и могут служить основой для написания
формально верифицированных динамического линковщика и динамического
загрузчика.

Проведенные исследования могут иметь продолжение в следующих направлениях:
(1) формализация ABI ``ленивой'' линковки, используемой в современных
библиотеках формата ELF; (2) формализация процесса заполнения релокаций
динамическим загрузчиком и его свойств, как это сделано в \citep{cardelli};
(3) формализация разбора бинарных файлов, загрузки кода в память и
взаимодействия с операционной системой, требуемых для получения realistic
dynamic linker/loader.

Описанные результаты могут повлиять на дальнейшие исследования, связанные
с:
}{
These formal specifications allow reasoning about the correctness of the
dynamic linking and can be used as a basis for creating formally verified
dynamic linker and loader.

This research can be continued in the following directions: (1) the
formalization of ``lazy'' linking ABI, used in modern ELF libraries; (2) the
formalization of
filling relocations process and its properties, as done by
\citep{cardelli}; (3) the formalization of binary files parsing, memory
mapping and interaction with the operating system, required for completing
realistic dynamic linker/loader.

Results described in this paper can influence further research related
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
    Further work can have a significant impact on LTO, which to the best of
    my knowledge currently does not have any formal semantics.
    Moreover, it can form toolchain with CompCert, which can cover not only
    translation phase but also linking and related optimizations.
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
