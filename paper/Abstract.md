\iftoggle{russian-draft}{
К настоящему моменту уже не приходится сомневаться в возможности
верификации низкоуровневого и системного программного обеспечения, в
частности, инструментов разработки. Возможно писать низкоуровневый код и
автоматически доказывать его свойства с использованием современных
пруфчекеров, что важно при написании, например, runtime-систем языков.
К примеру, для языка C, нативного для множества платформ, существует
компилятор CompCert, предоставляющий доказательства корректности
производимых оптимизаций.

Имеющиеся системы направлены на верификацию этапа трансляции, но сборка
программ из исходного кода не ограничивается только этим этапом. Недавние
исследования показывают, что множество ошибок происходит на этапе link-time
optimizations (LTO), который тоже необходимо верифицировать.
}{
It is no doubt that nowadays it is possible to verify low-level or system
software. In particular, we can write low-level code and prove its
properties with modern proof assistants. This can be important especially
in the development of runtime systems. For example, for C, the native
language of different platforms, there is CompCert, a compiler that proves
the correctness of performed optimizations.

Existing compilation verification systems are restricted to translation
phase, but compilation also contains few more steps. Recent research shows that
a lot of errors occur during link-time optimizations phase which also
needs verification.
}

\iftoggle{russian-draft}{
В данной работе представлена формализация простой модели процесса
линковки, который делится на две части: до запуска программы и в рантайме.
Формализация первого этапа включает в себя описание преобразований,
производимых над объектным фалом, а формализация второго этапа включает в
себя описание инвариантов, обеспечиваемых динамическим загрузчиком в
рантайме. Кроме того, показано, что при соблюдении описанного контракта
семантика вызова динамически слинкованной функции не отличается от
семантики вызова этой же функции, слинкованной статически.

Эта работа является основой для дальнейших исследований, направленных на
создание верифицированных динамического загрузчика и динамического
линковщика, позволяющих делать корректные оптимизации на этапе линковки.
}{
This paper presents a formalization of a simple model of linking mechanisms.
Dynamic linking can be divided into two phases: pre-runtime and runtime.
The formalization of the first phase includes the description of
performed program transformations and the formalization of the second phase
contains invariants provided by the dynamic loader in runtime. Moreover,
this paper shows that if these conditions are satisfied, then the semantics of a
dynamically-linked function call is the same as the semantics of a
statically-linked function call.

This paper forms the basis for further research aimed at the creation of a
verified dynamic linker and loader allowing to correctly perform
link-time optimizations.
}
