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

В данной работе представлена формализация простой модели процесса
линковки, который делится на две части: динамическая линковка и
динамическая загрузка. Формализация динамического линковщика включает в
себя описание производимых им преобразований, а формализация динамического
загрузчика включает в себя описание инвариантов, обеспечиваемых им в
рантайме. Кроме того, показано, что при соблюдении описанного контракта
семантика вызова динамически слинкованной функции не отличается от
семантики вызова этой же функции, слинкованной статически.

Эта работа является основой для дальнейших исследований, направленных на
создание верифицированных динамического загрузчика и динамического
линковщика, позволяющих делать корректные оптимизации на этапе линковки.
}{
Nowadays there is no doubt it is possible to verify low-level and system
software. In particular, we can write low-level code and prove its
properties with modern proof assistants. This can be important especially
in development of runtime systems. For example, for C, the native language
of plenty of platforms, there
is CompCert, a compiler that proves correctness of performed optimizations.

Existing compilation verification systems are directed at translation
phase, but compilation contains few more steps. Recent research shows that
a lot of errors occur during link-time optimizations phase which also
needs verification.

This paper presents formalization of a simple model of a linking mechanisms.
Dynamic linking is performed by two tools: a dynamic linker and a dynamic
loader. The formalization of the dynamic linker includes description of
performed program transformations and formalization of the dynamic loader
contains invariants provided by the dynamic loader in runtime. Moreover,
this paper shows that if these conditions are met, then semantics of
dynamically-linked function call is the same as semantics of
statically-linked function
call.

This paper forms the basis for further research aimed at creation of a
verified dynamic linker and loader allowing to perform correct
link-time optimizations.
}
