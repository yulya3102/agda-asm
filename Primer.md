# Linking primer

\iftoggle{russian-draft}{
Данная работa формализует упрощенный вариант динамической линковки,
используемой в файлах ELF и описанной в \citep{dsohowto}. В этом упрощенном
варианте поддерживается только линковка внешних функций и не подерживаются
внешние переменные.
}{
This paper formalizes a simplified version of the dynamic linking process
that is used in ELF files and described in \citep{dsohowto}. In this
simplified version we only support linking of external functions and do not
support exernal variables.
}

\iftoggle{russian-draft}{
Динамическая линковка предполагает использование внешних символов из
библиотек без включения этих библиотек в объектный файл, как это было бы
при статической линковке. При этом динамическому линковщику необходимо
чем-то заполнить \emph{релокации} - "пустые" аргументы инструкций перехода на
внешние функции из объектного файла, и тем самым сделать их пригодными к
исполнению. Но динамический линковщик не может менять код
непосредственно в месте появления релокации. В противном случае последующий
код и объявленные внутри него символы сдвинутся относительно своей
предыдущей позиции, и инструкции, использующие эти символы с помощью
относительной адресации, станут невалидны. Чтобы этого не произошло,
динамический линковщик добавляет отдельную секцию для кода, которая
называется PLT (Procedure Linkage Table). В этой секции
на каждую внешнюю функцию $f$ он генерирует процедуру $plt.f$, а
релокации, ссылающиеся на $f$, заполняет адресом процедуры $plt.f$.
Таким образом, релокации внутри исходного объектного файла оказываются
заполненными, а относительная адресация остается валидной. Внутри
добавленной секции линкер уже может генерировать код, осуществляющий
вызов динамически слинкованной функции.
}{
Dynamic linking allows to use external symbols without including libraries
into the object file, as would be done in static linking. On the other
hand, dynamic linker needs to make object file usable by filling
\emph{relocations} - "empty" arguments of jumps to external functions. But
dynamic linker can't change any code in place where relocation appeared.
Otherwise, symbols that are placed in object file after that relocation
would shift from their original positions, invalidating any instruction,
referring to them with their relative address. To prevent this, dynamic
linker creates a section with code which is called PLT (Procedure Linkage
Table). In this section for every external function $f$ it generates a
procedure $plt.f$ and fills corresponding relocations with $plt.f$
procedure address. Thereby, it fills relocations and doesn't break relative
addresses. Inside the new section dynamic linker can generate any code that
is necessary to call dynamically linked function.
}

\iftoggle{russian-draft}{
Помимо секции PLT, динамический линковщик добавляет к объектному файлу еще
одну секцию, называаемую GOT (Global Offset Table). В этой секции
динамический линковщик на каждую внешнюю функцию $f$ генерирует статическую
ячейку памяти $got.f$. Эта секция должна заполняться в рантайме
динамическим загрузчиком.
}{
In addition to the PLT section, dynamic linker adds another section which
is called GOT (Global Offset Table). In this section dynamic linker for
every extern function $f$ creates variable $got.f$ in static memory. This
section should be filled in runtime by dynamic loader.
}

\iftoggle{russian-draft}{
Добавленные в секцию PLT процедуры $plt.f$ содержат в себе единственную
инструкцию: indirect jump по указателю $got.f$. Если в $got.f$ находится
правильный адрес загруженной в память внешней функции $f$, то исполнение
процедуры $plt.f$ приведет к исполнению функции $f$.
}{
Procedures $plt.f$ added to the PLT section consist of a single
instruction: indirect jump by the $got.f$ pointer. If the $got.f$ contain
correct address of function $f$ loaded to memory, then execution of the
$plt.f$ procedure will lead to execution of the function $f$.
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
After this transformation there still $got.f$ variables that need to be
filled. But this is significantly different from the original unlinked
object file: relocations could be filled only before running program,
whereas $got.f$ variables can be filled in runtime. This is why indirect
jump instruction is so important: it allows to change target point of jump
instructions in runtime.
}

\iftoggle{russian-draft}{
Динамический линковщик совершает подобное преобразование над объектными
файлами, и на этом его работа заканчивается. После этого в рантайме
динамический загрузчик заполняет секции GOT загруженных библиотек, и код
становится полностью пригодным для исполнения.
}{
Dynamic linker performs this transformation on the object files, and its
work ends on it. After that dynamic loader in runtime fills GOT sections of
loaded libraries, and code becomes suitable for execution.
}
