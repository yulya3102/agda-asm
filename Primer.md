# Linking primer

Данная работa формализует упрощенный вариант динамической линковки,
используемой в файлах ELF и описанной в [@dsohowto]. В этом упрощенном
варианте поддерживается только линковка внешних функций и не подерживаются
внешние переменные.

Динамическая линковка предполагает использование внешних символов из
библиотек без включения этих библиотек в объектный файл, как это было бы
при статической линковке. При этом динамическому линковщику необходимо
чем-то заполнить *релокации* - "пустые" аргументы инструкций перехода на
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

Помимо секции PLT, динамический линковщик добавляет к объектному файлу еще
одну секцию, называаемую GOT (Global Offset Table). В этой секции
динамический линковщик на каждую внешнюю функцию $f$ генерирует статическую
ячейку памяти $got.f$. Эта секция должна заполняться в рантайме
динамическим загрузчиком.

Добавленные в секцию PLT процедуры $plt.f$ содержат в себе единственную
инструкцию: indirect jump по указателю $got.f$. Если в $got.f$ находится
правильный адрес загруженной в память внешней функции $f$, то исполнение
процедуры $plt.f$ приведет к исполнению функции $f$.

После такого преобразования для вызова внешней функции $f$ все еще
необходимо заполнить ячейку памяти $got.f$. Но это существенно
отличается от исходного неслинкованного объектного файла: заполнить
релокации исходного файла можно было только до запуска программы, в
то время как заполнить ячейку $got.f$ можно и в рантайме. В этом и
состоит важность инструкции indirect jump: она позволяет в рантайме менять
целевую точку инструкций перехода.

Динамический линковщик совершает подобное преобразование над объектными
файлами, и на этом его работа заканчивается. После этого в рантайме
динамический загрузчик заполняет секции GOT загруженных библиотек, и код
становится полностью пригодным для исполнения.