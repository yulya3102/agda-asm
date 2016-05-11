# Introduction

Верифицировать иногда надо. Тулчейны-то уж точно стоит, потому что баги в
них, как правило, труднонаходимы, но могут причинить много боли.

Люди пытаются делать что-то на тему верификации тулчейнов, но пока
получается как-то не очень. Есть, к примеру, VeLLVM, который формализует
язык LLVM и делает доказанно корректные оптимизации в нем. Еще есть
CompCert, который представляет собой компилятор, делающий внутри себя
оптимизации, доказанно сохраняющие семантику программы. Но линкер он
использует системный, не верифицированный.

Может показаться, что линкер — достаточно тупая программа, в которой трудно
ошибиться. Но, тем не менее, в какой-то момент стали делать оптимизации на
этапе линковки, которые усложняют логику линкера, и в итоге в ней
действительно становится возможным ошибиться в коде линкера. Какие-то
чуваки в 2015 делали стресс-тесты для линкеров, и находили просто уйму
багов на этапе оптимизаций во время линковки. Это показывает, что
верифицировать линкеры все-таки нужно.

Линкер — достаточно низкоуровневая программа, которая работает с
скомпилированными объектными файлами, а значит, для рассуждений про него
надо искать формализации чего-то, очень близкого к ассемблеру. В этой
области есть Bedrock, который можно назвать чем-то типа макро-языка для
ассемблера, формализованного на Coq. Они пытались что-то делать с
линковкой, но получилось не очень.

Существует хорошая формализация ассемблера — TAL от Моррисетта и компании,
и много его расширений, покрывающих, например, почти настоящий язык
ассемблера x86 (TALx86), работу со стеком (STAL) и даже объектные файлы
(MTAL). Кстати говоря, в той же работе, что описывает MTAL, пытались что-то
делать с линковкой объектных файлов, но осилили только статическую.
Формализовать динамическую линковку — вот реальный челлендж.

TAL, конечно, всем хорош, но, к сожалению, TAL-релейтед утилиты написаны на
ML, а все доказательства про TAL делаются по-старинке, на бумажке. В этой
статье используется формализация на агде, близкая к смеси TALx86, STAL и
MTAL. На этом всем определяется, какие элементы добавляются в программу в
процессе динамической линковки, вводится понятие эквивалентности различных
программ и доказывается, что при правильно работающей рантайм-части линкера
статически и динамически слинкованные программы получатся эквивалентными.

Это можно считать первыми шагами в области формализации динамической
линковки, из чего впоследствии можно получить верифицированный линкер,
использующий под собой какую-то работающую математическую модель.

# Обзор используемой формализации TAL

Оригинальный TAL использует System F в качестве системы типов, что является
безусловным оверкиллом для нашей задачи. Система типов в используемой
формализации куда проще: тут описание типов. Для того, чтобы статически
анализировать поведение блоков кода, в их тип засунули описание того, что
этот блок делает с состоянием исполнителя, проще говоря, дифф над типом
состояния исполнителя. Инструкции, кстати, тоже имеют в своем типе эту
фигню. Стек для простоты распилили на две части: стек вызовов и стек
данных. Пожалуй, больше ничем существенным формализация от TAL не
отличается.

**TODO: Надо в формализацию моего типизированного ассемблера добавить
что-нибудь из MTAL**

Никаких кусков кода пока тут нет, потому что пока не очень понятно, что
здесь должно быть.

\ignore{
(TODO something about low-level memory problems) However, discussed in this
paper properties of dynamic linking does not require dynamic memory
management. Keeping that in mind, we can assume that all memory is static
and no allocation is taken.

## Who needs this and who did something related

TODO

## Why do I need my own Typed Assembly Language formalisation

Reasoning about linker itself does not make much sense: what you really
want to prove is that linked program is correct (in assumption that not
linked program was correct). To achieve this you need abstractions used in
proofs to be as close to real machine language as possible. This leads to
need for typed assembly language that looks exactly as real assembly
language, that can be translated directly into machine code with one-to-one
correspondence.

## What this Typed Assembly Language should look like

Formalisation of linking requires four concepts:

*   `call` instruction;
*   `jmp[]` instruction;
*   memory with addressable data;
*   memory with addressable code.

Linking itself appears only when some binary calls a function from another
binary, so the `call` instruction is the key concept for the linking. The
`jmp[]` (indirect jump) is the key concept of dynamic linking, because it
can do jumps to addresses dynamically stored somewhere in data. Argument of
the indirect jump instruction is an address of entry in data, and that
entry keeps address of some block of code, therefore this instruction needs
addressable data and addressable code.

In dynamic linking addresses of loaded code are stored in runtime in global
offset table (GOT), and indirect jumps to GOT entries happen instead of
direct call to functions.
}
