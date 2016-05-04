\ignore{
## Introduction

TODO

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
