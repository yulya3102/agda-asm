## Introduction

???

??? how-hard-memory-management-can-be ??? However, discussed in this
paper properties of dynamic linking does not require dynamic memory
management. Keeping that in mind, we can assume that all memory is static
and no allocation is taken.

## ??? (why and how)

???: should it be all-detailed typecheckable paper or
overview-with-key-ideas and some formalizations

## Typed assembly language definition

### Machine state types

TODO: write somewhere about different sizeof(type) for different types

There are three common parts of machine state used in assembly languages:
registers, memory and stack. Although stack is usually appears to be part
of memory, it has one important aspect that makes stack a separate concept.

In our model memory doesn't support dynamic allocation and statically
allocated for every object that needs it. But memory on stack is actually
dynamically allocated, and stack objects lifetime may differ from program
lifetime. Therefore, address pointing to some place in stack can point to
different objects of different types during the program lifetime. However,
memory allocation on stack is done with very simple algorithm: just
increment or decrement stack pointer until you reach stack limit. Its
simplicity allows us to forget hard memory allocation problems and
implement stack as another part of machine state with two operations:
allocating some memory of given type on top of it and freeing the memory on
top of it. We could also assume that stack can grow indefinitely and memory
is not limited, but that's not necessary since we only care for small part
of program lifetime that allocates finite amount of stack memory needed to
run allocator at most ??? times.

TODO: memory, registers and stacks definition (types)

???: RegType/Type difference does not really matter

There is another difficulty in stack definition. Stack actually serves for
two purposes: tracking return addresses and saving stack frames with local
variables. These two purposes are similar, but for type system they are
quite different. For local variables it only should only check ???, but for
return address it should make sure that `ret` is executed only in suitable
machine state. So, in our model there will be two different stacks: call
stack and data stack.

TODO: callstacktype should refer to itself, but that's not problem

TODO: callstacktype and datastacktype definitions

### Meta-assembler

TODO: reusable agda code is nice

Actual assembler code has to know exact instruction set, it wouldn't make
much sense to write any code without any knowledge about instructions. On
the other hand, any assembler code can be represented as a sequence of
basic blocks (?), and other concepts can be defined using basic blocks
definition. Using this method, concepts like memory and registers can have
block type as parameter and don't depend on instruction set directly. This
helps to keep code much more generic.

To statically analyze types of different parts of machine state we need to
know how blocks change them. For us to do this, type of block needs to have
information about changes of machine state types applied by the block.

TODO: diffs definition

TODO: block definition

TODO: memory, registers and stacks definition

## Program equivalence as block equivalence

TODO: block equivalence definition
TODO: why it can be considered as program equivalence

## Static vs. dynamic linking

We will consider programs after they are loaded to memory. Due to this
assumption we can ignore memory mapping problems.

Statically linked program is just all binaries merged together without any
transformations. Dynamically linked program is a bunch of object files with
PLT and GOT added and calls to functions replaced with calls to
correspondent PLT elements. But when they are loaded into memory, there's no
separations between libraries left, so the only difference between
statically and dynamically linked programs is in GOT, PLT and calls to
functions. Therefore, we don't even need to define dynamically linked
program as several object files.

???: dynamically linked program cat have more than one PLT entry
correspondent to some function
TODO: what is input
TODO: how to get dynamically linked program

## Statically linked program

## Dynamically linked program

code with PLT and GOT

GOT-correctness

generic code proofs (???)

equivalence proof
