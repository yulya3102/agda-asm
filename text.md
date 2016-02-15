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

Any assembler code can be represented as a sequence of basic blocks (link?).
TODO: why blocks

To statically analyze types of different parts of machine state we need to
know how blocks change them. For us to do this, type of block needs to have
information about changes of machine state types applied by the block.

TODO: diffs definition

TODO: block definition

TODO: memory, registers and stacks definition

## Program equivalence as block equivalence

TODO: block equivalence definition
TODO: why it can be considered as program equivalence

## Statically linked program

"default" code version - statically linked

## Dynamically linked program

code with PLT and GOT

GOT-correctness

generic code proofs (???)

equivalence proof
