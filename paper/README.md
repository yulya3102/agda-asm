There are two "top-level" targets, both of them correspond to appendices of
the paper:

*   `BlockEqIsEq.lagda` the Appendix A which proves that defined
    relation of blocks equivalence meets axioms of equivalence relation.
*   `RuntimeEq.lagda` is the Appendix B which contains the main proof of
    the paper.

Both of them rely heavily on `agda-stdlib` which should be specified in
Agda's include path, like this:

    agda -i . -i agda-stdlib/src RuntimeEq.lagda

Every other module that is used in this formalization is imported into
"top-level" source file at some point, so there is no need to type-check
them manually.

Full source code with paper text and `agda-stdlib` submodule can be found
at [https://github.com/yulya3102/agda-asm](https://github.com/yulya3102/agda-asm).
