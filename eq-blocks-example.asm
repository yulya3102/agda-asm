    f:
        mov rax, 1
        ret

    g:
        call h
        mov rax, 1
        ret

    h:
        nop
        ret
