section .plt
    plt.f:
        jmp [got.f]

section .text
    <...>
        call plt.f
    <...>

section .got
    got.f dd 0x0
