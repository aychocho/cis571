        .section .data
input_string:   .asciz "Hello world!"

        # tohost/fromhost are data locations used by Spike
        .align 8
tohost: .byte 0
        .align 8
fromhost: .byte 0

        
        .section .text
        .globl _start
_start:
        # Load the address of the input string into a0
        la a0, input_string

        # Your code here!

capitalism:
        lb t0, 0(a0)
        beqz t0, end_program
        li t1, 97
        li t2, 122
        blt t0, t1, nextChar
        bgt t0, t2, nextChar
        li t3, 32
        sub t0, t0, t3
        sb t0, 0(a0)

nextChar:
        addi a0, a0, 1
        j capitalism


end_program:
        # jump here when you're done
        j end_program

