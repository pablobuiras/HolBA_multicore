addi 	  x7, x0, 42
1:
lr.w.aq x5, (x7)
bne     x5, x0, 1b
addi    x5, x0, 1
sc.w    x6, x5, (x7)
bne     x6, x0, 1b
nop
addi    x5, x0, 0
fence rw,w
sw     x0,(x7)
