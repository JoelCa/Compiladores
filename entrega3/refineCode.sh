#!/bin/bash

./tiger "$1" -code > CODE.s

X=".syntax unified\\n.thumb\\n\\n.text\\n.global _tigermain\\n.extern printf\\n"

Y='string1: .asciz \"Result: %d\\n\"\n.align'

sed -i.old "1s;^;$X;" CODE.s

sed -i "\$a$Y" CODE.s

sed -i 's/L0_//g' CODE.s
