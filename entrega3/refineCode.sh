#!/bin/bash

./tiger "$1" -code > CODE.s

X=".text\\n.global main\\n.extern printf\\n"

Y="string1: .asciz \"Result: %d\n\""

sed -i.old "1s;^;$X;" CODE.s

echo $Y >> CODE.s

sed -i 's/L0_//g' CODE.s
