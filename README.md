Compiladores
============

Compilador de Tiger para ARMv7.

Basado en el libro "Modern Compiler Implementation in ML".

## Instalación

Hacer make en el directorio "entrega3".

## Modo de uso

Generación del assembler en ARM de un archivo tiger.

```
$ ./tiger_compiler.sh <tiger file>
```

## Tests

Los ejemplos se encuentran en el directorio "test".

Ejemplo: si estamos ubicados en "entrega3" generamos
el asembler de "merge.tig" así:

```
$ ./tiger_compiler.sh ../tests/good/merge.tig
```
