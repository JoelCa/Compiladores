#!/bin/bash

# directorio de tiger
tiger=~/GitHub/Compiladores/entrega1/tiger

# directorio de los test
test=~/GitHub/Compiladores/test

for caso in "good" "syntax" "type"
do
    case $caso in
        "good")
            echo "Test CORRECTOS:"
            ;;
        "syntax")
            echo "Test SINTAXIS ERRONEO:"
            ;;
        "type")
            echo "Test ERRONEOS:"
            ;;
    esac

    for archivo in `find $test/$caso -name '*.tig'`
    do
        if [ -f $archivo ]
        then
            read -p "Presione una tecla para procesar: $(basename $archivo)."
            $tiger $archivo
        fi
    done

done

echo "Ya no hay más archivos."

exit 0
