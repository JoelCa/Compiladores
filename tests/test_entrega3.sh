#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
PATH_TIGER="$DIR/../entrega3/tiger"
PATH_TEST="$DIR/$1"

cd "$DIR/$1"

case $2 in
    good)
        TYPE=true
        ;;
    error)
        TYPE=false
        ;;
    *)
        echo "error: $2 no es un argumento válido"
        exit 1
        ;;
esac

if [ -d "$DIR/$1" ]
then
    files="$(ls *.tig)"
    while read -r f
    do
        tiger_output="$(exec "$PATH_TIGER" "$f" 2>&1)"
        #error= "$(echo $tiger_output 2> jojo)"
        res="$(echo "$tiger_output" | awk 'NR==1{print $1}')"
        if [ $TYPE = true ]
        then
            if [[ ("$res" == "Fail:")  || ("$res" == "Uncaught") || ("$res" == "Error") ]];
            then
                printf "Resultado inválido en $f\nDa error de tipo, cuando debería estar ok.\n"
            else
                printf "$f válido.\n"
            fi
        else
            if [[ ("$res" == "Fail:")  || ("$res" == "Uncaught") || ("$res" == "Error") ]];
            then
                printf "$f válido.\n"
            else
                printf "resultado inválido en $f\nDa ok, cuando debería dar un error.\n"
            fi
        fi
    done <<< "$files"
else
    echo "error: directorio inválido"
    exit 1
fi

exit 0
