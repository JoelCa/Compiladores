#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
PATH_TIGER="$DIR/tiger"

filename=$(basename "$1")
extension="${filename##*.}"
filename="${filename%.*}"

if [ ! -f "$1" ]; then
    echo "El archivo $1 no existe"
else
  echo "Compilando $1 ..."

  if [ "$extension" == "tig" ]
  then
    tiger_output="$(exec "$PATH_TIGER" "$1" -code 2>&1)"
    #./tiger "$1" -code 2>&1 > "$filename".s
  
    res="$(echo "$tiger_output" | awk 'NR==1{print $1}')"
   
    if [[ ("$res" == "Fail:")  || ("$res" == "Uncaught") || ("$res" == "Error") ]];
    then
      echo "$tiger_output"
    else
      echo "$tiger_output" > "$filename".s

      X=".syntax unified\\n.thumb\\n\\n.text\\n.global _tigermain\\n\\n"

      sed -i "1s;^;$X;" "$filename".s

      xclip -sel c < "$filename".s

      echo "Fin de compilación"
    fi
  else
    echo "El archivo que se intenta compilar debe tener extensión \"tig\""
  fi
fi
