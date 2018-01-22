#!/bin/bash

filename=$(basename "$1")
extension="${filename##*.}"
filename="${filename%.*}"

if [ ! -f "$1" ]; then
    echo "El archivo $1 no existe"
else
  echo "Compilando $1 ..."

  if [ "$extension" == "tig" ]
  then
   ./tiger "$1" -code > "$filename".s
  
    X=".syntax unified\\n.thumb\\n\\n.text\\n.global _tigermain\\n\\n"

    sed -i "1s;^;$X;" "$filename".s

    xclip -sel c < "$filename".s

    echo "Fin de compilación"
  else
    echo "El archivo que se intenta compilar debe tener extensión \"tig\""
  fi
fi
