Compiladores
============

Etapa de revisión 2016

Notas de la entrega1:

Para que funcione el test999.tig: No generamos pares de dependencia para los miembros de records a hagan referencia a tipos que se definen en su propio batch.

Para que funcione el test777.tig, test123.tig y test321.tig: Para asignar un tipo a un miembros de un record primero miramos su propio batch y si no está, luego vemos el entorno de tipos. Como consecuencia, tuve que agregar la función "tipoReal" en FieldVar y SubscriptVar.
