------------- MODULE booleen -------------


CONSTANT P, \* taille maximale de la case = 2^P
         D  \* type des �l�ments

ETAT == BOOLEAN

-------------------------------------------

Vide == FALSE

Unit(d) == TRUE

Join(left, right) == left \/ right

Split(join) ==
 << join, join >>

Pick(bit, d) ==
 /\ bit
 /\ d \in D

\* non utilis� car non d�fini
Occurrence(bit, d) ==
 IF bit THEN "__NO_DATA" ELSE 0

===========================================
