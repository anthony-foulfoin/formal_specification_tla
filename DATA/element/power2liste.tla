------------- MODULE power2liste -------------

EXTENDS Naturals, FiniteSets, Sequences


CONSTANT P, \* taille maximale de la liste = 2^P
         D  \* type des éléments

Power2[i\in Nat] ==
 IF (i = 0) THEN 1 ELSE 2 * Power2[i - 1]

\* ensemble des listes de taille bornée par T, d'éléments de type D
BoundedSeq(T) == UNION { [ 1..S -> D ] : S \in 0..T }

ETAT == BoundedSeq(Power2[P])


-------------------------------------------
\* A COMPLETER

Vide ==

Unit(d) ==

Join(left, right) ==

Split(join) ==

Pick(liste, d) ==

Occurrence(liste, d) ==


===========================================
