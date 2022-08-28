------------- MODULE power2liste -------------

EXTENDS Naturals, FiniteSets, Sequences, Reals


CONSTANT P, \* taille maximale de la liste = 2^P
         D  \* type des éléments

Power2[i\in Nat] ==
 IF (i = 0) THEN 1 ELSE 2 * Power2[i - 1]

\* ensemble des listes de taille bornée par T, d'éléments de type D
BoundedSeq(T) == UNION { [ 1..S -> D ] : S \in 0..T }

ETAT == BoundedSeq(Power2[P])


-------------------------------------------
\* A COMPLETER

Vide == << >>

Unit(d) == << d >>

Join(left, right) == left \o right

Split(join) == << SubSeq( join, 1, Len(join) \div 2 ) , SubSeq( join, (Len(join) \div 2)+1, Len(join)) >>

Occurrence(liste, d) == Cardinality({ i \in 1..Len(liste) : liste[i] = d })

Pick(liste, d) == 
	/\ Len(liste)>0
	/\ d \in D
	/\ Occurrence(liste,d) > 0

===========================================
