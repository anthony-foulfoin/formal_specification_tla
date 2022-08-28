------------- MODULE compteur -------------

EXTENDS Naturals


CONSTANT N, \* valeur maximale du compteur
         D  \* type des éléments

CHOIX == { "Insert", "Remove", "Cardinal" }

ETAT == 0..N

Inv(etat) ==
 /\ etat \in ETAT

-------------------------------------------

\* état initial
Init(etat) ==
 /\ etat = 0

\* incrémenter
Pre_Insert(param, etat) ==
 /\ param \in D
 /\ etat < N

Act_Insert(param, etat, etat_p, result) ==
 /\ etat_p = 1 + etat
 /\ result = "__NO_DATA"

\* décrémenter
Pre_Remove(param, etat) ==
 /\ param = "__NO_DATA"
 /\ etat > 0

Act_Remove(param, etat, etat_p, result) ==
 /\ etat_p = etat - 1
 /\ result \in D

\* cardinal
Pre_Cardinal(param, etat) ==
 /\ param = "__NO_DATA"

Act_Cardinal(param, etat, etat_p, result) ==
 /\ etat_p = etat
 /\ result = etat

-------------------------------------------

ContratClient(choix, param, etat) ==
 \/ (choix = "Insert"   /\ Pre_Insert(param, etat))
 \/ (choix = "Remove"   /\ Pre_Remove(param, etat))
 \/ (choix = "Cardinal" /\ Pre_Cardinal(param, etat))


ContratModule(choix, param, etat, etat_prime, result) ==
 /\ (choix = "Insert"   => (Pre_Insert(param, etat)   => Act_Insert(param, etat, etat_prime, result)))
 /\ (choix = "Remove"   => (Pre_Remove(param, etat)   => Act_Remove(param, etat, etat_prime, result)))
 /\ (choix = "Cardinal" => (Pre_Cardinal(param, etat) => Act_Cardinal(param, etat, etat_prime, result)))

===========================================
