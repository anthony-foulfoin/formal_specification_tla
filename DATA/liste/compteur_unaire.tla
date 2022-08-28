------------- MODULE compteur_unaire -------------

EXTENDS Naturals, Sequences


CONSTANT N, \* valeur maximale du compteur
         D  \* type des éléments

CHOIX == { "Insert", "Remove", "Cardinal" }

\* ensemble des séquences de taille bornée par T, d'éléments de type E
BoundedSeq(T, E) == UNION { [1..n -> E ] : n \in 0..T }

ETAT == BoundedSeq(N, { 1 })

Inv(etat) ==
 /\ Len(etat) \leq N 

-------------------------------------------

\* état initial
Init(etat) ==
 /\ etat = << >>

\* incrémenter
Pre_Insert(param, etat) ==
 /\ param \in D
 /\ Len(etat) < N

Act_Insert(param, etat, etat_p, result) ==
 /\ etat_p = << 1 >> \o etat
 /\ result = "__NO_DATA"

\* décrémenter
Pre_Remove(param, etat) ==
 /\ param = "__NO_DATA"
 /\ etat # << >>

Act_Remove(param, etat, etat_p, result) ==
 /\ etat_p = Tail(etat)
 /\ result \in D

\* cardinal
Pre_Cardinal(param, etat) ==
 /\ param = "__NO_DATA"

Act_Cardinal(param, etat, etat_p, result) ==
 /\ etat_p = etat
 /\ result = Len(etat)

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
