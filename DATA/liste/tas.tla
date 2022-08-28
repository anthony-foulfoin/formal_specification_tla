------------- MODULE tas -------------

EXTENDS Naturals, Bags, TLC


CONSTANT N, \* taille maximale du tas
         D  \* type des éléments

CHOIX == { "Insert", "Remove", "Occurrence", "Cardinal" }

\* ensemble des tas de taille bornée par T, d'éléments de type D
BoundedBag(T) == UNION { [ S -> 1..T ] : S \in SUBSET D }

ETAT == BoundedBag(N)

-------------------------------------------

\* état initial
Init(etat) ==
 /\ etat = EmptyBag

\* incrémenter
Pre_Insert(param, etat) ==
 /\ param \in D
 /\ BagCardinality(etat) < N

Act_Insert(param, etat, etat_p, result) ==
 /\ etat_p = etat \oplus SetToBag({param})
 /\ result = "__NO_DATA"

\* décrémenter
Pre_Remove(param, etat) ==
 /\ param = "__NO_DATA"
 /\ etat # EmptyBag

Act_Remove(param, etat, etat_p, result) ==
 \E elt \in DOMAIN(etat) :
 /\ etat_p = etat \ominus SetToBag({elt})
 /\ result = elt

\* occurrence
Pre_Occurrence(param, etat) ==
 /\ param \in D

Act_Occurrence(param, etat, etat_p, result) ==
 /\ etat_p = etat
 /\ result = IF param \in DOMAIN(etat) THEN etat[param] ELSE 0

\* cardinal
Pre_Cardinal(param, etat) ==
 /\ param = "__NO_DATA"

Act_Cardinal(param, etat, etat_p, result) ==
 /\ etat_p = etat
 /\ result = BagCardinality(etat)

-------------------------------------------

Cardinal(etat) ==
 LET Sum[S\in SUBSET D] ==
  IF (S = {}) THEN 0 ELSE
  LET d  == CHOOSE s \in S : TRUE IN
  LET sd == CHOOSE i \in 0..N : Act_Occurrence(d, etat, etat, i) IN
  sd + Sum[S \ { d }]
 IN Sum[D]

Inv(etat) == TRUE
 /\ etat \in ETAT
 /\ Cardinal(etat) \leq N
 /\ Act_Cardinal("__NO_DATA", etat, etat, Cardinal(etat))

-------------------------------------------

ContratClient(choix, param, etat) ==
 \/ (choix = "Insert"     /\ Pre_Insert(param, etat))
 \/ (choix = "Remove"     /\ Pre_Remove(param, etat))
 \/ (choix = "Occurrence" /\ Pre_Occurrence(param, etat))
 \/ (choix = "Cardinal"   /\ Pre_Cardinal(param, etat))

ContratModule(choix, param, etat, etat_prime, result) ==
 /\ (choix = "Insert"     => (Pre_Insert(param, etat)     => Act_Insert(param, etat, etat_prime, result)))
 /\ (choix = "Remove"     => (Pre_Remove(param, etat)     => Act_Remove(param, etat, etat_prime, result)))
 /\ (choix = "Occurrence" => (Pre_Occurrence(param, etat) => Act_Occurrence(param, etat, etat_prime, result)))
 /\ (choix = "Cardinal"   => (Pre_Cardinal(param, etat)   => Act_Cardinal(param, etat, etat_prime, result)))

===========================================
