------------- MODULE liste -------------

EXTENDS Naturals, FiniteSets, Sequences


CONSTANT N, \* taille maximale de la liste
         D  \* type des éléments

CHOIX == { "Insert", "Remove", "Put", "Get", "Occurrence", "Cardinal"  }

\* ensemble des séquences de taille bornée par T, d'éléments de type E
BoundedSeq(T, E) == UNION { [1..n -> E ] : n \in 0..T }

ETAT == BoundedSeq(N, D)

-------------------------------------------

\* état initial
Init(etat) ==
 /\ etat = << >>

\* incrémenter
Pre_Insert(param, etat) ==
 /\ param \in D
 /\ Len(etat) < N

Act_Insert(param, etat, etat_p, result) ==
 /\ etat_p = << param >> \o etat
 /\ result = "__NO_DATA"

\* décrémenter
Pre_Remove(param, etat) ==
 /\ param = "__NO_DATA"
 /\ etat # << >>

Act_Remove(param, etat, etat_p, result) ==
 /\ etat_p = Tail(etat)
 /\ result = Head(etat)

\* écrire
Pre_Put(param, etat) ==
 /\ param \in [ indice : 1..Len(etat), valeur : D ]

Act_Put(param, etat, etat_p, result) ==
 /\ etat_p = [ etat EXCEPT ![param.indice] = param.valeur ]
 /\ result = "__NO_DATA"

\* lire
Pre_Get(param, etat) ==
 /\ param \in 1..Len(etat)

Act_Get(param, etat, etat_p, result) ==
 /\ etat_p = etat
 /\ result = etat[param]

\* occurrence
Pre_Occurrence(param, etat) ==
 /\ param \in D

Act_Occurrence(param, etat, etat_p, result) ==
 /\ etat_p = etat
 /\ result = Cardinality({ i \in 1..Len(etat) : etat[i] = param })

\* cardinal
Pre_Cardinal(param, etat) ==
 /\ param = "__NO_DATA"

Act_Cardinal(param, etat, etat_p, result) ==
 /\ etat_p = etat
 /\ result = Len(etat)

-------------------------------------------

Cardinal(etat) ==
 LET Sum[S\in SUBSET D] ==
  IF (S = {}) THEN 0 ELSE
  LET d  == CHOOSE s \in S : TRUE IN
  LET sd == CHOOSE i \in 0..N : Act_Occurrence(d, etat, etat, i) IN
  sd + Sum[S \ { d }]
 IN Sum[D]

Inv(etat) ==
 /\ etat \in ETAT
 /\ Cardinal(etat) \leq N
 /\ Act_Cardinal("__NO_DATA", etat, etat, Cardinal(etat))

-------------------------------------------

ContratClient(choix, param, etat) ==
 \/ (choix = "Insert"     /\ Pre_Insert(param, etat))
 \/ (choix = "Remove"     /\ Pre_Remove(param, etat))
 \/ (choix = "Put"        /\ Pre_Put(param, etat))
 \/ (choix = "Get"        /\ Pre_Get(param, etat))
 \/ (choix = "Occurrence" /\ Pre_Occurrence(param, etat))
 \/ (choix = "Cardinal"   /\ Pre_Cardinal(param, etat))

ContratModule(choix, param, etat, etat_prime, result) ==
 /\ (choix = "Insert"     => (Pre_Insert(param, etat)     => Act_Insert(param, etat, etat_prime, result)))
 /\ (choix = "Remove"     => (Pre_Remove(param, etat)     => Act_Remove(param, etat, etat_prime, result)))
 /\ (choix = "Put"        => (Pre_Put(param, etat)        => Act_Put(param, etat, etat_prime, result)))
 /\ (choix = "Get"        => (Pre_Get(param, etat)        => Act_Get(param, etat, etat_prime, result)))
 /\ (choix = "Occurrence" => (Pre_Occurrence(param, etat) => Act_Occurrence(param, etat, etat_prime, result)))
 /\ (choix = "Cardinal"   => (Pre_Cardinal(param, etat)   => Act_Cardinal(param, etat, etat_prime, result)))

===========================================
