------------- MODULE compteur_binaire -------------

EXTENDS Naturals, Sequences, TLC


CONSTANT L, \* nombre de bits du compteur
         D  \* type des éléments

ASSUME L \geq 1

CHOIX == { "Insert", "Remove", "Cardinal" }

ELT == INSTANCE booleen WITH P <- L, D <- D

\* séquence des bits significatifs. bit de poids faible (2^0) en tête.
ETAT == [ 1..L -> ELT!ETAT ]

Inv(etat) ==
 /\ etat \in ETAT

Zero == << >>

Increment[carry \in ELT!ETAT, ss \in Seq(ELT!ETAT)] ==
 CASE (ss = Zero)           -> << carry >>
   [] (Head(ss) = ELT!Vide) -> << carry  >> \o Tail(ss)
   [] OTHER                 -> LET carry_succ == ELT!Join(carry, Head(ss)) IN
                               LET inc_succ   == Increment[carry_succ, Tail(ss)] IN
                               << FALSE >> \o inc_succ

Decrement[ss \in Seq(ELT!ETAT)] ==
 CASE (Len(ss) = 1)         -> [ result |-> << ELT!Vide >>,
                                 borrow |-> Head(ss) ]
   [] (Head(ss) = ELT!Vide) -> LET dec_succ == Decrement[Tail(ss)] IN
                               LET split == ELT!Split(dec_succ.borrow) IN
                               [ result |-> << split[2] >> \o dec_succ.result,
                                 borrow |-> split[1] ]
   [] OTHER                 -> [ result |-> << ELT!Vide >> \o Tail(ss),
                                 borrow |-> Head(ss) ]

BitToInteger[b\in ELT!ETAT] ==
 IF (b = ELT!Vide) THEN 0 ELSE 1

BinaryToInteger[s \in Seq(ELT!ETAT)] ==
 IF (s = Zero) THEN 0 ELSE
 BitToInteger[Head(s)] + 2*BinaryToInteger[Tail(s)]

Power2[i\in Nat] ==
 IF (i = 0) THEN 1 ELSE 2 * Power2[i - 1]

-------------------------------------------

\* état initial
Init(etat) ==
 /\ etat = [ i \in 1..L |-> ELT!Vide ]

\* incrémenter
Pre_Insert(param, etat) ==
 /\ param \in D
 /\ \E i \in 1..L : etat[i] = ELT!Vide

Act_Insert(param, etat, etat_p, result) ==
 LET inc == Increment[ELT!Unit(param), etat] IN
 /\ etat_p = inc
 /\ result = "__NO_DATA"

\* décrémenter
Pre_Remove(param, etat) ==
 /\ param = "__NO_DATA"
 /\ \E i \in 1..L : etat[i] # ELT!Vide

Act_Remove(param, etat, etat_p, result) ==
 LET dec == Decrement[etat] IN
 /\ etat_p = dec.result
 /\ ELT!Pick(dec.borrow, result)

\* cardinal
Pre_Cardinal(param, etat) ==
 /\ param = "__NO_DATA"

Act_Cardinal(param, etat, etat_p, result) ==
 /\ etat_p = etat
 /\ result = BinaryToInteger[etat]

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
