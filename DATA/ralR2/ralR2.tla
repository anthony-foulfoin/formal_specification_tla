------------- MODULE ralR2 -------------

EXTENDS Naturals, Sequences, TLC

CONSTANT L, \* décomposition binaire maximale de l'ensemble
         D  \* type des éléments

CHOIX == { "Insert", "Remove", "Put", "Get", "Occurrence", "Cardinal" }

Power2[i\in Nat] ==
 IF (i = 0) THEN 1 ELSE 2 * Power2[i - 1]

ELT == INSTANCE power2liste WITH P <- L, D <- D

ETAT == [ 0..L -> ELT!ETAT ]

Inv(etat) ==
 /\ etat \in Seq(ELT!ETAT)

Zero == << >>

Cardinal[ss \in Seq(ELT!ETAT)] == 
	CASE (ss = Zero) -> 0
	[] (Head(ss) = ELT!Vide) -> 0
	[] OTHER         -> Len(Head(ss)) + Cardinal[Tail(ss)]

PutBloc[indice \in Nat,bloc \in ELT!ETAT,elt \in D] ==
	LET PutBlocInt[indicei \in Nat,bloci \in ELT!ETAT,elti \in D,cpti \in Nat]==
		LET hd == Head(bloci) IN
		LET tl == Tail(bloci) IN
		CASE (cpti=indicei) 	-> ELT!Join(<<elti>>, tl)
		[] OTHER 			-> ELT!Join(<<hd>>, PutBlocInt[indicei,tl,elti,cpti+1])
	IN PutBlocInt[indice,bloc,elt,1]
		
 
Put[indice \in Nat, elt \in D, liste  \in Seq(ELT!ETAT)] == 
	 LET ind_in == Cardinal[liste]-indice+1 IN
		LET RechercheBloc[indicei \in Nat, elti \in D, listei  \in Seq(ELT!ETAT), poids \in Nat,cpt \in Nat] ==
			LET hd == Head(listei) IN
			LET tl == Tail(listei) IN
			CASE (hd = ELT!Vide)		-> <<hd>> \o RechercheBloc[indicei, elti, tl, poids*2,cpt]
			[] (indicei <= cpt+poids) 	-> <<PutBloc[indicei-cpt,hd,elti]>> \o tl
			[] OTHER					-> <<hd>> \o RechercheBloc[indicei,elti,tl,poids*2,cpt+poids]
		IN
			RechercheBloc[ind_in,elt,liste,1,0]

GetBloc[indice \in Nat,bloc \in ELT!ETAT] ==
	LET GetBlocInt[indicei \in Nat,bloci \in ELT!ETAT,cpti \in Nat]==
		LET hd == Head(bloci) IN
		LET tl == Tail(bloci) IN
		CASE (cpti=indicei) 	-> hd
		[] OTHER 				-> GetBlocInt[indicei,tl,cpti+1]
	IN GetBlocInt[indice,bloc,1]
			
Get[indice \in Nat, liste \in Seq(ELT!ETAT)] == 
	 LET ind_in == Cardinal[liste]-indice+1 IN
		LET RechercheBloc[indicei \in Nat, listei  \in Seq(ELT!ETAT), poids \in Nat,cpt \in Nat] ==
			LET hd == Head(listei) IN
			LET tl == Tail(listei) IN
			CASE (hd = ELT!Vide)		-> RechercheBloc[indicei, tl, poids*2,cpt]
			[] (indicei <= cpt+poids) 	-> GetBloc[indicei-cpt,hd]
			[] OTHER					-> RechercheBloc[indicei,tl,poids*2,cpt+poids]
		IN
			RechercheBloc[ind_in,liste,1,0]

Occurrence[liste \in Seq(ELT!ETAT),elt \in D] ==
	LET OccurenceInt[listei \in Seq(ELT!ETAT),elti \in D,cpt \in Nat] ==
		LET hd == Head(listei) IN
		LET tl == Tail(listei) IN
		CASE (listei = Zero) 	-> cpt
		[] (hd = ELT!Vide)		-> OccurenceInt[tl,elti,cpt]
		[] OTHER				-> OccurenceInt[tl,elti,cpt+ELT!Occurrence(hd,elti)]
	IN 
		OccurenceInt[liste,elt,0]
		

Add[carry \in ELT!ETAT, ss \in Seq(ELT!ETAT)] ==
		IF (Len(ss) < 2) THEN
			<< carry >> \o ss
		ELSE
			LET case1 == Head(ss) IN
			LET case2 == Head(Tail(ss)) IN
			LET reste == Tail(Tail(ss)) IN
			IF (Len(case1) = Len(case2)) THEN
				<< ELT!Join(carry, ELT!Join(case1, case2)) >> \o reste
			ELSE
				<< carry >> \o ss

Div2[liste \in ELT!ETAT] ==
	LET lg == Len(liste) IN
	LET Div2_aux[liste_aux \in ELT!ETAT, n \in Nat] == 
		CASE (liste_aux = ELT!Vide)    -> ELT!Vide
		[] (n > lg \div 2)             -> Div2_aux[Tail(liste_aux), n-1]	
		[] OTHER                       -> liste_aux
	IN
		Div2_aux[liste, lg]
			
Remove[ss \in Seq(ELT!ETAT)] ==
	LET case == Head(ss) IN
	LET reste == Tail(ss) IN
	IF (Len(case) = 1) THEN
		[ result |-> << ELT!Vide >> \o reste,
		  borrow |-> ELT!Vide ]
	ELSE
		[ result |-> << Div2[case] >> \o << Div2[case] >> \o reste,
		  borrow |-> ELT!Vide ]  
		  
-------------------------------------------

\* état initial
Init(etat) ==
 /\ etat = << <<>> >>

\* incrémenter
Pre_Insert(param, etat) ==
 /\ param \in D
 /\ Cardinal[etat] < Power2[L]

Act_Insert(param, etat, etat_p, result) ==
 LET inc == Add[ELT!Unit(param), etat] IN
 /\ etat_p = inc
 /\ result = "__NO_DATA"

\* décrémenter
Pre_Remove(param, etat) ==
 /\ param = "__NO_DATA"
 /\ Cardinal[etat] > 0

Act_Remove(param, etat, etat_p, result) ==
 LET dec == Remove[etat] IN
 /\ etat_p = dec.result
 /\ result = ELT!Pick(dec.borrow, result)
 
 \* écrire
Pre_Put(param, etat) ==
 /\ param \in [ indice : 1..Cardinal[etat], valeur : D ]

Act_Put(param, etat, etat_p, result) ==
 /\ etat_p =  Put[param.indice, param.valeur, etat]
 /\ result = "__NO_DATA"

\* lire
Pre_Get(param, etat) ==
 /\ param \in 1..Cardinal[etat]

Act_Get(param, etat, etat_p, result) ==
 /\ etat_p = etat
 /\ result = Get[param, etat]

\* occurrence
Pre_Occurrence(param, etat) ==
 /\ param \in D

Act_Occurrence(param, etat, etat_p, result) ==
 /\ etat_p = etat
 /\ result = Occurrence[etat,param]
 
\* cardinal
Pre_Cardinal(param, etat) ==
 /\ param = "__NO_DATA"

Act_Cardinal(param, etat, etat_p, result) ==
 /\ etat_p = etat
 /\ result = Cardinal[etat]

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
