---------------- MODULE run_raffinement ----------------
EXTENDS Naturals, TLC

VARIABLES
    Param,
    EtatA, EtatC,
    Result, 
    Tour,
    Choix,
    RaffOk

CONSTANTS
    ETATA                    , ETATC,
    InitA(_)                 , InitC(_),
    ContratClientA(_,_,_)    , ContratClientC(_,_,_),
    ContratModuleA(_,_,_,_,_), ContratModuleC(_,_,_,_,_),
    Liaison(_,_)

NO_DATA == "<NO_DATA>"

RaffinementOk == [] RaffOk

CondInitial(etatA) ==
 /\ InitA(etatA)
 /\ Liaison(etatA, EtatC)

Initial ==
 /\ Choix = NO_DATA
 /\ Tour = "client"
 /\ Param = NO_DATA
 /\ Result = NO_DATA
 /\ InitC(EtatC)
 /\ LET InitialA == { etatA \in ETATA : CondInitial(etatA) }
    IN IF (InitialA # {})
       THEN /\ RaffOk = TRUE
            /\ EtatA \in InitialA
       ELSE /\ Print("Condition de raffinement de l'etat initial invalide !", TRUE)
            /\ RaffOk = FALSE
            /\ EtatA = NO_DATA

CondClient(etatC) ==
 /\ ContratClientC(Choix', Param', etatC)

ActionClient ==
 /\ Tour  = "client"
 /\ Tour' = "module"
 /\ UNCHANGED EtatA
 /\ Result' = NO_DATA
 /\ ContratClientA(Choix', Param', EtatA)
 /\ (IF (CondClient(EtatC))
     THEN /\ RaffOk' = TRUE
          /\ UNCHANGED EtatC
          /\ CondClient(EtatC)
     ELSE /\ Print("Condition de raffinement des actions du client invalide !", TRUE)
          /\ RaffOk' = FALSE
          /\ UNCHANGED EtatC )

CondModule(etatA_prime) ==
 /\ ContratModuleA(Choix, Param, EtatA, etatA_prime, Result')
 /\ Liaison(etatA_prime, EtatC')

ActionModule ==
 /\ Tour  = "module"
 /\ Tour' = "client"
 /\ Choix' = NO_DATA
 /\ Param' = NO_DATA
 /\ ContratModuleC(Choix, Param, EtatC, EtatC', Result')
 /\ LET EtatA_prime == { etatA_prime \in ETATA : CondModule(etatA_prime) }
    IN IF (EtatA_prime # {})
       THEN /\ RaffOk' = TRUE
            /\ EtatA' \in EtatA_prime
       ELSE /\ Print("Condition de raffinement des actions du module invalide !", TRUE)
            /\ RaffOk' = FALSE
            /\ EtatA' = NO_DATA

Spec ==
 /\ Initial
 /\ [] [ ActionClient \/ ActionModule ]_<<Param, EtatA, EtatC, Result, Tour, Choix, RaffOk>>

================
