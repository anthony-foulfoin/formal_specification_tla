---------------- MODULE run_tas_liste ----------------

EXTENDS Naturals, var_raffinement

CONSTANT
    N, D

A == INSTANCE tas

C == INSTANCE liste

Liaison(etatA, etatC) ==
 /\ A!Cardinal(etatA) = C!Cardinal(etatC)
 /\ \A d \in D : \A o \in 0..C!Cardinal(etatC) :
     A!Act_Occurrence("__NO_DATA", etatA, etatA, o) = C!Act_Occurrence("__NO_DATA", etatC, etatC, o)

INSTANCE run_raffinement WITH ETATA <- A!ETAT, InitA <- A!Init, ContratClientA <- A!ContratClient, ContratModuleA <- A!ContratModule,
                              ETATC <- C!ETAT, InitC <- C!Init, ContratClientC <- C!ContratClient, ContratModuleC <- C!ContratModule


================================================================
