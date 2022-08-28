---------------- MODULE run_ralR1_liste ----------------

EXTENDS Naturals, FiniteSets, Sequences, var_raffinement

CONSTANT
    N, L, D

A == INSTANCE liste

C == INSTANCE ralR1

Liaison(etatA, etatC) ==
 /\ A!Cardinal(etatA) = C!Cardinal(etatC)
 /\ \A d \in D : \A o \in 0..C!Cardinal(etatC) :
     A!Act_Occurrence(d, etatA, etatA, o) = C!Act_Occurrence(d, etatC, etatC, o)

INSTANCE run_raffinement WITH ETATA <- A!ETAT, InitA <- A!Init, ContratClientA <- A!ContratClient, ContratModuleA <- A!ContratModule,
                              ETATC <- C!ETAT, InitC <- C!Init, ContratClientC <- C!ContratClient, ContratModuleC <- C!ContratModule


================================================================
