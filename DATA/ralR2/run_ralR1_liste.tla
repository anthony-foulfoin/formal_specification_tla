---------------- MODULE run_ralR1_liste ----------------

EXTENDS Naturals, FiniteSets, Sequences, var_raffinement

CONSTANT
    N, L, D

A == INSTANCE liste

C == INSTANCE ralR1

Liaison(etatA, etatC) ==
 /\ C!Cardinal(etatC) = Len(etatA)

INSTANCE run_raffinement WITH ETATA <- A!ETAT, InitA <- A!Init, ContratClientA <- A!ContratClient, ContratModuleA <- A!ContratModule,
                              ETATC <- C!ETAT, InitC <- C!Init, ContratClientC <- C!ContratClient, ContratModuleC <- C!ContratModule


================================================================
