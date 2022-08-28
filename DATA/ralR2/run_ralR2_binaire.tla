---------------- MODULE run_ralR2_binaire ----------------

EXTENDS Naturals, FiniteSets, Sequences, var_raffinement

CONSTANT
    L, D

A == INSTANCE compteur_binaire

C == INSTANCE ralR2

Liaison(etatA, etatC) ==
  Len(etatA) = C!Cardinal[etatC]

INSTANCE run_raffinement WITH ETATA <- A!ETAT, InitA <- A!Init, ContratClientA <- A!ContratClient, ContratModuleA <- A!ContratModule,
                              ETATC <- C!ETAT, InitC <- C!Init, ContratClientC <- C!ContratClient, ContratModuleC <- C!ContratModule


================================================================
