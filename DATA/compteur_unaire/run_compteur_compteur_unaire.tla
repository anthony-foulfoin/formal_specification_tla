---------------- MODULE run_compteur_compteur_unaire ----------------

EXTENDS Naturals, FiniteSets, Sequences, var_raffinement

CONSTANT
    N, D

A == INSTANCE compteur

C == INSTANCE compteur_unaire

Liaison(etatA, etatC) ==
  etatA = Len(etatC)

INSTANCE run_raffinement WITH ETATA <- A!ETAT, InitA <- A!Init, ContratClientA <- A!ContratClient, ContratModuleA <- A!ContratModule,
                              ETATC <- C!ETAT, InitC <- C!Init, ContratClientC <- C!ContratClient, ContratModuleC <- C!ContratModule


================================================================
