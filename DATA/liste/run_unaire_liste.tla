---------------- MODULE run_unaire_liste ----------------

EXTENDS Naturals, FiniteSets, Sequences, var_raffinement

CONSTANT
    N, D

A == INSTANCE compteur_unaire

C == INSTANCE liste

Liaison(etatA, etatC) ==
  Len(etatA) = Len(etatC)

INSTANCE run_raffinement WITH ETATA <- A!ETAT, InitA <- A!Init, ContratClientA <- A!ContratClient, ContratModuleA <- A!ContratModule,
                              ETATC <- C!ETAT, InitC <- C!Init, ContratClientC <- C!ContratClient, ContratModuleC <- C!ContratModule


================================================================
