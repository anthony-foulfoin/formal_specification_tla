---------------- MODULE run_compteur_compteur_binaire ----------------

EXTENDS Naturals, FiniteSets, Sequences, var_raffinement

CONSTANT
    L, N, D

A == INSTANCE compteur

C == INSTANCE compteur_binaire

ASSUME (N + 1 = C!Power2[L])

Liaison(etatA, etatC) ==
  etatA = C!BinaryToInteger[etatC]

INSTANCE run_raffinement WITH ETATA <- A!ETAT, InitA <- A!Init, ContratClientA <- A!ContratClient, ContratModuleA <- A!ContratModule,
                              ETATC <- C!ETAT, InitC <- C!Init, ContratClientC <- C!ContratClient, ContratModuleC <- C!ContratModule


================================================================
