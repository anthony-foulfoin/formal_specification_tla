---------------- MODULE run_compteur_tas ----------------

EXTENDS Naturals, var_raffinement

CONSTANT
    N, D

A == INSTANCE compteur

C == INSTANCE tas

Liaison(etatA, etatC) ==
  etatA = C!Cardinal(etatC)

INSTANCE run_raffinement WITH ETATA <- A!ETAT, InitA <- A!Init, ContratClientA <- A!ContratClient, ContratModuleA <- A!ContratModule,
                              ETATC <- C!ETAT, InitC <- C!Init, ContratClientC <- C!ContratClient, ContratModuleC <- C!ContratModule


================================================================
