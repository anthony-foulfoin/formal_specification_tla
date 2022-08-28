---------------- MODULE run_module ----------------

EXTENDS Naturals

VARIABLES
\* variables utilisateurs
    Etat,
    Param,
    Result,
\* variables spéciales
    Tour,
    Choix

CONSTANTS
    CHOIX,
    Init(_),
    ContratClient(_,_,_),
    ContratModule(_,_,_,_,_)

NO_DATA == "<NO_DATA>"

----------------------------------------------------------------

\* SPECIFICATION DES EXECUTIONS DU MODULE

\* initialisation des variables d'états
Initial ==
 /\ Choix = NO_DATA
 /\ Tour = "client"
 /\ Param = NO_DATA
 /\ Result = NO_DATA
 /\ Init(Etat)

\* action du client sur les variables d'états
ActionClient ==
 /\ Tour  = "client"
 /\ Tour' = "module"
 /\ UNCHANGED Etat
 /\ Result' = NO_DATA
 /\ ContratClient(Choix', Param', Etat)                     \* contrat instancié sur les variables d'états

\* action du module sur les variables d'états
ActionModule ==
 /\ Tour  = "module"
 /\ Tour' = "client"
 /\ Choix' = NO_DATA
 /\ Param ' = NO_DATA
 /\ ContratModule(Choix, Param, Etat, Etat', Result')          \* contrat instancié sur les variables d'états

Spec ==
 /\ Initial
 /\ [] [ ActionClient \/ ActionModule ]_<<Tour, Choix, Param, Etat, Result>>


================================================================
