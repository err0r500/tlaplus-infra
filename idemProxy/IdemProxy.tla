---- MODULE IdemProxy ----

(***************************************************************************)
(* Expectations :                                                          *)
(* - Every request must be hit the server exactly once                     *)
(* - For each try of a request, the response must be the same              *)
(* - 2 requests must be processable in parallel                            *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS  
    _ReqIDs, \* the request IDs sent by the user (an Id is the idempotent key)
    _MaxTries,
    NULL

ASSUME _MaxTries < 10

VARIABLES 
    hits, \* the number of hits of the "protected" backend per requests
    requests \* a specific request 

vars == <<requests, hits>>

(***************************************************************************)
(* Initial State                                                           *)
(***************************************************************************)
Init == 
    /\ requests = [req \in _ReqIDs |-> [st \in 0.._MaxTries |-> "pending"]]
    /\ hits = [r \in _ReqIDs |-> 0]

TypeInvariants ==
  /\ TRUE \* todo




(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
HitProxy(r,i) ==
    /\ requests[r][i] = "pending"
    /\ requests' = [requests EXCEPT ![r][i] = "submitted"]
    /\ UNCHANGED <<hits>>



HitServer(r,i) ==
    /\ requests[r][i] = "submitted"
    /\ requests' = [requests EXCEPT ![r][i] = "processed"]
    /\ UNCHANGED <<hits>>


(***************************************************************************)
(* Spec                                                                    *)
(***************************************************************************)
Next ==
  \/ \E r \in _ReqIDs, i \in 0.._MaxTries:
    \/ HitProxy(r,i)
    \/ HitServer(r,i)

Fairness == \A r \in _ReqIDs, i \in 0.._MaxTries : 
                /\ SF_vars(HitServer(r,i)) 
                /\ SF_vars(HitProxy(r,i))
 
Spec == 
  /\ Init 
  /\ [][Next]_vars 
  /\ Fairness

RequestIsProcessedOnlyOnce ==
    [](\A req \in DOMAIN requests : Cardinality({x \in DOMAIN requests[req]: requests[req][x] = "processed"}) < 2)

THEOREM Spec => RequestIsProcessedOnlyOnce

=====