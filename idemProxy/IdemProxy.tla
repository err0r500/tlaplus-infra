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
    _MaxTries \* how many times a request is retried

ASSUME _MaxTries < 10

VARIABLES 
    requests \* the state of all requests and their corresponding tries

vars == <<requests>>

\* `tryKeys' is a simple helper providing the set of try keys
tryKeys == 1.._MaxTries

(***************************************************************************)
(* Initial State                                                           *)
(***************************************************************************)
Init == 
(***************************************************************************)
(* `requests' is a struct with _ReqIDs as keys associated with structs with*)
(* tryKeys as keys associatied with the given try current status           *)
(***************************************************************************)
    /\ requests = [req \in _ReqIDs |-> [st \in tryKeys |-> "pending"]] 
    
     

TypeInvariants ==
  /\ TRUE \* todo



(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
HitProxy(r, i) ==
    /\ requests[r][i] = "pending"
    /\ requests' = [requests EXCEPT ![r][i] = "submitted"]
    

HitServer(r, i) ==
    /\ requests[r][i] = "submitted"
    /\ Cardinality({x \in DOMAIN requests[r]: requests[r][x] = "processed"}) = 0 \* add a blocking thread
    /\ requests' = [requests EXCEPT ![r][i] = "processed"]


(***************************************************************************)
(* Spec                                                                    *)
(***************************************************************************)
Next ==
  \/ \E r \in _ReqIDs, i \in tryKeys:
    \/ HitProxy(r,i)
    \/ HitServer(r,i)

Fairness == \A r \in _ReqIDs, i \in tryKeys : 
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