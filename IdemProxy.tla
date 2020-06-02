---- MODULE IdemProxy ----

(***************************************************************************)
(* Expectations :                                                          *)
(* - Every request must be hit the server exactly once                     *)
(* - For each try of a request, the response must be the same              *)
(* - 2 tries / requests must be processable in parallel                    *)
(***************************************************************************)

EXTENDS Integers \*, FiniteSets

CONSTANTS  
    _ReqIDs, \* the request IDs sent by the user (an Id is the idempotent key)
    _MaxTries,
    NULL

ASSUME _MaxTries < 10

VARIABLES 
    reqTriesCount, \* the different tries of specific _Requests 
    hits, \* the number of hits of the "protected" backend per requests
    tries, \* a specific real 
    responses \* the responses received by the client for each try

vars == <<tries, reqTriesCount, hits, responses>>

(***************************************************************************)
(* Initial State                                                           *)
(***************************************************************************)
Init == 
    /\ reqTriesCount = [r \in _ReqIDs |-> 0]
    /\ tries = [r \in _ReqIDs |-> [id |-> 0, status |-> "not submitted"]]
    /\ hits = [r \in _ReqIDs |-> 0]
    /\ responses = <<>> 

TypeInvariants ==
  /\ TRUE \* todo


(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
Submit(r) ==
    /\ reqTriesCount[r] < _MaxTries
    /\ reqTriesCount' = [reqTriesCount EXCEPT ![r] = reqTriesCount[r] + 1]
    /\ tries' = [tries EXCEPT ![r].id = reqTriesCount[r] + 1, ![r].status = "submitted"]
    /\ UNCHANGED <<hits, responses>>

(***************************************************************************)
(* Spec                                                                    *)
(***************************************************************************)
Next ==
  \/ \E r \in _ReqIDs :
    \/ Submit(r)

Spec == 
  /\ Init 
  /\ [][Next]_vars 

====
