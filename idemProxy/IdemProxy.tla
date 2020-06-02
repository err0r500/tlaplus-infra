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
    reqTriesCount, \* the different requests of specific _Requests 
    hits, \* the number of hits of the "protected" backend per requests
    requests, \* a specific request 
    responses \* the responses received by the client for each try

vars == <<requests, reqTriesCount, hits, responses>>

(***************************************************************************)
(* Initial State                                                           *)
(***************************************************************************)
Init == 
    /\ reqTriesCount = [r \in _ReqIDs |-> 0]
    /\ requests = [r \in _ReqIDs |-> <<>>]
    /\ hits = [r \in _ReqIDs |-> 0]
    /\ responses = <<>> 

TypeInvariants ==
  /\ TRUE \* todo








(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
HitProxy(r) ==
    /\ reqTriesCount[r] < _MaxTries
    /\ reqTriesCount' = [reqTriesCount EXCEPT ![r] = reqTriesCount[r] + 1]
    /\ requests' = [requests EXCEPT ![r] = Append(requests[r], [id |-> reqTriesCount[r] + 1, st |-> "submitted"])]
    /\ UNCHANGED <<hits, responses>>

HitServer(r) ==
    /\ requests[r].st = "submitted"
    /\ requests' = [requests EXCEPT ![r].st = "processed"]
    /\ UNCHANGED <<reqTriesCount, hits, responses>>







(***************************************************************************)
(* Spec                                                                    *)
(***************************************************************************)
Next ==
  \/ \E r \in _ReqIDs :
    \/ HitProxy(r)
    \/ HitServer(r)

Fairness == \A r \in _ReqIDs : 
                /\ SF_vars(HitServer(r)) 
                /\ SF_vars(HitProxy(r))
 
Spec == 
  /\ Init 
  /\ [][Next]_vars 
  /\ Fairness

RequestIsProcessedOnlyOnce == 
    [](\A req \in _ReqIDs : Len(SelectSeq(requests[req], LAMBDA r: r.st = "processed")) < 2)

THEOREM Spec => RequestIsProcessedOnlyOnce
====
