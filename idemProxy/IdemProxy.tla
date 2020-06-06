---- MODULE IdemProxy ----

(***************************************************************************)
(* Expectations :                                                          *)
(* - Every request must hit the server exactly once                     *)
(* - For each try of a request, the response must be the same              *)
(* - 2 requests must be processable in parallel                            *)
(***************************************************************************)

EXTENDS Integers, FiniteSets

CONSTANTS
    _ReqTokens, (* the request tokens used as idempotent keys *)
    _MaxTries  (* how many times a request is retried *)

ASSUME _MaxTries < 10

VARIABLES
    requests, (* the state of all requests and their corresponding tries *)
    locks (* locks on specific requests *)

vars == <<requests, locks>>


tryKeys == 1.._MaxTries (* simple helper providing the set of try keys *)


TypeInvariants ==
  /\ \A req \in _ReqTokens, x \in tryKeys: 
        requests[req][x] \in {
            "pending", 
            "inProxy", 
            "lock", 
            "processed", 
            "cached", 
            "fromCache"
            }
  /\ \A req \in _ReqTokens: locks[req] \in BOOLEAN




Init ==
(***************************************************************************)
(* `requests' is a struct with _ReqTokens as keys associated with structs with*)
(* tryKeys as keys associatied with the given try current status           *)
(***************************************************************************)
    /\ requests = [req \in _ReqTokens |-> [st \in tryKeys |-> "pending"]]
    /\ locks = [req \in _ReqTokens |-> FALSE] 


(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
HitProxy(r, i) ==
    /\ requests[r][i] = "pending"
    /\ requests' = [requests EXCEPT ![r][i] = "inProxy"]
    /\ UNCHANGED <<locks>>


Lock(r, i) ==
    (* check lock and set lock is atomic here *)
    /\ requests[r][i] = "inProxy"
    /\ locks[r] = FALSE
    /\ Cardinality({x \in DOMAIN requests[r]: requests[r][x] = "cached"}) = 0
    /\ requests' = [requests EXCEPT ![r][i] = "lock"]
    /\ locks' = [locks EXCEPT ![r] = TRUE]


HitServer(r, i) ==
    /\ requests[r][i] = "lock"
    /\ requests' = [requests EXCEPT ![r][i] = "processed"]
    /\ UNCHANGED <<locks>>

    
GetCache(r, i) == 
    /\ requests[r][i] = "inProxy"
    /\ Cardinality({x \in DOMAIN requests[r]: requests[r][x] = "cached"}) = 1
    /\ requests' = [requests EXCEPT ![r][i] = "fromCache"]
    /\ UNCHANGED <<locks>>

    
Cache(r, i) ==
    /\ requests[r][i] = "processed"
    /\ requests' = [requests EXCEPT ![r][i] = "cached"]
    /\ locks' = [locks EXCEPT ![r] = FALSE]




(***************************************************************************)
(* Spec                                                                    *)
(***************************************************************************)
Next ==
  \/ \E r \in _ReqTokens, i \in tryKeys:
    \/ HitProxy(r,i)
    \/ HitServer(r,i)
    \/ Lock(r,i)
    \/ Cache(r,i)
    \/ GetCache(r,i)

Fairness == \A r \in _ReqTokens, i \in tryKeys :
                /\ WF_vars(HitServer(r,i))
                /\ WF_vars(HitProxy(r,i))
                /\ WF_vars(Lock(r,i))
                /\ WF_vars(Cache(r,i))
                /\ WF_vars(GetCache(r,i))

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fairness

RequestIsProcessedOnlyOnce ==
    [](\A req \in DOMAIN requests :
        Cardinality({x \in DOMAIN requests[req]: requests[req][x] \in {"processed", "cached" }}) < 2)

EveryReqFinishAsCachedOrFromCache ==
    <>[](\A req \in DOMAIN requests : 
        \A x \in DOMAIN requests[req]: 
            (requests[req][x] = "cached") \/ (requests[req][x] = "fromCache"))

AttemptsCanBeProcessedConcurrently ==
    [](\A req \in DOMAIN requests, x \in tryKeys: requests[req][x] = "pending" => ENABLED HitProxy(req,x))

THEOREM Spec => RequestIsProcessedOnlyOnce
THEOREM Spec => EveryReqFinishAsCachedOrFromCache
THEOREM Spec => AttemptsCanBeProcessedConcurrently

=====
