---- MODULE UpdateCluster ----
EXTENDS Integers, FiniteSets

CONSTANTS  
    _Requests, \* the requests sent by the user
    _Workers, \* the pool of workers
    NULL

VARIABLES 
    lastVOK, \* last successfully applied version
    toApply, \* the version to apply (last requets that passed the initial tests)
    cluster, \*  cluster state 
    requests, \* the state of all requests
    workers, \* the state of all workers
    lock \* damn, I used a lock...

VARIABLES 
    \* these variables are tla+ details
    confOK, \* are we able to get a valid conf ? 
    reqCounter \* just to keep track of the order of submissions 

vars == <<confOK, reqCounter, lastVOK, toApply, cluster, requests, workers, lock>>

TypeInvariants == 
    /\ confOK \in BOOLEAN \* won't change for a specific behavior
    /\ lock \in BOOLEAN
    /\ cluster.st \in {
        "idle", 
        "starting",
        "partial", 
        "failed" 
        }
    /\ \A r \in _Requests : requests[r].st \in {
        "waiting", \* the request (req) hasn't been submitted yet
        "submitted", \* req has been submitted
        "rejected", \* req has been rejected (auth problem)
        "valid" \* auth etc passed 
        }
    /\ \A w \in _Workers : workers[w].st \in {
        "waiting", 
        "starting",
        "working"
        }



(***************************************************************************)
(* Initial State                                                           *)
(***************************************************************************)
Init == 
    /\ requests = [r \in _Requests |-> [st |-> "waiting", v |-> NULL]]
    /\ workers = [w \in _Workers |-> [st |-> "waiting", v |-> NULL]] 
    /\ cluster = [v |-> 0, st |-> "idle"]
    /\ lastVOK = 0 
    /\ reqCounter = 0
    /\ toApply = 0 
    /\ confOK \in BOOLEAN
    /\ lock = FALSE



(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
Submit(r) == \* update request received from the user 
    LET newV == reqCounter + 1 IN
    /\ requests[r].st = "waiting"
    /\ reqCounter' = newV
    /\ requests' = [requests EXCEPT ![r].st = "submitted", ![r].v = newV]
    /\ UNCHANGED <<confOK, lastVOK, toApply, cluster, workers, lock>>


Initialcheck(r) == \* request validation (auth, quotas...)
    /\ requests[r].st = "submitted"
    /\ \E ok \in BOOLEAN: 
        IF ok
            THEN  
                requests' = [requests EXCEPT  ![r].st = "valid"]
            ELSE 
                requests' = [requests EXCEPT  ![r].st = "rejected"]
    /\ UNCHANGED <<confOK, reqCounter, lastVOK, toApply, cluster, workers, lock>>


PushToPending(r) == \* the request is pushed to queue
    /\ requests[r].st = "valid"
    /\ IF toApply < requests[r].v
        THEN /\ toApply' = requests[r].v
             /\ UNCHANGED <<confOK, reqCounter, lastVOK, cluster, requests, workers, lock>>
        ELSE /\ requests' = [requests EXCEPT ![r].st = "rejected"]
             /\ UNCHANGED <<confOK, reqCounter, lastVOK, toApply, cluster, workers, lock>>


SpawnWorker(w) == \* spawns a new worker
    /\ workers[w].st = "waiting"
    /\ toApply /= lastVOK
    /\  \/ cluster.st = "idle"
        \/ cluster.st = "failed"
    /\ workers' = [workers EXCEPT ![w].v = toApply, ![w].st = "starting"]
    /\ lock' = TRUE
    /\ UNCHANGED <<confOK, reqCounter, lastVOK, toApply, requests, cluster>> 
    


ApplyStart(w) == \* the cluster starts to be modified
    /\ workers[w].st = "starting"
    /\ IF workers[w].v >= toApply 
        THEN 
            IF confOK 
                THEN 
                    /\ cluster' = [v |-> workers[w].v, st |-> "partial"]
                    /\ workers' = [workers EXCEPT ![w].st = "working"]
                    /\ UNCHANGED <<confOK, reqCounter, lastVOK, toApply, requests, lock>>
                ELSE 
                    /\ workers' = [workers EXCEPT ![w].st = "waiting", ![w].v = NULL] 
                    /\ UNCHANGED <<confOK, reqCounter, lastVOK, toApply, cluster, requests>>       
        ELSE \* a new version has been submitted, no need to apply this one
            /\ workers' = [workers EXCEPT ![w].st = "waiting", ![w].v = NULL] 
            /\ UNCHANGED <<confOK, reqCounter, lastVOK, toApply, cluster, requests>>
    
    
RollbackVersion == 
    \* to differenciate it from the original last VOK
    lastVOK + 10

ApplyFinish(w) == \* the cluster update finishes
    /\ workers[w].st = "working"
    /\ \E ok \in BOOLEAN : 
        IF ok \/ workers[w].v = RollbackVersion  \* rollback always works
            THEN 
                /\ cluster' =  [cluster EXCEPT !.st = "idle"]
                /\ lastVOK' = workers[w].v
                /\ workers' = [workers EXCEPT ![w].st = "waiting", ![w].v = NULL] 
                /\ UNCHANGED <<confOK, reqCounter, toApply, requests>>
            ELSE
                /\ cluster' =  [cluster EXCEPT !.st = "failed"]
                /\ workers' = [workers EXCEPT ![w].st = "waiting", ![w].v = NULL] 
                /\ IF workers[w].v < toApply
                    THEN \* a newer version has been submitted
                        /\ UNCHANGED <<confOK, reqCounter, lastVOK, toApply, requests>>
                    ELSE \* let's trigger a rollback
                        /\ toApply' = RollbackVersion 
                        /\ UNCHANGED <<confOK, reqCounter, lastVOK, requests>>
            


(***************************************************************************)
(* Requirements                                                            *)
(***************************************************************************)
NoConcurrentUpdate == 
    [](Cardinality({r \in DOMAIN requests: requests[r].st = "working"}) < 2)
    
NoPartialUpdateTermination == \* we don’t want the cluster to end up in a partially update st
    <>[](cluster.st = "idle")

EveryReqIsProcessed ==
    <>[](~\E r \in _Requests: requests[r].st = "waiting")
    
    

(***************************************************************************)
(* Spec                                                                    *)
(***************************************************************************)
Next ==
    \/ \E r \in _Requests : 
            \/ Submit(r) 
            \/ Initialcheck(r) 
            \/ PushToPending(r)
    \/ \E w \in _Workers:
            \/ SpawnWorker(w)
            \/ ApplyStart(w) 
            \/ ApplyFinish(w)


Fairness == \A r \in _Requests, w \in _Workers : 
                /\ WF_vars(Submit(r)) 
                /\ WF_vars(Initialcheck(r)) 
                /\ WF_vars(PushToPending(r))
                /\ WF_vars(SpawnWorker(w)) 
                /\ WF_vars(ApplyStart(w)) 
                /\ WF_vars(ApplyFinish(w))


Spec == 
  /\ Init 
  /\ [][Next]_vars 
  /\ Fairness


THEOREM Spec => [](TypeInvariants)
THEOREM Spec => NoPartialUpdateTermination
=====
