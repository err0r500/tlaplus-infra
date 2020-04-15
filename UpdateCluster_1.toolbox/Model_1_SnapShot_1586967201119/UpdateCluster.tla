---- MODULE UpdateCluster ----
EXTENDS Integers, FiniteSets


CONSTANT  
    Reqs, \* the requests sent by the user
    NULL


VARIABLES 
    queue,
    confOK, \* are we able to get a valid conf ? 
    lastRank, \* last cluster submission rank
    clusterState, \* last cluster fully deployed 
    reqState \* the state of all requests (reqState[req]) 
vars == <<confOK, clusterState, reqState, queue, lastRank>>


NoConcurrentUpdate == 
    Cardinality({r \in DOMAIN reqState: reqState[r].status = "partial"}) < 2


TypeInvariants == 
  /\ confOK \in BOOLEAN \* won't change for a specific behavior
  /\ NoConcurrentUpdate
  /\ \A r \in Reqs : reqState[r].status \in {
    "waiting", \* the request (req) hasn't been submitted yet
    "submitted", \* req has been submitted
    "rejected", \* req has been rejected (auth problem)
    "valid", \* auth etc passed 
    "processing", \* the processing of the req has started
    "partial", \* req is partially applied (the infra is partially modified)
    "partialFailure", \* req failed in the middle of an application
    "success", \* req has been sucessfully applied
    "failure", \* the req failed before modifying the cluster
    "rolledback" \* the req has been rolledback
    }



(***************************************************************************)
(* Initial State                                                           *)
(***************************************************************************)
Init == 
    /\ reqState = [r \in Reqs |-> [status |-> "waiting", rank |-> NULL]]
    /\ clusterState = [req |-> NULL, complete |-> TRUE] 
    /\ lastRank = 0
    /\ confOK \in BOOLEAN
    /\ queue = {}



(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)
Submit(r) == \* update request received from the user 
    LET currSubmitRank == lastRank + 1 IN
    /\ reqState[r].status = "waiting"
    /\ lastRank' = currSubmitRank
    /\ reqState' = [reqState EXCEPT ![r].status = "submitted", ![r].rank = currSubmitRank]
    /\ UNCHANGED <<confOK, queue, clusterState>>


Initialcheck(r) == \* request validation (auth, quotas...)
    /\ reqState[r].status = "submitted"
    /\ \E ok \in BOOLEAN: 
        IF ok
            THEN  
                reqState' = [reqState EXCEPT  ![r].status = "valid"]
            ELSE 
                reqState' = [reqState EXCEPT  ![r].status = "rejected"]
    /\ UNCHANGED <<confOK, queue, clusterState, lastRank>> 


PushToQueue(r) == \* the request is pushed to queue
    /\ reqState[r].status = "valid"
    /\ queue' = queue \union {r} 
    /\ UNCHANGED <<confOK, reqState, clusterState, lastRank>> 


ProcessQueue ==  \* a request in queue is processed (order of submission not took into account)
    /\ queue /= {}
    /\ \E r \in queue :
        /\ queue' = queue \ {r}
        /\ reqState' =  [reqState EXCEPT ![r].status = "processing"]
        /\ UNCHANGED <<confOK, clusterState, lastRank>> 


StartApply(r) == \* the cluster starts to be modified
    /\ reqState[r].rank = lastRank
    /\ reqState[r].status = "processing"
    /\ clusterState.complete = TRUE
    /\ ~\E x \in DOMAIN reqState: reqState[x].status = "partial" \* don't attempt if an attempt is already on-going
    /\ IF confOK 
        THEN 
            /\ reqState' = [reqState EXCEPT ![r].status = "partial"] 
            /\ clusterState' = [req |-> r, complete |-> FALSE]
            /\ UNCHANGED <<confOK, lastRank, queue>> 
        ELSE 
            /\ reqState' = [reqState EXCEPT ![r].status = "failure"]
            /\ UNCHANGED <<confOK, clusterState, lastRank, queue>> 


CompleteApply(r) == \* the cluster update finishes
    /\ reqState[r].status = "partial"
    /\ \E ok \in BOOLEAN : 
        IF ok 
            THEN 
                /\ reqState' = [reqState EXCEPT ![r].status = "success"] 
                /\ clusterState' =  [clusterState EXCEPT !.req = r, !.complete = TRUE]
                /\ UNCHANGED <<confOK, lastRank, queue>> 
            ELSE
                /\ reqState' = [reqState EXCEPT ![r].status = "partialFailure"] 
                /\ UNCHANGED <<confOK, clusterState, lastRank, queue>> 


Rollback(r) == \*we assume rollback always works if confOK (ie we shouldn’t have to rollback if conf not OK )
    /\ reqState[r ].status = "partialFailure"
    /\ IF confOK
        THEN
            /\ reqState' = [reqState EXCEPT ![r].status = "rolledback"]
            /\ clusterState' = [clusterState EXCEPT !.complete = TRUE]
            /\ UNCHANGED <<confOK , lastRank , queue>>
        ELSE
            UNCHANGED vars
            
            
            
(***************************************************************************)
(* Requirements                                                            *)
(***************************************************************************)
NoPartialUpdateTermination == \* we don’t want the cluster to end up in a partially update state
    <>[](clusterState.complete = TRUE)
    
    
NoApplicationOfOutdatedReq == \* we don’t want transition updates of successive requests
    []({r \in DOMAIN reqState: ENABLED StartApply(r) /\ reqState[r].rank /= lastRank} = {})
    
    
EveryReqInQueueIsProcessed == \* we don’t want messages to stay in queue
    <>[](queue = {})



(***************************************************************************)
(* Spec                                                                    *)
(***************************************************************************)
Fairness == 
    \A r \in Reqs : 
        /\ WF_vars(PushToQueue(r))
        /\ WF_vars(ProcessQueue)
        /\ WF_vars(CompleteApply(r))
        /\ WF_vars(Rollback(r))
        
        
Next == 
    ProcessQueue \/ 
    \E r \in Reqs : 
        \/ Submit(r) \/ Initialcheck(r)
        \/ PushToQueue(r)
        \/ StartApply(r) \/ CompleteApply(r)
        \/ Rollback(r)


Spec == 
  /\ Init /\ [][Next]_vars /\ Fairness


THEOREM Spec => [](TypeInvariants)
THEOREM Spec => NoPartialUpdateTermination
THEOREM Spec => NoApplicationOfOutdatedReq
THEOREM Spec => EveryReqInQueueIsProcessed

=====
