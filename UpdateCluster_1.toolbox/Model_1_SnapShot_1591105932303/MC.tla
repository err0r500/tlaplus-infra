---- MODULE MC ----
EXTENDS UpdateCluster, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
w1, w2
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
----

\* MV CONSTANT definitions _Workers
const_15911059278148000 == 
{w1, w2}
----

\* MV CONSTANT definitions _Requests
const_15911059278149000 == 
{r1, r2, r3}
----

=============================================================================
\* Modification History
\* Created Tue Jun 02 15:52:07 CEST 2020 by matth
