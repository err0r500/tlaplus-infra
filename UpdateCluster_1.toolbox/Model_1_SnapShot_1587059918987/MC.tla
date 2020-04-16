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
const_1587059914970530000 == 
{w1, w2}
----

\* MV CONSTANT definitions _Requests
const_1587059914970531000 == 
{r1, r2, r3}
----

=============================================================================
\* Modification History
\* Created Thu Apr 16 19:58:34 CEST 2020 by matth