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
const_15894665920572000 == 
{w1, w2}
----

\* MV CONSTANT definitions _Requests
const_15894665920573000 == 
{r1, r2, r3}
----

=============================================================================
\* Modification History
\* Created Thu May 14 16:29:52 CEST 2020 by matth
