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
const_1587052926513446000 == 
{w1, w2}
----

\* MV CONSTANT definitions _Requests
const_1587052926513447000 == 
{r1, r2, r3}
----

=============================================================================
\* Modification History
\* Created Thu Apr 16 18:02:06 CEST 2020 by matth
