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
const_1587050257578404000 == 
{w1, w2}
----

\* MV CONSTANT definitions _Requests
const_1587050257578405000 == 
{r1, r2, r3}
----

=============================================================================
\* Modification History
\* Created Thu Apr 16 17:17:37 CEST 2020 by matth
