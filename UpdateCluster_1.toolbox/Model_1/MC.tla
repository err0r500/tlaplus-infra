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
const_159110641192926000 == 
{w1, w2}
----

\* MV CONSTANT definitions _Requests
const_159110641192927000 == 
{r1, r2, r3}
----

=============================================================================
\* Modification History
\* Created Tue Jun 02 16:00:11 CEST 2020 by matth
