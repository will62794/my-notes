------------------------------ MODULE MinuteClock ------------------------------
EXTENDS Naturals

\* Models a clock with minute level accuracy.

VARIABLE hour
VARIABLE minute

Init == 
    /\ hour = 0
    /\ minute = 0

Next == 
    /\ minute' = (minute + 1) % 60
    /\ hour' = IF minute = 59 THEN (hour + 1) % 12 ELSE hour

Spec == Init /\ [][Next]_<<hour, minute>>

V == INSTANCE HourClock WITH hour <- hour

IsRefinement == V!Spec

THEOREM Spec => V!Spec

================================================================================
\* Modification History
\* Last modified Sat Sep 14 09:25:28 CDT 2019 by williamschultz
\* Created Sat Sep 14 09:07:06 CDT 2019 by williamschultz
