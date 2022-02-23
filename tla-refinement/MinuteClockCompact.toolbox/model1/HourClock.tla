------------------------------ MODULE HourClock ------------------------------
EXTENDS Naturals

\* Models a clock with hour precision.

VARIABLE hour

Init == 
    /\ hour = 0

Next == 
    /\ hour' = (hour + 1) % 12

Spec == Init /\ [][Next]_hour

================================================================================
\* Modification History
\* Last modified Sat Sep 14 09:28:15 CDT 2019 by williamschultz
\* Created Sat Sep 14 09:05:57 CDT 2019 by williamschultz
