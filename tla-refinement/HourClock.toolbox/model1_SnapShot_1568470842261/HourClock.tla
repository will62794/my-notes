------------------------------ MODULE HourClock ------------------------------
EXTENDS Naturals

VARIABLE hour

Init == hour = 0

Next == hour' = (hour + 1) % 12

Spec == Init /\ [][Next]_hour

================================================================================
\* Modification History
\* Last modified Sat Sep 14 09:20:12 CDT 2019 by williamschultz
\* Created Sat Sep 14 09:05:57 CDT 2019 by williamschultz
