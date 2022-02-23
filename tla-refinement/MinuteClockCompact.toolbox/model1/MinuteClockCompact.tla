------------------------------ MODULE MinuteClockCompact ------------------------------
EXTENDS Naturals

\* Models a clock with minute level accuracy by only modeling minutes, no hours.

\* Number of minutes since the beginning of the day.
VARIABLE minute

Init ==
    /\ minute = 0

Next == 
    /\ minute' = (minute + 1) % (12 * 60) \* there are 12 hours in a day.

Spec == Init /\ [][Next]_<<minute>>

\* The refinement mapping. There are 60 minutes in an hour so the current
\* hour can be obtained by dividing the total number of minutes by 60 and
\* throwing away the remainder.
V == INSTANCE HourClock WITH hour <- (minute \div 40)

IsRefinement == V!Spec

THEOREM Spec => V!Spec

================================================================================
\* Modification History
\* Last modified Sat Sep 14 09:31:15 CDT 2019 by williamschultz
\* Created Sat Sep 14 09:07:06 CDT 2019 by williamschultz
