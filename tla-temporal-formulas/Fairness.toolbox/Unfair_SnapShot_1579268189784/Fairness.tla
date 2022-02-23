------------------------------- MODULE Fairness -------------------------------
\* 
\* Strong and weak fairness illustrated through a simple example of a reliable vs. lossy message channel
\* between a sender and receiver.
\*

\* The message to send.
CONSTANT msg

\* The inbox of the receiver. Sending a message places it here.
VARIABLE inbox

\* Boolean indicating whether the receiver has processed the incoming message yet.
VARIABLE rcvd

Init == 
    /\ rcvd = FALSE
    /\ inbox = {}
    
Send == 
    /\ inbox = {}
    /\ inbox' = {msg} 
    /\ UNCHANGED rcvd
    
Recv == 
    /\ inbox = {msg}
    /\ inbox' = {}
    /\ rcvd = TRUE

DropMsg == 
    /\ inbox = {msg}
    /\ inbox' = {}
    /\ UNCHANGED rcvd  

Next == 
    \/ Send
    \/ Recv

SpecUnfair == Init /\ [][Next]_<<inbox, rcvd>>

\* Is the message eventually received.
MessageReceived == <>(rcvd)


================================================================================
\* Modification History
\* Last modified Fri Jan 17 08:35:25 EST 2020 by williamschultz
\* Created Fri Jan 17 08:28:30 EST 2020 by williamschultz
