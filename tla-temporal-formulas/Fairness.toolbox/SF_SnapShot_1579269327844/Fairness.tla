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

vars == <<inbox, rcvd>>

Init == 
    /\ rcvd = FALSE
    /\ inbox = {}

\* Send a message.    
Send == 
    /\ inbox = {}
    /\ inbox' = {msg} 
    /\ UNCHANGED rcvd
  
\* Receive a message.  
Recv == 
    /\ inbox = {msg}
    /\ inbox' = {}
    /\ rcvd' = TRUE

\* Simulate dropping a message.
DropMsg == 
    /\ inbox = {msg}
    /\ inbox' = {}
    /\ UNCHANGED rcvd  

Next == 
    \/ Send
    \/ Recv

NextLossy == 
    \/ Send
    \/ Recv
    \/ DropMsg

\* Reliable channel.
Spec == Init /\ [][Next]_vars

\* Lossy channel.
SpecLossy == Init /\ [][NextLossy]_vars

\* Weak fairness property.
WeakFair == WF_vars(Next)

\* Strong fairness property.
StrongFair ==
    /\ WF_vars(Send)
    /\ WF_vars(Recv)
    /\ SF_vars(DropMsg)

NextEnabledInfinitelyOften == []<>(ENABLED (Next /\ vars' # vars))

\* Is the message eventually received.
MessageReceived == <>(rcvd)


================================================================================
\* Modification History
\* Last modified Fri Jan 17 08:55:19 EST 2020 by williamschultz
\* Created Fri Jan 17 08:28:30 EST 2020 by williamschultz
