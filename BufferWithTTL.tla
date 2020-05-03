---- MODULE BufferWithTTL ----
EXTENDS Naturals

CONSTANTS 
    (* Set of items that can be buffered. *)
    Items, 
    (* Since Nat is infinite, it makes sense to bound time for practical reasons. *)
    Time,
    (* Time to live for buffered items. *)
    TTL

ASSUME 
    /\ Items /= {}
    /\ Time \in SUBSET Nat
    /\ TTL > 0

VARIABLES 
    (* Represents how many time units ticked since the begining. *)
    currentTime,
    (* Set of ordered pairs, where first element is an item and second element is a time when it was put in the buffer. *)
    buffer

vars == <<currentTime, buffer>>
----
Init == 
    /\ currentTime = CHOOSE x \in Time: \A y \in Time: x =< y
    /\ buffer = {}
----
RefreshedBuffer == {item \in buffer: currentTime' - item[2] =< TTL}

Tick == 
    /\ currentTime' = currentTime + 1
    /\ currentTime' \in Time

NoItem == 
    /\ Tick  
    /\ buffer' = RefreshedBuffer

Push(item) ==
    /\ Tick
    /\ buffer' = RefreshedBuffer \union {<<item, currentTime'>>}

PushSomeItem == \E item \in Items: Push(item)

Next == NoItem \/ PushSomeItem
----
Spec == Init /\ [][Next]_vars
----
TypeOK == 
    /\ currentTime \in Time
    /\ buffer \in SUBSET (Items \X Time)
THEOREM Spec => []TypeOK
----
BufferObeysTimelimit == \A item \in buffer: currentTime - item[2] =< TTL
THEOREM Spec => []BufferObeysTimelimit
====