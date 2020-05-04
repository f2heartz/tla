---- MODULE LinkedListCycleDetection ----
EXTENDS 
    Naturals
----
CONSTANTS 
    (* Some positive Nat that limits linked list's length. *)
    Len

ASSUME  
    /\ Len > 0
    /\ Len \in Nat
----
VARIABLES 
    (* Both i, j are 1-based indexes that point to some linked list's node. *)
    i,
    j,
    (* A global counter of moves made so far. *)
    movesCounter,
    (* Represents a cycled linked lists. *)
    nextLinkIndex

vars == <<i, j, movesCounter, nextLinkIndex>>
----
Init == 
    /\ i = 1
    /\ j = 1
    /\ movesCounter = 0
    (* The nextLinkIndex function won't change: last node is linked to the first node *)
    (* and that's why linked list is cycled. Yet we can't have it as constant *)
    (* because Len could be arbitrary natural number. *)
    /\ nextLinkIndex = [currentLinkIndex \in 1..Len |-> IF currentLinkIndex = Len THEN 1 ELSE currentLinkIndex + 1]
----
Step ==
    /\ movesCounter' = movesCounter + 1
    (* Essence of the algorithm: while i steps one node forward, j does two-nodes step. *)
    (* If given linked list is cycled indeed - which is guaranteed by the nextLinkIndex - *)
    (* eventually both indexes will appear on the same node. *)
    /\ i' = nextLinkIndex[i]
    /\ j' = nextLinkIndex[nextLinkIndex[j]]

CycleDetected == 
    (* Once cycle is detected, nothing happens. Algorithm considered terminated. *)
    /\ movesCounter > 0
    /\ i = j

Continue ==
    /\ ~CycleDetected
    /\ Step
    /\ UNCHANGED nextLinkIndex

Next == 
    \/ Continue
    \/ 
        /\ CycleDetected
        /\ UNCHANGED vars
----
Spec == Init /\ [][Next]_vars /\ SF_vars(Continue)
----
TypeOK ==
    /\ i \in 1..Len
    /\ j \in 1..Len
    /\ movesCounter \in Nat

THEOREM Spec => []TypeOK

CycleEventuallyDetected == ~CycleDetected ~> []CycleDetected
THEOREM Spec => CycleEventuallyDetected
====
