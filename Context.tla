---------------------- MODULE Context ----------------------
(* Set of contexts that can be either linked or cancelled. *)
CONSTANTS Contexts

VARIABLES 
    (* A reflexive binary relation that is true iff first context does influenced on a second directly or indirectly. *)
    (* If true, cancellation of a parent context must eventually imply cancellation of a child (influencedd) context. *)
    influenced, 
    isCancelled
    
vars == <<influenced, isCancelled>>

Cancel(context) == 
    (* Cancels given context. It isn't revertable: once cancelled, context stays so forever. *)
    /\ isCancelled[context] = FALSE
    /\ isCancelled' = [isCancelled EXCEPT ![context] = TRUE] 
    /\ UNCHANGED influenced   

Link(parentContext, childContext) ==
    (* Links given contexts such that cancellation of the parent must lead to cancellation of the child. *)
    (* Note that due to async nature of cancellation, child may get cancelled before it's parent did. *)
    /\ isCancelled[parentContext] = FALSE
    /\ isCancelled[childContext] = FALSE
    /\ influenced[parentContext, childContext] = FALSE
    /\ influenced[childContext, parentContext] = FALSE
    /\ influenced' = [influenced EXCEPT ![parentContext, childContext] = TRUE]
    /\ UNCHANGED isCancelled

Init ==
    /\ influenced = [parentContext, childContext \in Contexts |-> parentContext = childContext]
    /\ isCancelled = [context \in Contexts |-> FALSE]

Next ==
    \/ \E context \in Contexts:
        Cancel(context)
    \/ \E parentContext, childContext \in Contexts:
        Link(parentContext, childContext)
    \/  (* Once neither Cancel nor Link are possible, system just stays in the same state forever. *)
        (* Not sure why is it here and why stuttering steps are insufficient to avoid deadlock? *)
        /\ UNCHANGED influenced 
        /\ UNCHANGED isCancelled
           
Spec == 
    /\ Init 
    /\ [][Next]_vars 
    /\ SF_vars(\E context \in Contexts: Cancel(context))
------------------------------------------------------------            
THEOREM 
    (* Once parent context is cancelled, eventually, all reachable childs contexts will be cancelled too. *)
    (* It's fine for child contexts to get cancelled before their parent did. *)
    \E parentContext \in Contexts: isCancelled[parentContext] ~> 
        \A childContext \in { childContext \in Contexts: influenced[parentContext, childContext] }: 
            isCancelled[childContext]
============================================================