---------------------------------------------------- MODULE CDCGenManage ----------------------------------------------------
EXTENDS Integers, Naturals

CONSTANTS Node

VARIABLES
    commonSeed,
    knows, \* b \in knows[a] when a chooses a timestamp => a's generation will include b's tokens
    promisesSent,
    promisesRcvd,
    maxTsRcvd,
    chosenTs,
    crashed
vars == <<commonSeed, knows, promisesSent, promisesRcvd, maxTsRcvd, chosenTs, crashed>>

PromiseMsg   == [from: Node, to: Node, known: SUBSET Node, ts: Nat \cup {-1}]

TypeOK ==
    /\ commonSeed \in Node
    /\ knows \in [Node -> SUBSET Node]
    /\ promisesSent \in SUBSET PromiseMsg
    /\ promisesRcvd \in [Node -> SUBSET Node]
    /\ maxTsRcvd \in [Node -> Nat \cup {-1}]
    /\ chosenTs \in [Node -> Nat \cup {-1}]
    /\ crashed \in SUBSET Node

\* A can learn about B from any source: gossip, config, by receiving a promise request... we don't care.
Learn(a, b) ==
    /\ knows' = [knows EXCEPT ![a] = knows[a] \cup {b}]
    /\ UNCHANGED <<commonSeed, promisesSent, promisesRcvd, maxTsRcvd, chosenTs, crashed>>

\* A sends a promise to B after receiving a promise request.
\* We don't include request sending into the spec so that the number of states doesn't grow unnecessarily.
\* We instead include preconditions here that need to be true on B for it to have sent the request.
SendPromise(a, b) ==
    \* To send the promise, A must have received a request from B => it knows B.
    /\ b \in knows[a]

    \* The following three preconditions need to be true so that B could have sent the request.
    \* In reality, at the moment of receiving and processing the request on A, they might not be true
    \* because of B crashing; but in this case, we will send our answer over a connection that doesn't exist anymore,
    \* so it's as if we never send it. The model doesn't need to handle this. Also see Forget(a), where we
    \* delete all messages {p \in promisesSent: p.to = a} when node `a` crashes.

    \* The requester must have known us to send the promise request:
    /\ a \in knows[b]
    \* Nodes don't send requests after they have chosen a timestamp.
    \* We also know that B won't choose its timestamp until it receives our message
    \* (see the NoInFlightPromises invariant).
    /\ chosenTs[b] = -1
    \* Nodes don't send requests to nodes that they have already contacted.
    \* We also know that B won't add us to promisesRcvd until it receives our message
    \* (see NoInFlightPromises).
    /\ ~ a \in promisesRcvd[b]

    \* In an implementation we might as well send many promises,
    \* but the requester will handle only one of them, so we don't need to remember them all in the model:
    /\ ~ \E p \in promisesSent: p.from = a /\ p.to = b

    /\ promisesSent' = promisesSent \cup {[from |-> a, to |-> b, known |-> knows[a], ts |-> chosenTs[a]]}
    /\ UNCHANGED <<commonSeed, knows, promisesRcvd, maxTsRcvd, chosenTs, crashed>>

max(a, b) == IF a > b THEN a ELSE b

ReceivePromise(a) ==
    /\ \E p \in promisesSent:
        /\ p.to = a
        /\ promisesSent' = promisesSent \ {p}
        /\ promisesRcvd' = [promisesRcvd EXCEPT ![a] = promisesRcvd[a] \cup {p.from}]
        /\ knows' = [knows EXCEPT ![a] = knows[a] \cup p.known]
        /\ maxTsRcvd' = [maxTsRcvd EXCEPT ![a] = max(maxTsRcvd[a], p.ts)]
    /\ UNCHANGED <<commonSeed, chosenTs, crashed>>

ChooseTs(a) ==
    /\ chosenTs[a] = -1
    /\ knows[a] \subseteq promisesRcvd[a]
    /\ chosenTs' = [chosenTs EXCEPT ![a] = maxTsRcvd[a] + 1]
    /\ UNCHANGED <<commonSeed, knows, promisesSent, promisesRcvd, maxTsRcvd, crashed>>

Forget(a) ==
    \* We allow every node to crash at most once so that model checking is viable.
    /\ ~ a \in crashed
    /\ crashed' = crashed \cup {a}

    \* Even if they are in-flight messages for us, no one will be there to receive them.
    /\ promisesSent' = promisesSent \ {p \in promisesSent: p.to = a}

    \* Forget everything except known[a], which will be persisted on disk.
    /\ promisesRcvd' = [promisesRcvd EXCEPT ![a] = {a}]
    /\ maxTsRcvd' = [maxTsRcvd EXCEPT ![a] = -1]
    /\ chosenTs' = [chosenTs EXCEPT ![a] = -1]
    /\ UNCHANGED <<commonSeed, knows>>

Init ==
    \* We assume that there is at least one common node known to everyone (by config): commonSeed.
    /\ \E x \in Node: commonSeed = x
    /\ knows = [a \in Node |-> {a} \cup {commonSeed}]
    /\ crashed = {}
    /\ promisesSent = {}
    /\ promisesRcvd = [a \in Node |-> {a}]
    /\ maxTsRcvd = [a \in Node |-> -1]
    /\ chosenTs = [a \in Node |-> -1]

NextNoForget ==
    \/ \E a, b \in Node: Learn(a, b)
    \/ \E a, b \in Node: SendPromise(a, b)
    \/ \E a \in Node: ReceivePromise(a)
    \/ \E a \in Node: ChooseTs(a)

NextSingleForget ==
    \/ NextNoForget
    \/ /\ crashed = {}
       /\ \E a \in Node: Forget(a)

Next ==
    \/ NextNoForget
    \/ \E a \in Node: Forget(a)
        
Spec == Init /\ [][Next]_vars

Inv ==
    LET AllChosen == {a \in Node: chosenTs[a] /= -1}
        MaxChosen == {a \in AllChosen: \A b \in AllChosen: chosenTs[a] >= chosenTs[b]}
     IN \A a \in MaxChosen: AllChosen \subseteq knows[a]

NoInFlightPromises ==
    /\ \A a \in Node: chosenTs[a] /= -1 => ~ \E p \in promisesSent: p.to = a
    /\ \A a, b \in Node: a \in promisesRcvd[b] => ~ \E p \in promisesSent: p.from = a /\ p.to = b

THEOREM Correctness == Spec => [](TypeOK /\ Inv /\ NoInFlightPromises)
 
=============================================================================================================================
