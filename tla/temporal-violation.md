### Note
This is an updated version of the temporal violation, the first description is another violation that can occur if some operations are not atomic (``UpdateSessionStart(n)``).

## Problem 1

In the code snippet below the condiiton ``height[bestBEEFY[n]] >= round[n]`` can violate the temporal property (``BlockEventuallyConfirmed``).

``BlockEventuallyConfirmed == <>\E b \in Blocks : Justified(b) /\ b /= gen``

This temporal property is simply to confirm that the protocol effectively justifies blocks through BEEFY with weak fairness on all actions of honest participants.

```tla
UpdateRound(n) ==
    /\ height[bestBEEFY[n]] >= round[n] 
    /\ castVote[n]
    /\ CalculateRoundNumber(n)
    /\ UNCHANGED <<bestGRANDPA, bestBEEFY, sessionStart, votes, 
                    height, status, parent, epoch>>
```
If we remove the condition ``height[bestBEEFY[n]] >= round[n]`` in ``UpdateRound(n)`` the specification satisifes the liveness property (``BlockEventuallyConfirmed``).

## Rationale

The reason we have included this condition is because of the following description from the [Polkadot Specification](https://spec.polkadot.network/sect-finality#id-consensus-mechanism-beefy-1):

A round is an attempt by BEEFY validators to produce a BEEFY Justification.
Round number is simply defined as a block number the validators are voting for, or to be more precise, the Commitment for that block number.
Round ends when the next round is started, which may happen when one of the events occur:
1. Either the node collects ``2/3 + 1`` valid votes for that round.
2. Or the node receives a BEEFY Justification for a block with heighter greater than the current best BEEFY block.

The condition ``height[bestBEEFY[n]] >= round[n]`` ensures that a node ``n`` only updates its round number if it has seen either:
- A BEEFY Justification for it's current round, or
- a BEEFY Justification for a higher round.

The problem that can arise is that nodes may get stuck in different rounds, preventing the generation of a BEEFY Justification that allows them to update their rounds, ultimately leading to a deadlock.

## Generating the Trace

Running the configuration file listed below (``BEEFYSingleChain.cfg``) on the ``BEEFYSingleChain.tla`` file will highlight the problem when honest nodes are stuck on different rounds (deadlock).

```tla
SPECIFICATION Spec

CONSTANTS
    CNodes = {"c1", "c2", "c3"}
    FNodes = {"f1"}
    N = 4
    T = 1
    Blocks = {"b0", "b1", "b2", "b3"}
    MaxEpoch = 0

INVARIANTS
    ...
    
PROPERTIES 
    BlockEventuallyConfirmed

CHECK_DEADLOCK 
    FALSE
```

One can generate an error trace highlighting why the temporal property is violated.

The easiest way to run the specification ``BEEFYSingleChain.tla`` with the configuration file ``BEEFYSingleChain.cfg`` is to either use the TLA+ Toolbox or use the VSCode extension for TLA+.

The following description is for using the VSCode extension.
By right clicking ``BEEFYSingleChain.tla`` and clicking ``Check model with TLC`` and using the following paramters ``-coverage 1 -workers auto`` it will show an error trace after 17 steps (steps 18 and above is stuttering steps) to highlight how the temporal property is violated.
The ``-workers auto`` input defines how many threads the machine should use when model checking, auto stats that TLC will use all threads on the machine, but it can be any number between 1 and the number of threads (e.g., 24).


## Problem 2 

In the code snippet below, the condition ``height[bestBEEFY[n]] >= round[n]`` can violate the temporal property (``MandatoryBlocksJustified``), which states that every mandatory block must eventually be BEEFY Justified:

``MandatoryBlocksJustified == \A b \in Blocks : ((IsMandatory(b) ~> Justified(b)))``

```tla
UpdateRound(n) ==
    /\ height[bestBEEFY[n]] >= round[n] 
    /\ castVote[n]
    /\ CalculateRoundNumber(n)
    /\ UNCHANGED <<bestGRANDPA, bestBEEFY, sessionStart, votes, 
                    height, status, parent, epoch>>
```
### Cause

This violation occur because we have ``UpdateSessionStart(n)`` as an own subaction of ``Next`` that can take its step whenever it is enabled.
This might not be a realsitic scenario of what the BEEFY implementation actually does in Polkadot.

```tla
FindMandatoryBlock(e) ==
    LET 
        B == {b \in Blocks : epoch[b] > e /\ Finalized(b)}
    IN 
        CHOOSE b \in B : (\A c \in B : height[b] <= height[c])

UpdatesessionStart(n) ==
    LET 
        m == sessionStart[n]
            \* Current mandatory block for node n.
        g == bestGRANDPA[n]
            \* Latest GRANDPA finalized block for node n.
    IN
    /\ Justified(m)
    /\ epoch[g] > epoch[m]
    /\ sessionStart' = [sessionStart EXCEPT ![n] = FindMandatoryBlock(epoch[m])]
    /\ UNCHANGED <<round, bestGRANDPA, bestBEEFY, round, castVote, votes, 
                    height, status, parent, epoch>>
```
