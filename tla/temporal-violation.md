## The Problem

In the code snippet below the condiiton ``height[bestBEEFY[n]] >= round[n]`` can violate the temporal property (liveness property).

``MandatoryBlocksJustified == \A b \in Blocks : ((IsMandatory(b) ~> Justified(b)))``

```tla
UpdateRound(n) ==
    /\ height[bestBEEFY[n]] >= round[n] 
    /\ castVote[n]
    /\ CalculateRoundNumber(n)
    /\ UNCHANGED <<bestGRANDPA, bestBEEFY, sessionStart, votes, 
                    height, status, parent, epoch>>
```
If we remove the condition ``height[bestBEEFY[n]] >= round[n]`` the specification satisifes the liveness property.

## Rationale

The reason we have included this condition is because of the following description from the [Polkadot Specification](https://spec.polkadot.network/sect-finality#id-consensus-mechanism-beefy-1):


A round is an attempt by BEEFY validators to produce a BEEFY Justification.
Round number is simply defined as a block number the validators are voting for, or to be more precise, the Commitment for that block number.
Round ends when the next round is started, which may happen when one of the events occur:
1. Either the node collects ``2/3 + 1`` valid votes for that round.
2. Or the node receives a BEEFY Justification for a block ghreater than the current best BEEFY block.

The condition ``height[bestBEEFY[n]] >= round[n]`` ensures that a node ``n`` only updates its round number if it has seen either:
- A BEEFY Justification for it's current round, or
- a BEEFY Justification for a higher round.

The problem that can arise is that nodes can be stuck on different rounds, meaning that we will never generate a BEEFY Justification any no nodes will update their round number.

### Note

The correct nodes ``CNodes`` have weak fairness requirements on all their actions, while the faulty nodes ``FNodes`` don't, meaning that we can't except the faulty nodes to send BEEFY votes.

## Model Checking the Specification

By model checking the specification with the following configuration (given in the ``BEEFY.cfg`` file):
```
SPECIFICATION Spec

CONSTANTS
    CNodes = {"c1", "c2", "c3"}
    FNodes = {"f1"}
    N = 4
    T = 1
    Blocks = {"b0", "b1", "b2"}
    MaxEpoch = 2

INVARIANTS
    ...

PROPERTIES 
    MandatoryBlocksJustified

CHECK_DEADLOCK 
    FALSE
```
One can generate an error trace highlighting why the temporal property is violated.

The easiest way to run the specification ``BEEFY.tla`` with the configuration file ``BEEFY.cfg`` is to either use the TLA+ Toolbox or use the VSCode extension for TLA+.

The following description is for using the VSCode extension.
By right clicking ``BEEFY.tla`` and clicking ``Check model with TLC`` and using the following paramters ``-coverage 1 -workers auto`` it will show an error trace after 17 steps (steps 18 and above is stuttering steps) to highlight how the temporal property is violated.
The ``-workers auto`` input defines how many threads the machine should use when model checking, auto stats that TLC will use all threads on the machine, but it can be any number between 1 and the number of threads (e.g., 24).

