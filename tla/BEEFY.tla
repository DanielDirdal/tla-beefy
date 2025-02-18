------------------------------- MODULE BEEFY -------------------------------
EXTENDS Integers, FiniteSets, TLC, BEEFY_typedefs 

(***************************************************************************)
(* PROTOCOL PARAMETERS                                                     *)
(***************************************************************************)
CONSTANTS
    \* The set of correct nodes.
    \* @type: Set($node);
    CNodes,
    \* Set of Byzantine nodes, may be empty (unknown to nodes).
    \* @type: Set($node);
    FNodes,
    \* Total number of voters, correct and Byzantine.
    \* @type: Int;
    N,
    \* An upper bound of the number of faulty voters.
    \* @type: Int;
    T,
    \* Set of unique blocks.
    \* @type: Set($node);
    Blocks,
    \* The maximum number of epochs, which we bound for model checking.
    \* @type: Int;
    MaxEpoch

(***************************************************************************)
(* Definitions                                                             *)
(***************************************************************************)
\* The set of all nodes (Honest and Byzantine combined).
Nodes == CNodes \cup FNodes

\* Blocks not associated with an round start with height set to -1.
\* Note: Nodes use the principle of round while block have height and slot.
\* Round corresponds to a block with that height (can be multiple block with)
\* the same height). Height and round is used interchangeably.
\* @type: Set($height);
Heights == -1..(Cardinality(Blocks)-1)

\* Each block b in Blocks must also have an associated epoch.
\* There can be multiple blocks with the same epoch and there can exists
\* skipped epochs (if there was no proposed block with that or those epochs).
\* Usually a block has an associated slot that corresponds to an epoch, but
\* we abstract away slots and only look at epochs, this makes it possible to 
\* not care about how many slots an epoch should last.
\* @type: Set($epoch);
Epochs == -1..MaxEpoch

(***************************************************************************)
(* Assume Statements                                                       *)
(***************************************************************************)

\* Assume N = 3f + 1 where f is maximal amount of faulty nodes (Byzantine).
\* Assume the total number of nodes equals the cardinaity of set of all nodes.
ASSUME N = Cardinality(CNodes \cup FNodes)

\* One would probably expect that we assume Cardinality(FNodes) <= T but we
\* don't use that assumption because we often want to verify that the abstract
\* program actually breaks the invariants when the number of faulty nodes goes
\* over the bound T.

\* Assume there exists blocks.
ASSUME Blocks /= {}

\* If there exists blocks we get a determinsitic genesis block.
\* @type: () => $block;
gen == CHOOSE b \in Blocks : TRUE

(***************************************************************************)
(* Protocol State Variables                                                *)
(* Based on the Polkadot specifications and BEEFY paper:                   *)
(*  - https://spec.polkadot.network/sect-finality#sect-grandpa-beefy       *)
(*  - https://eprint.iacr.org/2025/057.pdf                                 *)
(***************************************************************************)
VARIABLES
    \* The round number of a node ($r$ in the spec).
    \* The round number corresponds to a block height.
    \* @type: $node -> $height;
    round,
    \* A node's view of best BEEFY block ($best_beefy$ in the spec).
    \* @type: $node -> $block;
    bestBEEFY,
    \* A node's view of best GRANDPA block ($best_grandpa$ in the spec).
    \* @type: $node -> $block;
    bestGRANDPA,
    \* A node's view of when a new session/epoch starts, it must be the first
    \* first finalized block in an epoch ($session_start$ in the spec).
    \* These blocks are mandatory (they must receive a BEEFY Justification).
    \* @type: $node -> $block;
    sessionStart,
    \* Indicate if a node has cast a vote for its round.
    \* FALSE for not cast a vote and TRUE for cast a vote.
    \* @type: $node -> Bool;
    castVote,
    \* Set of votes for a block, mapping of block to set of votes.
    \* @type: $block -> Set($node);
    votes,
    \* Height of a block, mapping of block to height.
    \* @type: $block -> $height;
    height,
    \* Blocks parent block, mapping of block to block.
    \* @type: $block -> $block;
    parent,
    \* The block status, mapping of block to "Available" or "Finalized".
    \* @type: $block -> $status;
    status,
    \* The blocks epoch number, mapping of block to epoch.
    \* @type: $block -> $epoch;
    epoch

\* Tuple of all the variables
vars == <<round, bestBEEFY, bestGRANDPA, sessionStart, castVote, votes, 
          height, status, parent, epoch>>

(***************************************************************************)
(* The type invariant                                                      *)
(***************************************************************************)
TypeOK ==
    /\ round \in [CNodes -> Heights]
    /\ bestBEEFY \in [CNodes -> Blocks]
    /\ bestGRANDPA \in [CNodes -> Blocks]
    /\ sessionStart \in [CNodes -> Blocks]
    /\ castVote \in [CNodes -> BOOLEAN]
    /\ votes \in [Blocks -> SUBSET Nodes]
    /\ height \in [Blocks -> Heights]
    /\ status \in [Blocks -> {"Available", "Finalized"}]
    /\ parent \in [Blocks -> Blocks]
    /\ epoch \in [Blocks -> Epochs]

(***************************************************************************)
(* Note: Uppercase always indicate that it is a set (if a set uses both, it*)
(* will be obvious from context).                                          *)
(***************************************************************************)

(***************************************************************************)
(* Init                                                                    *)
(*  - Node's start in round 0 (height 0)                                   *)
(*  - Nodes have bestBEEFY, bestGRANDPA, and sessionStart as the genesis   *)
(*    block.                                                               *)
(*  - Initially all blocks but genesis have height -1 (Genesis have 0).    *)
(*  - Since all node's start in round 0 and have already cast a vote.      *)
(*  - No block is voted for, except genesis.                               *)
(*  - All nodes voted for the genesis block.                               *)
(*  - All blocks are their own parent.                                     *)
(*  - All blocks have their epoch set to -1 except genesis block (epoch 0).*)
(***************************************************************************)
Init ==
    \* Nodes
    /\ round = [n \in CNodes |-> 0]
    /\ bestBEEFY = [n \in CNodes |-> gen]
    /\ bestGRANDPA = [n \in CNodes |-> gen]
    /\ sessionStart = [n \in CNodes |-> gen]
    /\ castVote = [n \in CNodes |-> TRUE]
    \* Blocks
    /\ height = [[b \in Blocks |-> -1] EXCEPT ![gen]=0]
    /\ status = [[b \in Blocks |-> "Available"] EXCEPT ![gen]="Finalized"]
    /\ parent = [b \in Blocks |-> b]
    /\ epoch = [[b \in Blocks |-> -1] EXCEPT ![gen]=0]
    /\ votes = [[b \in Blocks |-> {}] EXCEPT ![gen]=Nodes]

(***************************************************************************)
(* To reduce the state space and improve running time, we initialize the   *)
(* protocol with faulty voters in the initial state.                       *)
(*  - Allowing faulty voters to cast votes at any point significantly      *)
(*    increases the state space, making verification more difficult.       *)
(*  - By starting with faulty voters already present in the initial state, *)
(*    we can reduce the amount of next actions the specifications can take *)
(*    by instead increasing the amount of initial states.                  *) 
(* Inspired by:                                                            *)
(* https://protocols-made-fun.com/specification/modelchecking/tlaplus/apalache/2024/11/03/ben-or.html *)
(***************************************************************************)
InitWithFaults == 
    \* Nodes
    /\ round = [n \in CNodes |-> 0]
    /\ bestBEEFY = [n \in CNodes |-> gen]
    /\ bestGRANDPA = [n \in CNodes |-> gen]
    /\ sessionStart = [n \in CNodes |-> gen]
    /\ castVote = [n \in CNodes |-> TRUE]
    \* Blocks
    /\ height = [[b \in Blocks |-> -1] EXCEPT ![gen]=0]
    /\ status = [[b \in Blocks |-> "Available"] EXCEPT ![gen]="Finalized"]
    /\ parent = [b \in Blocks |-> b]
    /\ epoch = [[b \in Blocks |-> -1] EXCEPT ![gen]=0]
    \* non-deterministically initialize the votes for blocks with faults
    /\ \E F \in SUBSET [n: FNodes, b: Blocks] :
        votes = [b \in Blocks |->
            IF b = gen THEN 
                Nodes
            ELSE 
                {f \in FNodes : (\E m \in F : m.n = f /\ m.b = b)}]

(***************************************************************************)
(* A block b is proposed if and only if:                                   *)
(*  - A block is considered proposed if it is part of the chain, meaning   *)
(*    it has been assigned a valid height (height[b] > -1).                *)
(***************************************************************************)
Proposed(b) == 
    /\ b \in Blocks
    /\ height[b] > -1

(***************************************************************************)
(* A block p is a valid parent for a block with height h and epoch e iff:  *)
(*  - The parent block p has already been proposed (height[b] > -1).       *)
(*  - The parent block's height is exactly one less than h.                *)
(*  - Parent block p epoch is less or equal to proposed block epoch e.     *)
(***************************************************************************)
(* Note:                                                                   *)
(*  - It is also possible that all blocks belong to the same epoch 0.      *)
(*  - There can be skipped epochs (e.g., 0 -> 0 -> 1 -> 3 -> 3).           *)
(***************************************************************************)
ValidParent(p, h, e) == 
    /\ Proposed(p)
    /\ h = height[p] + 1
    /\ epoch[p] <= e

(***************************************************************************)
(* Propose block b with parent p and height h in epoch e if:               *)
(*  - Block b is not the same as parent block p (b != p).                  *)
(*  - Block b is not already proposed (height[b] <= -1).                   *)
(*  - The parent block p is valid.                                         *)
(***************************************************************************)
propose(b, p, h, e) ==
    /\ height' = [height EXCEPT ![b] = h]
    /\ parent' = [parent EXCEPT ![b] = p]
    /\ epoch' = [epoch EXCEPT ![b] = e]

Propose(b, p, h, e) == 
    /\ b \in Blocks
    /\ b /= p
    /\ ~Proposed(b)
    /\ ValidParent(p, h, e)
    /\ propose(b, p, h, e)
    /\ UNCHANGED <<round, bestBEEFY, bestGRANDPA, sessionStart, castVote, 
                   votes, status>>

(***************************************************************************)
(* Block b is finalized (GRANDPA Finalized) if and only if:                *)
(*  - Block b is proposed (height[b] > -1).                                *)
(*  - Block b's status is explictly set to "Finalized".                    *)
(***************************************************************************)
Finalized(b) == 
    /\ Proposed(b)
    /\ status[b] = "Finalized"

(***************************************************************************)
(* Block b is confirmed (BEEFY Justified) if and only if:                  *)
(*  - It is Finalized (Finalized implies proposed).                        *)
(*  - A quorum of nodes has voted for it (Quorum Certificate).             *)
(*  - Quorum ceritiface corresponds to N - T = 2f + 1 votes.               *)
(***************************************************************************)
Confirmed(b) == 
    /\ Finalized(b)
    /\ Cardinality(votes[b]) >= N - T
   
(***************************************************************************)
(* Update the status of block b to "Finalized" if:                         *)
(*  - Block b have been proposed (height[b] > -1).                         *)
(*  - Block b is not already finalized.                                    *)
(*  - The parent block of b is finalized.                                  *)
(*  - No other block c with a height greater than or equal to b's height   *)
(*    is already finalized.                                                *)
(***************************************************************************)
(* Note: While GRANDPA can finalize multiple blocks simultaneously,        *)
(* this specification assumes that only one block is finalized at a time.  *)
(* This operator also ensures that at most one block per height is updated *)
(* to "Finalized" and that all finalized blocks lie on a single chain.     *)
(***************************************************************************)
UpdateBlock(b) ==
    /\ Proposed(b)
    /\ ~Finalized(b)
    /\ Finalized(parent[b])
    /\ ~\E c \in Blocks : 
                /\ height[c] >= height[b] 
                /\ status[c] = "Finalized"
    /\ status' = [status EXCEPT ![b] = "Finalized"]
    /\ UNCHANGED <<round, bestBEEFY, bestGRANDPA, sessionStart, castVote, 
                    votes, height, parent, epoch>>

(***************************************************************************)
(* Updates the best GRANDPA block for node n to block b if:                *)
(*  - Block b is finalized.                                                *)
(*  - Block b has a greater height than the current best GRANDPA block     *)
(*    tracked by node n.                                                   *)
(***************************************************************************)
UpdateGRANDPAView(n, b) ==
    /\ Finalized(b)
    /\ height[b] > height[bestGRANDPA[n]]
    /\ bestGRANDPA' = [bestGRANDPA EXCEPT ![n] = b]
    /\ UNCHANGED <<round, bestBEEFY, sessionStart, castVote, votes, 
                    height, status, parent, epoch>>
                
(***************************************************************************)
(* Updates the best BEEFY block for node n to block b if:                  *)
(*  - Block b has a greater height than the current best BEEFY block       *)
(*    tracked by node n.                                                   *)
(*  - Block b does not exceed the height of the best GRANDPA block         *)
(*    tracked by node n (Best GRANDPA is always >= than best BEEFY.).      *)
(*  - Block b is finalized and has a BEEFY justification (Confirmed).      *)
(***************************************************************************)   
UpdateBEEFYView(n, b) == 
    /\ height[b] > height[bestBEEFY[n]]
    /\ height[bestGRANDPA[n]] >= height[b]
    /\ Confirmed(b)
    /\ bestBEEFY' = [bestBEEFY EXCEPT ![n] = b]
    /\ UNCHANGED <<round, bestGRANDPA, sessionStart, castVote, votes, 
                    height, status, parent, epoch>>

(***************************************************************************)
(* Updates the session start mandatory block for node n if:                *)
(*  1. The current mandatory block m (session start) has a BEEFY           *)
(*     justification (Confirmed).                                          *)
(*  2. The latest GRANDPA finalized block g belongs to a higher epoch      *)
(*     than the current mandatory block m.                                 *)
(*  - If conditions 1 and 2 are met, update sessionStart with a new        *)
(*    mandatory block.                                                     *)
(*  - The new mandatory block must be the first finalized block in an      *)
(*    epoch greater than the current mandatory block m.                    *)
(***************************************************************************)
\* @type: ($epoch) => $block;
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
    /\ Confirmed(m)
    /\ epoch[g] > epoch[m]
    /\ sessionStart' = [sessionStart EXCEPT ![n] = FindMandatoryBlock(epoch[m])]
    /\ UNCHANGED <<round, bestGRANDPA, bestBEEFY, round, castVote, votes, 
                    height, status, parent, epoch>>

(***************************************************************************)
(* Recursive operator to compute the smallest power of two >= x            *)
(*  1. Start with y = 1, the smallest power of two (2^0).                  *)
(*  2. If y is greater than or equal to x, return y.                       *)
(*  3. Otherwise, call operator with double y.                             *)
(***************************************************************************)
(* Example:                                                                *)
(*  NEXT_POWER_OF_TWO(10, 1)                                               *)
(*  - Checks 1, 2, 4, 8 (all < 10).                                        *)
(*  - Reaches 16 (the smallest power of two ≥ 10).                         *)
(***************************************************************************)
RECURSIVE NEXT_POWER_OF_TWO(_,_)
NEXT_POWER_OF_TWO(x, y) == IF y >= x THEN y ELSE NEXT_POWER_OF_TWO(x, 2 * y)

(***************************************************************************)
(* Non-recursive version of NEXT_POWER_OF_TWO.                             *)
(*  - Uses set operations to find the next power of two.                   *)
(*  - Required for Apalache, which does not support recursion.             *)
(* Note: Since Apalache struggles with the CHOOSE operator it recommends   *)
(* to use Fold operators is instead (not implemented).                     *)
(***************************************************************************)
NEXT_POWER_OF_TWO_V2(x) == 
    LET 
        POT == {2^n : n \in 0..x}
            \* Set of all powers of two from 0..x.
        POTR == {n \in POT : n <= x}
            \* Powers of two less than or equal to x.
        max == CHOOSE y \in POTR : (\A z \in POTR : y >= z)
            \* Max value in POTR.
    IN 
        IF x = 0 THEN 1 ELSE
        IF x \in POTR THEN x ELSE max*2

(***************************************************************************)
(* Calculate the minimum of two naturals.                                  *)
(***************************************************************************)
Min(x, y) == IF x <= y THEN x ELSE y 

(***************************************************************************)
(* Determines the next mandatory block for node n, if one exists:          *)
(*  1. If the best GRANDPA block is in a higher epoch than the             *)
(*     sessionStart block, return the first finalized block in that epoch. *)
(*  2. Otherwise, return the best GRANDPA block.                           *)
(***************************************************************************)
NextMandatoryBlock(n) == 
    LET 
        m == sessionStart[n]
            \* latest mandatory block for node n.
        g == bestGRANDPA[n]
            \* best GRANDPA block for node n.
    IN
        IF epoch[g] > epoch[m] THEN FindMandatoryBlock(epoch[m]) ELSE g

(***************************************************************************)
(* Calculates the updated round number for node n:                         *)
(*  - M is 1 if the mandatory block in the current session is already      *)
(*    BEEFY justified; otherwise, it is 0.                                 *)
(*  - NEXT_POWER_OF_TWO(x) returns the smallest power of two ≥ x.          *)
(*  - Ensures the new round does not exceed the height of the best         *)
(*    finalized GRANDPA block.                                             *)
(*  - Prevents multiple votes in the same round for the same block.        *)
(***************************************************************************)
(* Reference:                                                              *)
(*  - https://spec.polkadot.network/sect-finality#defn-beefy-round-number  *)
(***************************************************************************)
CalculateRoundNumber(n) ==
    LET 
        M == IF height[bestBEEFY[n]] >= height[sessionStart[n]] THEN 1 ELSE 0
            \* Check if mandatory block in the current Epoch is Confirmed.
        x == ((height[bestGRANDPA[n]] - height[bestBEEFY[n]]) + 1) \div 2
            \* (bestGRANDPA[n] - bestBEEFY[n] + 1) / 2.
        e == NextMandatoryBlock(n)
            \* Either next mandatory block or best GRANDPA block.
        r == (1 - M) * height[sessionStart[n]] + 
        M * Min(height[e], (height[bestBEEFY[n]] + NEXT_POWER_OF_TWO_V2(x)))
            \* Calculate the next round to start.
    IN
        \* Make sure the new round is less or equal to the best finalized
        \* GRANDPA round (block height).
        /\ height[bestGRANDPA[n]] >= r
        \* To avoid casting multiple votes in the same round (for same block).
        /\ r > round[n]
        /\ round' = [round EXCEPT ![n] = r]
        /\ castVote' = [castVote EXCEPT ![n] = FALSE]

(***************************************************************************)
(* Update the round number for node n if:                                  *)
(*  - Node n has already cast a vote in the current round.                 *)
(*  - The CalculateRoundNumber operator finds a round greater than node's  *)
(*    n current round, else the round stays the same.                      *)
(***************************************************************************)
(* Note:                                                                   *)
(*  - Once a node picks a new round r (and casts a vote), it ends the      *)
(*    previous round, regardless of whether finality was reached.          *)
(*  - Votes for an inactive round are not propagated.                      *)
(***************************************************************************)
UpdateRound(n) ==
    /\ castVote[n]
    /\ CalculateRoundNumber(n)
    /\ UNCHANGED <<bestGRANDPA, bestBEEFY, sessionStart, votes, 
                    height, status, parent, epoch>>

(***************************************************************************)
(* A honest node n can vote for a block b in round r if:                   *)
(*  - Block b is finalized.                                                *)
(*  - Node n best GRANDPA block is greater or equal to block b.            *)
(*    This indicates that block b is visible for node n.                   *)
(*  - The height of block b matches the current round r.                   *)
(*  - Node n has not already voted in this round.                          *)
(***************************************************************************)
vote(n, b) ==
    /\ votes' = [votes EXCEPT ![b] = votes[b] \cup {n}]
    /\ castVote' = [castVote EXCEPT ![n] = TRUE]

Vote(n, b) == 
    /\ Finalized(b)
    /\ height[bestGRANDPA[n]] >= height[b]
    /\ round[n] = height[b]
    /\ ~castVote[n]
    /\ vote(n, b)
    /\ UNCHANGED <<round,bestGRANDPA, bestBEEFY, sessionStart, 
                    height, status, parent, epoch>>

(***************************************************************************)
(* Logic for a faulty node.                                                *)
(*  - A faulty node can vote for any block, but does not vote for genesis  *)
(*    since it is already BEEFY justified (Confirmed).                     *)
(***************************************************************************)
FaultyStep == 
    /\ \E n \in FNodes : \E b \in Blocks : 
        /\ b /= gen
        /\ votes' = [votes EXCEPT ![b] = votes[b] \cup {n}]
    /\ UNCHANGED <<round,bestGRANDPA, bestBEEFY, sessionStart, castVote, 
                    height, status, parent, epoch>>

(***************************************************************************)
(* Below are defined the next-state action and the complete spec.          *)
(***************************************************************************)
Environment ==
    \/ \E b, p \in Blocks : \E h \in Heights : \E e \in Epochs :
         Propose(b, p, h, e)
    \/ \E b \in Blocks : UpdateBlock(b)

CorrectStep == 
    \E n \in CNodes : 
        \/ \E b \in Blocks :
            \/ Vote(n, b)
            \/ UpdateGRANDPAView(n, b)
            \/ UpdateBEEFYView(n, b)
        \/ UpdatesessionStart(n)
        \/ UpdateRound(n)

System == 
    \/ CorrectStep
    \/ FaultyStep
    
Next == Environment \/ System

(***************************************************************************)
(* Weak fairness is applied to honest nodes.                               *)
(* Byzantine nodes can vote for any block in any round or choose to be     *)
(* silent (do nothing), so we can't require any fairness from them.        *)
(***************************************************************************)
L == 
    /\ \A b, p \in Blocks : 
        /\ \A h \in Heights : \A e \in Epochs : WF_vars(Propose(b, p, h, e))
        /\ WF_vars(UpdateBlock(b))
    /\ \A n \in CNodes :
        /\ WF_vars(UpdateRound(n))
        /\ WF_vars(UpdatesessionStart(n))
        /\ \A b \in Blocks : 
            /\ WF_vars(Vote(n, b))
            /\ WF_vars(UpdateGRANDPAView(n, b))
            /\ WF_vars(UpdateBEEFYView(n, b))


Spec == Init /\ [][Next]_vars /\ L

NextWithoutFaulty == Environment \/ CorrectStep

Spec2 == InitWithFaults /\ [][NextWithoutFaulty]_vars /\ L

(***************************************************************************)
(* Invariants (Safety)                                                     *)
(***************************************************************************)

(***************************************************************************)
(* Helper definition to determine if block b is mandatory:                 *)
(*  - Block b must be GRANDPA Finalized.                                   *)
(*  - There must not exist another block c such that:                      *)
(*       1. c has the same epoch as b.                                     *)
(*       2. c has a lower height than b.                                   *)
(*       3. c is GRANDPA Finalized.                                        *)
(***************************************************************************)
IsMandatory(b) ==
    /\ Finalized(b)
    /\ ~\E c \in Blocks : /\ epoch[c] = epoch[b]
                          /\ height[c] < height[b]
                          /\ Finalized(c)

(***************************************************************************)
(* No two blocks have been GRANDPA Finalized on different chains.          *)
(* - If blocks b1 and b2 have the same height and both are finalized,      *)
(*   they must be the same block.                                          *)
(* - This property depends on the Finality Gadget.                         *)
(***************************************************************************)
NoConflictingFinalizedBlocks == 
    \A b1, b2 \in Blocks : 
            /\ height[b1] = height[b2]
            /\ Finalized(b1)
            /\ Finalized(b2)
            => b1 = b2

(***************************************************************************)
(* No two blocks have been Confirmed on different chains.                  *)
(* - If blocks b1 and b2 have the same height and both are confirmed, they *)
(*   must be the same block.                                               *)
(***************************************************************************)
NoConflictingConfirmedBlocks == 
    \A b1, b2 \in Blocks : 
            /\ height[b1] = height[b2]
            /\ Confirmed(b1)
            /\ Confirmed(b2)
            => b1 = b2

(***************************************************************************)
(* Only GRANDPA Finalized blocks can be Confirmed.                         *)
(* - If a block is confirmed, it must also be finalized.                   *)
(***************************************************************************)
ConfirmedBlockImpliesFinalized == 
    \A b \in Blocks : Confirmed(b) => Finalized(b)

(***************************************************************************)
(* No honest node is on a round that is not GRANDPA finalized.             *)
(* - An honest node cannot be on a round greater than the height of        *)
(*   its best GRANDPA finalized block.                                     *)
(***************************************************************************)
NoHonestNodeWithRoundGreaterThanBestFinalized ==
    \A n \in CNodes : ~(round[n] > height[bestGRANDPA[n]])

(***************************************************************************)
(* If a honest node n is on round r then all mandatory blocks with r' < r  *)
(* must have a BEEFY Justification.                                        *)
(***************************************************************************)
HonestRoundImpliesMandatoryBlocksConfirmed ==  TRUE


\* There should never exist a block b that have a BEEFY Justification, if there
\* exsists a mandatory block m that does not have a BEEFY Justification, if
\* b > m.
\* TODO

(***************************************************************************)
(* Temporal Properties (Liveness)                                          *)
(***************************************************************************)

(***************************************************************************)
(* Eventually, all mandatory blocks should be confirmed.                   *)
(*  - We use the leadsto (~>) operator which is defined as: [](F => <>G).  *)
(***************************************************************************)
MandatoryBlocksConfirmed ==
    \A b \in Blocks : ((IsMandatory(b) ~> Confirmed(b)))

=============================================================================