--------------------- MODULE BEEFYSingleChain -------------------------------
EXTENDS Integers, FiniteSets, TLC, BEEFY_typedefs 

(***************************************************************************)
(* PROTOCOL PARAMETERS                                                     *)
(***************************************************************************)
CONSTANTS
    \* The set of correct/honest nodes.
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
\* The set of all nodes (Correct and Byzantine combined).
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
\* Assume that MaxEpoch is a number in naturals >= 0.
ASSUME MaxEpoch \in Nat

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
    \* The round number corresponds to a block with height = round.
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
    \* Boolean value to highlight if a node has cast a vote for its round.
    \* TRUE indicate a vote has been cast, FALSE otherwise.
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
    epoch,
    \* Program Counter to indicate when finished proposing blocks.
    \* @type: $str -> $str
    pc

\* Tuple of all the variables
vars == <<round, bestBEEFY, bestGRANDPA, sessionStart, castVote, votes, 
          height, status, parent, epoch, pc>>

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
    /\ pc \in {"Proposing", "Voting"}

(***************************************************************************)
(* Note: Uppercase always indicate that it is a set (if a set uses both, it*)
(* will be obvious from context).                                          *)
(***************************************************************************)
(* P if Q (Q => P).                                                        *)
(* P only if Q (P => Q).                                                   *)
(* P if and only if Q (P => Q /\ Q => P).                                  *)
(* Iff is an abbreviation for if and only if.                              *)
(***************************************************************************)

(***************************************************************************)
(* Init                                                                    *)
(*  - Node's start in round 0 (height 0).                                  *)
(*  - Nodes have bestBEEFY, bestGRANDPA, and sessionStart as the genesis   *)
(*    block.                                                               *)
(*  - Initially all blocks but genesis have height -1 (Genesis have 0).    *)
(*  - All node's start in round 0.                                         *)
(*  - All nodes have already cast a vote in round 0 (for genesis).         *)
(*  - All blocks except the genesis block have votes (all nodes).          *)
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
    /\ pc = "Proposing"

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
    /\ pc = "Proposing"
    \* non-deterministically initialize the votes for blocks with faults
    /\ \E F \in SUBSET [n: FNodes, b: Blocks] :
        votes = [b \in Blocks |->
            IF b = gen THEN 
                Nodes
            ELSE 
                {f \in FNodes : (\E m \in F : m.n = f /\ m.b = b)}]
                
(***************************************************************************)
(* A block b is proposed iff:                                              *)
(*  - Block b is considered proposed if it is part of the chain, meaning   *)
(*    block b has been assigned a valid height (height[b] > -1).           *)
(*  - Block b has also been assigned a valid epoch (epoch[b] > -1).        *)
(***************************************************************************)
Proposed(b) == 
    /\ b \in Blocks
    /\ height[b] > -1
    /\ epoch[b] > -1

(***************************************************************************)
(* A block p is a valid parent for a block with height h and epoch e iff:  *)
(*  - The parent block p has already been proposed (height[p] > -1).       *)
(*  - The parent block's height is exactly one less than h.                *)
(*  - Parent block p epoch is less or equal to the proposed block epoch e. *)
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
(*  - If there is no more blocks to be proposed then set pc to "Voting".   *)
(***************************************************************************)
propose(b, p, h, e) ==
    /\ height' = [height EXCEPT ![b] = h]
    /\ parent' = [parent EXCEPT ![b] = p]
    /\ epoch' = [epoch EXCEPT ![b] = e]

doneProposing ==
    /\ pc' = "Voting"
    /\ UNCHANGED <<round, bestBEEFY, bestGRANDPA, sessionStart, castVote, 
                    votes, height, parent, epoch, status>>

Propose(e) ==
    LET 
        B == {c \in Blocks : height[c] = -1}
        p == CHOOSE p \in Blocks \ B : \A c \in Blocks : height[p] >= height[c]
            \* Since genesis start with height 0, there will always be a 
            \* block with the greatest height.
        b == CHOOSE c \in B : TRUE
            \* Block to be proposed.
        h == height[p] + 1
            \* Height of the block to be propsoed.
    IN
    /\ pc = "Proposing"
    /\ IF B = {} THEN doneProposing ELSE
       /\ ~Proposed(b)
       /\ ValidParent(p, h, e)
       /\ propose(b, p, h, e)
       /\ UNCHANGED <<round, bestBEEFY, bestGRANDPA, sessionStart, castVote, 
                   votes, pc, status>>

(***************************************************************************)
(* Block b is finalized (GRANDPA Finalized) iff:                           *)
(*  - Block b is proposed (height[b] > -1).                                *)
(*  - Block b's status is explictly set to "Finalized".                    *)
(***************************************************************************)
Finalized(b) == 
    /\ Proposed(b)
    /\ status[b] = "Finalized"

(***************************************************************************)
(* Block b is Justified (BEEFY Justified) iff:                             *)
(*  - Block b is finalized (finalized implies proposed).                   *)
(*  - A quorum of nodes has voted for it (Quorum Certificate).             *)
(*  - Quorum ceritiface corresponds to N - T = 2f + 1 votes.               *)
(***************************************************************************)
Justified(b) == 
    /\ Finalized(b)
    /\ Cardinality(votes[b]) >= N - T
   
(***************************************************************************)
(* Update the status of block b to "Finalized" if:                         *)
(*  - Block b have been proposed (height[b] > -1).                         *)
(*  - Block b is not already finalized (implies status is "Available").    *)
(*  - The parent block of b is finalized.                                  *)
(*  - No other block c with a height greater than or equal to b's height   *)
(*    is already finalized.                                                *)
(***************************************************************************)
(* Note: While GRANDPA can finalize multiple blocks simultaneously,        *)
(* this specification assumes that only one block is finalized at a time.  *)
(* This operator also ensures that at most one block per height is updated *)
(* to "Finalized" and that all finalized blocks lies on a single chain.    *)
(***************************************************************************)
UpdateBlock(b) ==
    /\ pc = "Voting"
    /\ Proposed(b)
    /\ ~Finalized(b)
    /\ Finalized(parent[b])
    /\ ~\E c \in Blocks : 
                /\ height[c] >= height[b] 
                /\ status[c] = "Finalized"
    /\ status' = [status EXCEPT ![b] = "Finalized"]
    /\ UNCHANGED <<round, bestBEEFY, bestGRANDPA, sessionStart, castVote, 
                    votes, height, parent, epoch, pc>>

(***************************************************************************)
(* Updates the best GRANDPA block for node n to block b if:                *)
(*  - Block b is finalized.                                                *)
(*  - Block b has height greater than the current best GRANDPA block       *)
(*    tracked by node n.                                                   *)
(***************************************************************************)
UpdateGRANDPAView(n, b) ==
    /\ pc = "Voting"
    /\ Finalized(b)
    /\ height[b] > height[bestGRANDPA[n]]
    /\ bestGRANDPA' = [bestGRANDPA EXCEPT ![n] = b]
    /\ UNCHANGED <<round, bestBEEFY, sessionStart, castVote, votes, 
                    height, status, parent, epoch, pc>>
                
(***************************************************************************)
(* Updates the best BEEFY block for node n to block b if:                  *)
(*  - Block b has height greater than the current best BEEFY block tracked *)
(*    by node n.                                                           *)
(*  - Block b does not exceed the height of the best GRANDPA block         *)
(*    tracked by node n (Best GRANDPA is always >= than best BEEFY).       *)
(*  - Block b is finalized and has a BEEFY justification.                  *)
(***************************************************************************)   
UpdateBEEFYView(n, b) ==
    /\ pc = "Voting"
    /\ height[b] > height[bestBEEFY[n]]
    /\ height[bestGRANDPA[n]] >= height[b]
    /\ Justified(b)
    /\ bestBEEFY' = [bestBEEFY EXCEPT ![n] = b]
    /\ UNCHANGED <<round, bestGRANDPA, sessionStart, castVote, votes, 
                    height, status, parent, epoch, pc>>

(***************************************************************************)
(* Updates the session start mandatory block for node n if:                *)
(*  1. The current mandatory block m (session start) has a BEEFY           *)
(*     justification.                                                      *)
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
    /\ pc = "Voting"
    /\ Justified(m)
    /\ epoch[g] > epoch[m]
    /\ sessionStart' = [sessionStart EXCEPT ![n] = FindMandatoryBlock(epoch[m])]
    /\ UNCHANGED <<round, bestGRANDPA, bestBEEFY, round, castVote, votes, 
                    height, status, parent, epoch, pc>>

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
(* to use Fold operators instead (not implemented).                        *)
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
            \* Check if mandatory block in the current Epoch is Justified.
        x == ((height[bestGRANDPA[n]] - height[bestBEEFY[n]]) + 1) \div 2
            \* (bestGRANDPA[n] - bestBEEFY[n] + 1) / 2.
        e == NextMandatoryBlock(n)
            \* Either next mandatory block or best GRANDPA block.
        r == (1 - M) * height[sessionStart[n]] + 
        M * Min(height[e], (height[bestBEEFY[n]] + NEXT_POWER_OF_TWO_V2(x)))
            \* Calculate the next round to start.
    IN
        /\ pc = "Voting"
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
(* Note: In the Polkadot specification and BEEFY paper it states: From the *)
(* local view of a node, a round ends if either of the following occurs:   *)
(*  1. Nodes collect 2f + 1 valid votes for the current round, i.e., the   *)
(*     block obtains BEEFY Justification.                                  *)
(*  2. Nodes receives a BEEFY Justification for a block higher than the    *)
(*     currently known highest BEEFY block.                                *)
(* In both cases the node proceeds to determine the new round.             *)
(* This won't actually work because nodes can get stuck on different rounds*)
(* e.g., node 1 and 2 is on round 1, while node 3 is on round 2 and the    *)
(* byzantine node 4 does not cast any votes.                               *)
(* Note: The BEEFY paper also states the following                         *)
(*  - Once a node picks a new round r (and casts a vote), it ends the      *)
(*    previous round, regardless of whether finality was reached.          *)
(*  - Votes for an inactive round are not propagated.                      *)
(***************************************************************************)
UpdateRound(n) ==
    /\ pc = "Voting"
    /\ height[bestBEEFY[n]] >= round[n]
    /\ castVote[n]
    /\ CalculateRoundNumber(n)
    /\ UNCHANGED <<bestGRANDPA, bestBEEFY, sessionStart, votes, 
                    height, status, parent, epoch, pc>>

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
    /\ pc = "Voting"
    /\ Finalized(b)
    /\ height[bestGRANDPA[n]] >= height[b]
    /\ round[n] = height[b]
    /\ ~castVote[n]
    /\ vote(n, b)
    /\ UNCHANGED <<round,bestGRANDPA, bestBEEFY, sessionStart, 
                    height, status, parent, epoch, pc>>

(***************************************************************************)
(* Logic for a faulty node.                                                *)
(*  - A faulty node can vote for any block, but does not vote for genesis  *)
(*    since it is already BEEFY justified.                                 *)
(***************************************************************************)
FaultyStep == 
    /\ \E n \in FNodes : \E b \in Blocks : 
        /\ b /= gen
        /\ votes' = [votes EXCEPT ![b] = votes[b] \cup {n}]
    /\ UNCHANGED <<round,bestGRANDPA, bestBEEFY, sessionStart, castVote, 
                    height, status, parent, epoch, pc>>

(***************************************************************************)
(* Below are defined the next-state action and the complete spec.          *)
(***************************************************************************)
Environment ==
    \/ \E e \in Epochs : Propose(e)
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
    \*\/ FaultyStep
    
Next == Environment \/ System

(***************************************************************************)
(* Weak fairness is applied to honest nodes.                               *)
(* Byzantine nodes can vote for any block in any round or choose to be     *)
(* silent (do nothing), so we can't require any fairness from them.        *)
(***************************************************************************)
L == 
    /\ \A e \in Epochs : WF_vars(Propose(e))
    /\ \A b, p \in Blocks : WF_vars(UpdateBlock(b))
    /\ \A n \in CNodes :
        /\ WF_vars(UpdateRound(n))
        /\ WF_vars(UpdatesessionStart(n))
    /\ \A n \in CNodes : \A b \in Blocks : 
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
(* All proposed blocks are on a single chain.                              *)
(*  - If blocks b1 and b2 have the same height and both are proposed, they *)
(*    must be the same block.                                              *)
(***************************************************************************)
SingleChain == 
    \A b1, b2 \in Blocks :
            /\ height[b1] = height[b2]
            /\ Proposed(b1)
            /\ Proposed(b2)
            => b1 = b2

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
(* No two blocks have been Justified on different chains.                  *)
(* - If blocks b1 and b2 have the same height and both are justified, they *)
(*   must be the same block.                                               *)
(***************************************************************************)
NoConflictingJustifiedBlocks == 
    \A b1, b2 \in Blocks : 
        /\ height[b1] = height[b2]
        /\ Justified(b1)
        /\ Justified(b2)
        => b1 = b2

(***************************************************************************)
(* Only GRANDPA Finalized blocks can be BEEFY Justified.                   *)
(* - If a block is justified, it must also be finalized.                   *)
(***************************************************************************)
JustifiedBlockImpliesFinalized == 
    \A b \in Blocks : Justified(b) => Finalized(b)

(***************************************************************************)
(* If a honest node is on round r, then there should exists a block that   *)
(* is GRANDPA Finalized at round r.                                        *)
(***************************************************************************)
NodeAtRoundImpliesFinalizedBlockAtRound ==
    \A n \in CNodes : \E b \in Blocks :
        /\ Finalized(b) 
        /\ round[n] = height[b]

(***************************************************************************)
(* No honest node is on a round that is not GRANDPA Finalized.             *)
(* - An honest node cannot be on a round greater than the height of        *)
(*   its best GRANDPA Finalized block.                                     *)
(***************************************************************************)
NoHonestNodeWithRoundGreaterThanBestFinalized ==
    \A n \in CNodes : ~(round[n] > height[bestGRANDPA[n]])

(***************************************************************************)
(* If an honest node n is on round r, then all mandatory blocks with       *)
(* height less than r must have a BEEFY Justification.                     *)
(***************************************************************************)
HonestRoundImpliesMandatoryBlocksJustified ==
    \A n \in CNodes : \A b \in Blocks : 
        /\ IsMandatory(b)
        /\ height[b] < round[n]
        => Justified(b)

(***************************************************************************)
(* If a block has a BEEFY Justification b, then all mandatory blocks with  *)
(* height less or equal to b must have a BEEFY Justification.              *)
(***************************************************************************)
AllPreviousMandatoryBlocksJustified == 
    \A b \in Blocks : Justified(b) => \A c \in Blocks :
        /\ IsMandatory(c)
        /\ height[c] <= height[b]
        => Justified(c)

(***************************************************************************)
(* Temporal Properties (Liveness)                                          *)
(***************************************************************************)

(***************************************************************************)
(* Eventually, all mandatory blocks should be Justified.                   *)
(*  - We use the leadsto (~>) operator which is defined as: [](F => <>G).  *)
(***************************************************************************)
MandatoryBlocksJustified ==
    \A b \in Blocks : ((IsMandatory(b) ~> Justified(b)))

BlockEventuallyConfirmed ==
    <>\E b \in Blocks : Justified(b) /\ b /= gen

=============================================================================