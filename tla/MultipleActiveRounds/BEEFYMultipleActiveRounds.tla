--------------------- MODULE BEEFYMultipleActiveRounds ---------------------
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
\* Usually a block has an associated slot along with an epoch, but
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
\* program actually breaks some invariants when the number of faulty nodes goes
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
(* Based on:                                                               *)
(*  - Polkadot Specifications                                              *)
(*    https://spec.polkadot.network/sect-finality#sect-grandpa-beefy       *)
(*  - BEEFY Paper                                                          *)
(*    https://eprint.iacr.org/2025/057.pdf                                 *)
(*  - Talks with Bhargav Bhatt from Web3 Foundation Research.              *)
(*  - Substrate Rust Implementation                                        *)
(*    https://github.com/paritytech/polkadot-sdk/tree/master/substrate/client/consensus/beefy *)
(***************************************************************************)
VARIABLES
    \* The set of active round for a node.
    \* A round corresponds to a block with height equal to it.
    \* @type: $node -> Set($height);
    round,
    \* A node's view of best BEEFY block.
    \* @type: $node -> $block;
    bestBEEFY,
    \* A node's view of best GRANDPA block.
    \* @type: $node -> $block;
    bestGRANDPA,
    \* A node's view of when a new session/epoch starts, it must be the first
    \* first finalized block in an epoch.
    \* These blocks are mandatory (they must receive a BEEFY Justification).
    \* If bestBEEFY block is greater than sessionStart, then sessionStart has
    \* a BEEFY Justification.
    \* @type: $node -> $block;
    sessionStart,
    \* A mapping of each node to the mandatory blocks it has a BEEFY
    \* Justification for.
    \* @type $node -> Set($block);
    mandatoryBlocks,
    \* A node's view of when it should accept blocks and update round.
    \* After each new block (bestBEEFY or bestGRANDPA) it should check
    \* if a new round can become active.
    \* After checking if a new round can become active, it goes back to
    \* waiting for new blocks (GRANDPA or BEEFY).
    \* @type: $node -> $Str;
    pc,
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
vars == <<round, bestBEEFY, bestGRANDPA, sessionStart, mandatoryBlocks, pc, 
            votes, height, status, parent, epoch>>

(***************************************************************************)
(* The type invariant                                                      *)
(***************************************************************************)
TypeOK ==
    /\ round \in [CNodes -> SUBSET Heights]
    /\ bestBEEFY \in [CNodes -> Blocks]
    /\ bestGRANDPA \in [CNodes -> Blocks]
    /\ sessionStart \in [CNodes -> Blocks]
    /\ mandatoryBlocks \in [CNodes -> SUBSET Blocks]
    /\ pc \in [CNodes -> {"ReceiveBlock", "UpdateRound"}]
    /\ votes \in [Blocks -> SUBSET Nodes]
    /\ height \in [Blocks -> Heights]
    /\ status \in [Blocks -> {"Available", "Finalized"}]
    /\ parent \in [Blocks -> Blocks]
    /\ epoch \in [Blocks -> Epochs]

(***************************************************************************)
(* P if Q (Q => P).                                                        *)
(* P only if Q (P => Q).                                                   *)
(* P if and only if Q (P => Q /\ Q => P).                                  *)
(* Iff is an abbreviation for if and only if.                              *)
(***************************************************************************)

(***************************************************************************)
(* Init                                                                    *)
(*  - Node's start with zero active rounds (empty set).                    *)
(*  - Nodes have bestBEEFY, bestGRANDPA, and sessionStart as the genesis   *)
(*    block.                                                               *)
(*  - All nodes have the genesis in the mandatory blocks set, which should *)
(*    contain all mandatory blocks they have received a BEEFY              *)
(*    Justification for.                                                   *)
(*  - All nodes are ready to receive blocks (pc = "ReceiveBlock").         *)
(*  - Initially all blocks but genesis have height -1 (Genesis have 0).    *)
(*  - All blocks are "Available" except genesis which is "Finalized".      *)
(*  - All blocks are their own parent (this is only valid for genesis).    *)
(*  - All blocks have their epoch set to -1 except genesis block (epoch 0).*)
(*  - All blocks except the genesis block (all nodes have voted) have zero *)
(*    votes for them.                                                      *)
(***************************************************************************)
Init ==
    \* Nodes
    /\ round = [n \in CNodes |-> {}]
    /\ bestBEEFY = [n \in CNodes |-> gen]
    /\ bestGRANDPA = [n \in CNodes |-> gen]
    /\ sessionStart = [n \in CNodes |-> gen]
    /\ mandatoryBlocks = [n \in CNodes |-> {gen}]
    /\ pc = [n \in CNodes |-> "ReceiveBlock"]
    \* Blocks
    /\ height = [[b \in Blocks |-> -1] EXCEPT ![gen]=0]
    /\ status = [[b \in Blocks |-> "Available"] EXCEPT ![gen]="Finalized"]
    /\ parent = [b \in Blocks |-> b]
    /\ epoch = [[b \in Blocks |-> -1] EXCEPT ![gen]=0]
    /\ votes = [[b \in Blocks |-> {}] EXCEPT ![gen]=Nodes]
                
(***************************************************************************)
(* A block b is proposed iff:                                              *)
(*  - It is part of the chain, meaning block b has been assigned a valid   *)
(*    height (height[b] > - 1), and                                        *)
(*  - been assigned a valid epoch (epoch[b] > -1).                         *)
(***************************************************************************)
Proposed(b) == 
    /\ b \in Blocks
    /\ height[b] > -1
    /\ epoch[b] > -1

(***************************************************************************)
(* A block p is a valid parent for a block with height h and epoch e iff:  *)
(*  - The parent block p has already been proposed check Proposed(p).      *)
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
(*  - Block b is not already proposed, check not Proposed(b).              *)
(*  - The parent block p is valid.                                         *)
(***************************************************************************)
propose(b, p, h, e) ==
    /\ height' = [height EXCEPT ![b] = h]
    /\ parent' = [parent EXCEPT ![b] = p]
    /\ epoch' = [epoch EXCEPT ![b] = e]

Propose(e) ==
    LET 
        B == {c \in Blocks : height[c] = -1}
        p == CHOOSE p \in Blocks \ B : \A c \in Blocks : height[p] >= height[c]
            \* Since genesis start with height 0, there will always be a 
            \* block with the greatest height.
        b == CHOOSE c \in B : TRUE
            \* Block to be proposed.
        h == height[p] + 1
            \* Height of the block to be proposed.
    IN
    /\ B /= {}
    /\ ~Proposed(b)
    /\ ValidParent(p, h, e)
    /\ propose(b, p, h, e)
    /\ UNCHANGED <<round, bestBEEFY, bestGRANDPA, sessionStart, pc,
                    mandatoryBlocks, votes, status>>

(***************************************************************************)
(* Block b is finalized (GRANDPA Finalized) iff:                           *)
(*  - Block b is proposed check Proposed(b).                               *)
(*  - Block b's status is explictly set to "Finalized".                    *)
(***************************************************************************)
Finalized(b) == 
    /\ Proposed(b)
    /\ status[b] = "Finalized"

(***************************************************************************)
(* Block b is Justified (BEEFY Justified) iff:                             *)
(*  - Block b is finalized (Finalized(b) implies proposed).                *)
(*  - A quorum of nodes has voted for it (Quorum Certificate).             *)
(*  - Quorum ceritiface corresponds to N - T = 2f + 1 votes.               *)
(***************************************************************************)
Justified(b) == 
    /\ Finalized(b)
    /\ Cardinality(votes[b]) >= N - T
   
(***************************************************************************)
(* Update the status of block b to "Finalized" if:                         *)
(*  - Block b have been proposed, check Proposed(b).                       *)
(*  - Block b is not already finalized (implies status is "Available").    *)
(*  - The parent block p of b is finalized, check Finalized(p).            *)
(*  - No other block c with a height greater than or equal to b's height   *)
(*    is already finalized.                                                *)
(***************************************************************************)
(* Note: While GRANDPA can finalize multiple blocks simultaneously,        *)
(* this specification assumes that only one block is finalized at a time.  *)
(* This operator also ensures that at most one block per height is updated *)
(* to "Finalized" and that all finalized blocks lies on a single chain.    *)
(***************************************************************************)
UpdateBlock(b) ==
    /\ Proposed(b)
    /\ ~Finalized(b)
    /\ Finalized(parent[b])
    /\ ~\E c \in Blocks : 
                /\ height[c] >= height[b] 
                /\ status[c] = "Finalized"
    /\ status' = [status EXCEPT ![b] = "Finalized"]
    /\ UNCHANGED <<round, bestBEEFY, bestGRANDPA, sessionStart, pc,
                    mandatoryBlocks, votes, height, parent, epoch>>

(***************************************************************************)
(* Updates the session start (mandatory block) for node n if the following *)
(* conditons are met, given inputs b = bestBEEFY and g = bestGRANDPA.      *)
(*  1. The current mandatory block m (current sessionStart) has a BEEFY    *)
(*     Justification (i.e., bestBEEFY >= sessionStart).                    *)
(*  2. The best GRANDPA Finalized block g belongs to a higher epoch than   *)
(*     the current mandatory block m.                                      *)
(* If these conditions hold, the sessionStart for node n is updated to a   *)
(* new mandatory block, which is defined as:                               *)
(*  - The first finalized block in the first epoch greater than that of m. *)
(* Note: The reason bestBEEFY and bestGRANDPA are given as input instead   *)
(* of fetching them through bestBEEFY[n] and bestGRANDPA[n] is that we     *)
(* need to access the primed values, which reflect the updated state.      *)
(* Fetching them through bestBEEFY[n] and bestGRANDPA[n] would give us the *)
(* old/stale values.                                                       *)
(* Only one of them will the primed value, but the operator won't known    *)
(* which one.                                                              *)
(***************************************************************************)
\* @type: ($epoch) => $block;
findMandatoryBlock(e) ==
    LET 
        B == {b \in Blocks : epoch[b] > e /\ Finalized(b)}
    IN 
        CHOOSE b \in B : (\A c \in B : height[b] <= height[c])

updatesessionStart(n, b, g) ==
    LET 
        m == sessionStart[n]
            \* Current mandatory block for node n.
    IN
    IF 
        height[b] >= height[m] /\ epoch[g] > epoch[m]
    THEN
        sessionStart' = [sessionStart EXCEPT ![n] = findMandatoryBlock(epoch[m])]
    ELSE 
        sessionStart' = sessionStart

(***************************************************************************)
(* Updates the best GRANDPA block for node n to block b if the following   *)
(* conditions are met:                                                     *)
(*  1. We are ready to receive a block (indicated by pc = "ReciveBlock").  *)
(*  2. Block b is finalized (implies it is proposed).                      *)
(*  3. Block b has a higher height than the current best GRANDPA block     *)
(*     tracked by node n.                                                  *)
(* If these conditions are satisifed, then:                                *)
(*  - The best GRANDPA blockf ro node n is updated to block b.             *)
(*  - The program counter (pc) is set to "UpdateRound" to check whether a  *)
(*    new round should become active.                                      *)
(*  - Update the sessionStart (next mandatory block) if necessary.         *)
(***************************************************************************)
UpdateGRANDPAView(n, b) ==
    /\ pc[n] = "ReceiveBlock"
    /\ Finalized(b)
    /\ height[b] > height[bestGRANDPA[n]]
    /\ bestGRANDPA' = [bestGRANDPA EXCEPT ![n] = b]
    /\ pc' = [pc EXCEPT ![n] = "UpdateRound"]
    /\ updatesessionStart(n, bestBEEFY[n], b)
    /\ UNCHANGED <<round, bestBEEFY, mandatoryBlocks, votes, height, 
                    status, parent, epoch>>

(***************************************************************************)
(* Remove stale rounds up to round r for node n:                           *)
(*  - The node updates its local view of active rounds by discarding all   *)
(*    rounds with a value less than r.                                     *)
(*  - The round r represents the height of the newly updated best BEEFY    *)
(*    block.                                                               *)
(***************************************************************************)
(* Note: In the Polkadot specification and BEEFY paper it states: From the *)
(* local view of a node, a round ends if either of the following occurs:   *)
(*  1. Nodes collect 2f + 1 valid votes for the current round, i.e., the   *)
(*     block obtains a BEEFY Justification.                                *)
(*  2. Nodes receives a BEEFY Justification for a block higher than the    *)
(*     currently known highest BEEFY block.                                *)
(***************************************************************************)
removeStaleRounds(n, r) ==
    /\ round' = [round EXCEPT ![n] = @ \ 0..r]

(***************************************************************************)
(* Add block b to the set of mandatory blocks for node n if:               *)
(*  - b is a mandatory block (it must be equal to the sessionStart block). *)
(*  - b is BEEFY Justified (the caller ensures this condition).            *)
(***************************************************************************)
updateMandatoryBlocks(n, b) ==
    LET 
        m == sessionStart[n]
            \* Current mandatory block for node n.
    IN 
    IF 
        m = b 
    THEN 
        mandatoryBlocks' = [mandatoryBlocks EXCEPT ![n]=@ \cup {b}]
    ELSE
        mandatoryBlocks' = mandatoryBlocks
                
(***************************************************************************)
(* Updates the best BEEFY block for node n to block b if the following     *)
(* conditions are met:                                                     *)
(*  1. We are ready to receive a block (indicated by pc = "ReciveBlock").  *)
(*  2. Block b is BEEFY Justified (implies GRANDPA Finalized).             *)
(*  3. Block b has a higher height than the current best BEEFY block       *)
(*     tracked by node n.                                                  *)
(*  4. Block b does not exceed the height of the best GRANDPA block        *)
(*     tracked by node n (best GRANDPA block should always be greater or   *)
(*     equal to best BEEFY block).                                         *)
(*  5. One of these conditions holds:                                      *)
(*      - Block b is the current mandatory block m (sessionStart).         *)
(*      - The current mandatory block m is already BEEFY Justified.        *)
(* If these conditions are satisifed, then:                                *)
(*  - The best BEEFY block for node n is updated to block b.               *)
(*  - The program counter (pc) is set to "UpdateRound" to check whether a  *)
(*    new round should be activated.                                       *)
(*  - Stale rounds are removed.                                            *)
(*  - Update the sessionStart (next mandatory block) if necessary.         *)
(*  - Add block b to set of mandatory blocks that have received a BEEFY    *)
(*    Justification, if block b is mandatory.                              *)
(***************************************************************************)
(* Note: If the current mandatory block m (sessionStart) does not have a   *)
(* BEEFY Justification, we will not update bestBEEFY until mandatory block *)
(* m recives a BEEFY Justification, regardless of whether we receive a     *)
(* BEEFY JUstification for a block with height > m.                        *)
(* In an actual implementation, we would likely query another node if this *)
(* scenario occurs to ensure we obtain the necessary BEEFY Justification.  *)
(***************************************************************************)   
UpdateBEEFYView(n, b) ==
    LET 
        m == sessionStart[n]
            \* Current mandatory block for node n.
    IN
    /\ pc[n] = "ReceiveBlock"
    /\ Justified(b)
    /\ height[b] > height[bestBEEFY[n]]
    /\ height[bestGRANDPA[n]] >= height[b]
    /\ \/ b = m
       \/ height[bestBEEFY[n]] >= height[m]
    /\ bestBEEFY' = [bestBEEFY EXCEPT ![n] = b]
    /\ pc' = [pc EXCEPT ![n] = "UpdateRound"]
    /\ removeStaleRounds(n, height[b])
    /\ updatesessionStart(n, b, bestGRANDPA[n])
    /\ updateMandatoryBlocks(n, b)
    /\ UNCHANGED <<bestGRANDPA, votes, height, status, parent, epoch>>

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
nextMandatoryBlock(n) == 
    LET 
        m == sessionStart[n]
            \* latest mandatory block for node n.
        g == bestGRANDPA[n]
            \* best GRANDPA block for node n.
    IN
        IF epoch[g] > epoch[m] THEN findMandatoryBlock(epoch[m]) ELSE g

(***************************************************************************)
(* Calculates the round number r for node n based on the following logic:  *)
(*  1. M is 1 if the mandatory block in the current session is already     *)
(*     BEEFY justified; otherwise, it is 0.                                *)
(*  2. NEXT_POWER_TWO(x) returns the smallest power of two greater than or *)
(*     equal to x.                                                         *)
(*  3. If M is 0 (mandatory block is not BEEFY Justified):                 *)
(*      - The round r is equal to the height of the mandatory block.       *)
(*  4. If M is 1 (mandatory block is BEEFY Justified):                     *)
(*      - The round number r is calculated using the formula found in the  *)
(*        Polkadot specification (see Reference below).                    *)
(*      - Round Number r is bounded by the height of the next mandatory    *)
(*        block.                                                           *)
(*      - If there is no next mandatory block, it is bounded by the best   *)
(*        GRANDPA Finalized block.                                         *)
(*  5. Then:                                                               *)
(*      - The round r is added to the set of active rounds.                *)
(*      - A vote is cast for the GRANDPA Finalized block with height = r.  *)
(* Note: Because of the calculation in step 4, we can only make rounds     *)
(* active if we have seen a GRANDPA Finalized block with the same height.  *)
(***************************************************************************)
(* Reference:                                                              *)
(*  - https://spec.polkadot.network/sect-finality#defn-beefy-round-number  *)
(***************************************************************************)
CalculateRoundNumberAndVote(n) ==
    LET 
        M == IF height[bestBEEFY[n]] >= height[sessionStart[n]] THEN 1 ELSE 0
            \* Check if mandatory block in the current Epoch is Justified.
        x == ((height[bestGRANDPA[n]] - height[bestBEEFY[n]]) + 1) \div 2
            \* (bestGRANDPA[n] - bestBEEFY[n] + 1) / 2.
        e == nextMandatoryBlock(n)
            \* Either the next mandatory block or best GRANDPA block.
        r == (1 - M) * height[sessionStart[n]] + 
        M * Min(height[e], (height[bestBEEFY[n]] + NEXT_POWER_OF_TWO_V2(x)))
            \* Calculate the next round to start.
        b == CHOOSE b \in Blocks : height[b] = r /\ Finalized(b)
            \* Find the block to vote for.
    IN
        /\ round' = [round EXCEPT ![n] = @ \cup {r}]
        /\ votes' = [votes EXCEPT ![b] = votes[b] \cup {n}]

(***************************************************************************)
(* Update the round number for node n if the following conditions are met: *)
(*  1. Node n is at the "UpdateRound" step (i.e., we have just received a  *)
(*     BEEFY or GRANDPA block).                                            *)
(*  2. The CalculateROundNumberAndVote operator finds a round that is not  *)
(*     active and casts a vote for it, else do nothing.                    *)
(* Then:                                                                   *)
(*  - The program counter (pc) is set to "ReceiveBlock" to signal the node *)
(*    ready to receive a new block.                                        *)
(***************************************************************************)
UpdateRound(n) ==
    /\ pc[n] = "UpdateRound"
    /\ CalculateRoundNumberAndVote(n)
    /\ pc' = [pc EXCEPT ![n] = "ReceiveBlock"]
    /\ UNCHANGED <<bestGRANDPA, bestBEEFY, sessionStart, mandatoryBlocks, 
                    height, status, parent, epoch>>

(***************************************************************************)
(* Logic for a faulty node.                                                *)
(*  - A faulty node can vote for any block, but does not vote for genesis  *)
(*    since it is already BEEFY justified.                                 *)
(***************************************************************************)
FaultyStep == 
    /\ \E n \in FNodes : \E b \in Blocks : 
        /\ b /= gen
        /\ votes' = [votes EXCEPT ![b] = votes[b] \cup {n}]
    /\ UNCHANGED <<round,bestGRANDPA, bestBEEFY, sessionStart, pc,
                    mandatoryBlocks, height, status, parent, epoch>>

(***************************************************************************)
(* Below are defined the next-state action and the complete spec.          *)
(***************************************************************************)
Environment ==
    \/ \E e \in Epochs : Propose(e)
    \/ \E b \in Blocks : UpdateBlock(b)

CorrectStep == 
    \E n \in CNodes : 
        \/ \E b \in Blocks :
            \/ UpdateGRANDPAView(n, b)
            \/ UpdateBEEFYView(n, b)
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
    /\ \A n \in CNodes : WF_vars(UpdateRound(n))
    /\ \A n \in CNodes : \A b \in Blocks : 
            /\ WF_vars(UpdateGRANDPAView(n, b))
            /\ WF_vars(UpdateBEEFYView(n, b))


Spec == Init /\ [][Next]_vars /\ L

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
(* Honest nodes only store mandatory block in the mandatoryBlocks set.     *)
(***************************************************************************)
MandatorySet == 
    \A n \in CNodes : \A b \in mandatoryBlocks[n] : /\ IsMandatory(b)
                                                    /\ Justified(b)

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
    \A n \in CNodes : \A r \in round[n] : \E b \in Blocks :
        /\ Finalized(b) 
        /\ r = height[b]

(***************************************************************************)
(* No honest node is on a round that is not GRANDPA Finalized.             *)
(* - An honest node cannot be on a round greater than the height of        *)
(*   its best GRANDPA Finalized block.                                     *)
(***************************************************************************)
NoHonestNodeWithRoundGreaterThanBestFinalized ==
    \A n \in CNodes : ~\E r \in round[n] : r > height[bestGRANDPA[n]]

(***************************************************************************)
(* If an honest node n is on round r, then all mandatory blocks with       *)
(* height less than r must have a BEEFY Justification.                     *)
(***************************************************************************)
HonestRoundImpliesMandatoryBlocksJustified ==
    \A n \in CNodes : \A r \in round[n] : \A b \in Blocks : 
        /\ IsMandatory(b)
        /\ height[b] < r
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