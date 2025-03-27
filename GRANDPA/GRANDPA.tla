------------------------------ MODULE GRANDPA ------------------------------
EXTENDS Integers, FiniteSets, TLC, GRANDPA_typedefs

(***************************************************************************)
(* PROTOCOL PARAMETERS                                                     *)
(***************************************************************************)
CONSTANTS 
    \* Set of correct voters.
    \* @type: Set($voter);
    CVoters,
    \* Set of Byzantine voters, may be empty (unknown to voters).
    \* @type: Set($voter);
    FVoters,
    \* Total number of voters, correct and Byzantine.
    \* @type: Int;
    N,
    \* An upper bound of the number of faulty voters.
    \* @type: Int;
    T,
    \* Set of unique blocks.
    \* @type: Set($block);
    Blocks,
    \* The maximum number of rounds, which we bound for model checking.
    \* @type: $round;
    MaxRound

(***************************************************************************)
(* Definitions                                                             *)
(***************************************************************************)

\* the set of all voters.
Voters == CVoters \cup FVoters

\* Blocks not associated with an height start with height set to -1.
\* @type: Set($height);
Heights == -1..(Cardinality(Blocks)-1)

\* The number of rounds the voters will participate in.
\* As genesis is already finalied in round 0, all voters start in round 1.
\* @type: Set($round);
Rounds == 0..MaxRound

\* Nil Value (returned by g(S) if no block has a supermajority).
\* @type: $block;
Nil == CHOOSE b : b \notin Blocks

(***************************************************************************)
(* Assume Statements                                                       *)
(***************************************************************************)

\* N = 3f + 1 where f is maximal amount of faulty voters (Byzantine).
\* he total number of voters equals the cardinaity of set of all voters.
ASSUME N = Cardinality(Voters)

\* Check that MaxRound is greater than 0.
ASSUME MaxRound > 0

\* Assume there exists blocks.
ASSUME Blocks /= {}

\* If there exists blocks we get a determinsitic genesis block.
\* @type: () => $block;
gen == CHOOSE b \in Blocks : TRUE

\* Symmetry for the correct voters set.
Symmetry == Permutations(CVoters)

(***************************************************************************)
(* This is a message-passing algorithm, so we begin by defining the set    *)
(* Message of all possible messages. The messages are explained below      *)
(* with the actions that send them.                                        *)
(***************************************************************************)
\* @type: Set($message);
Message == [voter: Voters, round: Rounds, block: Blocks, type: {"pv", "pc"}]

(***************************************************************************)
(* Protocol State Variables                                                *)
(***************************************************************************)
VARIABLES
    \* Height of a block.
    \* @type: $block -> $height;
    height,
    \* Mapping of blocks to its parent block.
    \* @type: $block -> $block;
    parent,
    \* Prevotes messages sent by the correct and faulty voters, mapped by rounds.
    \* @type: $round -> Set($message);
    prevotes,
    \* Precommits messages sent by the correct and faulty voters, mapped by rounds.
    \* @type: $round -> Set($message);
    precommits,
    \* The round number of a voter, called $r$ in the paper.
    \* @type: $voter -> $round;
    round,
    \* A voters view of last finalized block.
    \* @type: $voter -> $block;
    finalized,
    \* The voters step: "Prevote", "Precommit", "Done"
    \* @type: $voter -> $step;
    step,
    \* A voters view of their best GHOST prevote block, called $g(V_{r,v})$ in the paper.
    \* @type: $voter -> $block;
    ghost,
    \* A voters view of their best estimate, called $E_{r,v] in the paper.
    \* @type: $voter -> $block;
    estimate

\* Note: The algorithm incorporates a time variable to signify when a voter
\* can start a new round and when it is permitted to cast prevote and precommit.
\* Since this specification assumes an asynchronous network, all time-related
\* parameters are omitted.

\* Tuple of all the variables
vars == <<height, parent, 
          prevotes, precommits, 
          round, finalized, step, ghost, estimate>>

TypeOK ==
    /\ height \in [Blocks -> Heights]
    /\ parent \in [Blocks -> Blocks]
    \* This is not 100% correct because we don't verify that they belong to 
    \* the correct round and have correct status ("pv", "pc").
    /\ prevotes \in [Rounds -> SUBSET Message]
    /\ precommits \in [Rounds -> SUBSET Message]
    \* This method works, but is too slow.
    (*
    /\ \E PV \in SUBSET Message :
        prevotes = [r \in Rounds |-> {m \in PV : m.round = r /\ m.type = "pv"}]
    /\ \E PC \in SUBSET Message :
        precommits = [r \in Rounds |-> {m \in PC : m.round = r /\ m.type = "pc"}]
    *)
    /\ round \in [CVoters -> Rounds]
    /\ finalized \in [CVoters -> Blocks]
    /\ step \in [CVoters -> {"prevote", "precommit", "done"}]
    /\ ghost \in [CVoters -> Blocks]
    /\ estimate \in [CVoters -> Blocks]

(***************************************************************************)
(* Init                                                                    *)
(*  - Blocks (height, parent):                                             *)
(*      1. All blocks start with height = -1, except the genesis block,    *)
(*         which starts with height = 0.                                   *)
(*      2. Each block starts with itself as its parent.                    *)
(*  - Messages (prevotes and precommits):                                  *)
(*      1. Both prevote and precommit functions consists of empty set for  *)
(*         all rounds except 0 which have votes from all voters.           *)
(*  - Voters (round, finalized, and step):                                 *)
(*      1. Voters begin in round 1, having already voted for the genesis   *)
(*         block in round 0 (both prevote and precommit).                  *)
(*      2. Each voter starts with the genesis block as their finalized     *)
(*         block.                                                          *)
(*      3. Each voter start in the prevote state.                          *)
(*      4. Each voter start with ghost and estimate as genesis.            *)
(***************************************************************************)
Init == 
    \* Blocks
    /\ height = [[b \in Blocks |-> -1] EXCEPT ![gen] = 0]
    /\ parent = [b \in Blocks |-> b]
    \* Msgs
    /\ prevotes = [[r \in Rounds |-> {}] EXCEPT ![0] = {[block |-> gen, 
        round |-> 0, voter |-> n, type |-> "pv"] : n \in Voters}]
    /\ precommits = [[r \in Rounds |-> {}] EXCEPT ![0] = {[block |-> gen, 
        round |-> 0, voter |-> n, type |-> "pc"] : n \in Voters}]
    \* Voters
    /\ round = [v \in CVoters |-> 1]
    /\ finalized = [v \in CVoters |-> gen]
    /\ step = [v \in CVoters |-> "prevote"]
    /\ ghost = [v \in CVoters |-> gen]
    /\ estimate = [v \in CVoters |-> gen]

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
    \* Blocks
    /\ height = [[b \in Blocks |-> -1] EXCEPT ![gen] = 0]
    /\ parent = [b \in Blocks |-> b]
    \* Msgs
    \* non-deterministically initialize the messages (prevotes and precommits) 
    \* with faults
    /\ \E F1 \in SUBSET [block: Blocks, round: Rounds \ {0}, voter: FVoters, type : {"pv"}] :
        prevotes = [r \in Rounds |-> 
        IF r = 0 THEN 
            {[block |-> gen, round |-> r, voter |-> n, type |-> "pv"] : n \in Voters}
        ELSE 
            {m \in F1 : m.round = r}]
    /\ \E F2 \in SUBSET [block: Blocks, round: Rounds \ {0}, voter: FVoters, type : {"pc"}] :
        precommits = [r \in Rounds |-> 
        IF r = 0 THEN 
            {[block |-> gen, round |-> r, voter |-> n, type |-> "pc"] : n \in Voters}
        ELSE 
            {m \in F2 : m.round = r}]
    \* Voters
    /\ round = [v \in CVoters |-> 1]
    /\ finalized = [v \in CVoters |-> gen]
    /\ step = [v \in CVoters |-> "prevote"]
    /\ ghost = [v \in CVoters |-> gen]
    /\ estimate = [v \in CVoters |-> gen]
                
(***************************************************************************)
(* Block Production Protocol:                                              *)
(*  - TODO*)
(***************************************************************************)
(* P if Q (Q => P).                                                        *)
(* P only if Q (P => Q).                                                   *)
(* P if and only if Q (P => Q /\ Q => P).                                  *)
(***************************************************************************)

(***************************************************************************)
(* A block b is proposed if and only if (iff):                             *)
(*  - A block is considered proposed if it is part of the chain, meaning   *)
(*    it has been assigned a valid height (height[b] > -1).                *)
(***************************************************************************)
Proposed(b) ==
    /\ b\in Blocks
    /\ height[b] > -1

(***************************************************************************)
(* A block p is a valid parent for a block with height h iff:              *)
(*  - The parent block p has already been proposed (height[b] > -1).       *)
(*  - The parent block's height is exactly one less than h.                *)
(***************************************************************************)
ValidParent(p, h) == 
    /\ Proposed(p)
    /\ h - 1 = height[p]

(***************************************************************************)
(* Propose block b with parent p and height h if:                          *)
(*  - Block b is not the same as parent block p (b != p).                  *)
(*  - Block b is not already proposed (height[b] <= -1).                   *)
(*  - The parent block p is valid.                                         *)
(***************************************************************************)
propose(b, p, h) == 
    /\ height' = [height EXCEPT ![b] = h]
    /\ parent' = [parent EXCEPT ![b] = p]
        
Propose(b, p, h) ==
    /\ b \in Blocks
    /\ b /= p
    /\ ~Proposed(b)
    /\ ValidParent(p, h)
    /\ propose(b, p, h)
    /\ UNCHANGED <<round, prevotes, precommits, finalized, step, 
                   ghost, estimate>>

(***************************************************************************)
(* GRANDPA Protocol:                                                       *)
(*  - Uppercase always indicate that it is a set (there will be some sets  *)
(*    that combine upper and lower but will be obvious from context).      *)
(*      - S = A set of votes either PV (prevotes) or PC (precommits).      *)
(*      - EV = Equivocating votes based on S.                              *)
(*      - V = All honest votes (S \ EV).                                   *)
(*      - RV = Potential voters not observed in S (Voters \ S).            *)
(*        RV stands for remaining votes, can't use PV for potential votes  *)
(*        because PV stands for prevotes.                                  *)
(*  - If one of EV, V, RV contain PV or PC it indicates the type of votes. *)
(*  - In the context of V_{r,v} and C_{r,v} it means that we look at the   *)
(*    prevotes for V and precommits for C.                                 *)
(***************************************************************************)

(***************************************************************************)
(* Derive-Primary                                                          *)
(*  - Determines the primary voter for a given round.                      *)
(*  - The primary is typically selected deterministically, based on the    *)
(*    round number and a known, agreed-upon scheme (e.g., rotating order). *)
(*  - i mod n is the easiest method for rotating leader                    *)
(***************************************************************************)
DerivePrimary(r) == CHOOSE v : v \in Voters
    \* Use CHOOSE operator atm so no matter what round the same primary
    \* will be picked. (CHOOSE is determinisitic)

(***************************************************************************)
(* Equivocations:                                                          *)
(*  - A voter equivocates in a set of votes S if they cast more than one   *)
(*    vote in S.                                                           *)
(*  - A set S of votes is considered safe if the number of voters who      *)
(*    equivocate in S does not exceed f.                                   *)
(*  - Equivocations are counted as votes for every block, ensuring that    *)
(*    vote observation remains monotonic.                                  *)
(***************************************************************************)
\* @type: (Set($message)) => Set($voter);
CalculateEquivocations(S) == 
    {v \in Voters : (\E m1, m2 \in S : /\ m1 /= m2 
                                       /\ m1.voter = v 
                                       /\ m2.voter = v)}

(***************************************************************************)
(* Determine if block c is a descendant of block b.                        *)
(*  - Assumes each block maps to itself as its parent at protocol init.    *)
(*  - Return FALSE if b = c.                                               *)
(* Logic:                                                                  *)
(*  1. Both blocks must be proposed (round > -1).                          *)
(*  2. If parent[c] = b, then c is an descendant of b.                     *)
(*  3. If parent[c] = c, then c is the root block, and b is not an         *)
(*     ancestor of b.                                                      *)
(*  4. Otherwise, recursively check the parent of c.                       *)
(***************************************************************************)
RECURSIVE Descendant(_, _)
Descendant(b, c) ==
    /\ Proposed(b)
    /\ Proposed(c)
    /\ b /= c
    /\ IF 
            parent[c] = b
        THEN 
            TRUE
        ELSE 
            IF 
                parent[c] = c
            THEN 
                FALSE
            ELSE 
                Descendant(b, parent[c])


(***************************************************************************)
(* Calculate Direct and Indirect Votes for a block b:                      *)
(*  - Identify voters who directly support block through direct votes.     *)
(*  - Identify voters who indirectly support block b through descendants.  *)
(*  - Assumes the vote set V excludes equivocations.                       *)
(***************************************************************************)
\* @type: ($block, Set($message)) => Set($voter);
Votes(b, V) == 
    {v \in Voters : (\E m \in V : /\ m.voter = v 
                                  /\ \/ m.block = b
                                        \* Direct vote
                                     \/ Descendant(b, m.block))}
                                        \* Indirect vote

(***************************************************************************)
(* Calculate the GHOST Supermajority for a set of votes S:                 *)
(*  1. Identify voters that have equivocated in set S (EV).                *)
(*  2. Filter S to exclude those from the equivocating set EV (V).         *)
(*  3. Check if each block has a supermajority by combining:               *)
(*      a. Direct votes for the block.                                     *)
(*      b. Votes for descendants of the block (indirect votes).            *)
(*      c. Equivocations.                                                  *)
(*  4. Check that the Cardinality of union a, b, and c >= N - T (2*f + 1). *)
(*  5. Return all blocks that have supermajority.                          *)
(***************************************************************************)
(* Note: A set S is said to have a supermajority for a block B if the set  *)
(* of voters who either cast a vote for blocks >= B or equivocate in S     *)
(* has a size of at least (n + f + 1) / 2 = 2f + 1 = n - f.                *)
(***************************************************************************)
\* @type: (Set($message)) => Set($block);
GHOSTSupermajority(S) ==
    LET 
        EV == CalculateEquivocations(S)
        \* @type: Set($message);
        V == {m \in S : m.voter \notin EV}
            \* Votes for round r and type t, excluding those from equivocating 
            \* voters.
    IN 
        {b \in Blocks : Cardinality(Votes(b, V) \cup EV) >= N - T}
        \* Blocks with a supermajority through the union of direct votes, 
        \* descendant votes, and equivocations.
        \* The intersection of these sets should be the empty set.


(***************************************************************************)
(* GRANDPA-GHOST g(S):                                                     *)
(*  - The GHOST function selects the highest block in the chain that is    *)
(*    supported by a supermajority of votes in S.                          *)
(*  - S is either prevotes (PV) or precommits (PC).                        *)
(*  - GHOST = Greedy Heaviest Observed SubTree.                            *)
(* Logic:                                                                  *)
(*  - Determines the set of blocks with a supermajority of votes in the    *)
(*    set S using GHOSTSupermajority.                                      *)
(*  - If no such blocks exist, returns Nil.                                *)
(*  - Otherwise, selects the block with the greatest height from the set   *)
(*    of supermajority blocks.                                             *)
(***************************************************************************)
(* Note: The set S is a set of votes for a specific round and type.        *)
(* The type can be either prevote ("pv") or precommit ("pc").              *)
(***************************************************************************)
\* @type: (Set($message)) => $block;
GHOST(S) == 
    LET 
        B == GHOSTSupermajority(S) 
    IN 
        IF
            B = {}
        THEN 
            Nil
        ELSE 
            CHOOSE b \in B : (\A c \in B : height[b] >= height[c])
            \* Choose the block with greatest height.

(***************************************************************************)
(* Calculate the minimum of two naturals.                                  *)
(***************************************************************************)
\* @type: (Int, Int) => Int;
Min(x, y) == IF x <= y THEN x ELSE y

(***************************************************************************)
(* Calculate the set of not observed votes.                                *)
(*  - Given a set of votes S of either prevotes or precommits.             *)
(*  - FInd the voters that have not cast a vote in S.                      *)
(***************************************************************************)
\* @type: (Set($message)) => Set($voter);
NotObservedVote(S) == 
    {v \in Voters : (~\E m \in S : m.voter = v)}

(***************************************************************************)
(* Calculate Potential Equivocations for block b:                          *)
(* - This function calculates the number of potential equivocations        *)
(*   that can still occur for the block b, given the current votes (V)     *)
(*   and the set of already observed equivocations (EV).                   *)
(* - Potential equivocations are votes for block b that are neither        *)
(*   descendants of b nor equal to b itself.                               *)
(* - The result is the minimum between T and the sum of:                   *)
(*     1. The number of votes meeting the above criteria.                  *)
(*     2. The count of already observed equivocations for this round.      *)
(* Note: Assumes the vote set V excludes equivocations.                    *)
(***************************************************************************)
\* @type: ($block, Set($message), Set($voter)) => Int;
PotentialEquivocations(b, V, EV) ==
    LET 
        \* $type: Set($message)
        S == {m \in V : ~Descendant(b, m.block) /\ m.block /= b}
    IN
    Min(T, (Cardinality(S) + Cardinality(EV)))

(***************************************************************************)
(* Check if block b can achieve a supermajority of precommits:             *)
(*  - Determines whether block b can gather >= 2T + 1 precommit votes      *)
(*    (supermajority) by considering:                                      *)
(*      1. Direct and indirect (descendant) votes for block b in V.        *)
(*      2. Potential equivocations for block b, including equivocations EV.*)
(*      3. Remaining uncast votes RV which we assume support b.            *)
(* Note: Assumes the vote set V excludes equivocations.                    *)
(***************************************************************************)
\* @type: ($block, Set($message), Set($voter), Set($voter)) => Bool;
AchieveSupermajority(b, V, EV, RV) ==
    ((Cardinality(Votes(b, V)) 
    + PotentialEquivocations(b, V, EV) 
    + Cardinality(RV)) 
    >= (N - T))

(***************************************************************************)
(* Calculate Estimate (E_{r,v}):                                           *)
(*  - Represents a voters view of what could have been finalized in round  *)
(*    r based on the current state of prevotes and precommits.             *)
(*  - Derived from the last block in the chain headed by g(V_{r,v}) where  *)
(*    the precommits C_{r,v} could achieve a supermajority.                *)
(***************************************************************************)
(* Steps to calculate the estimate given PV and PC:                        *)
(*  1. Identify g = GHOST(PV), the head of the prevote GHOST.              *)
(*  2. Determine equivocating precommit voters in round r (EVPC).          *)
(*  3. Sort precommits for round r by excluding equivocators (VPC).        *)
(*  4. Identify voters that have not cast a precommit (RVPC).              *)
(*  5. Check if each block in the chain up-to g (or g itself) can achieve  *)
(*     a supermajority of precommits using these votes (2,3,4).            *)
(***************************************************************************)
(* Note:                                                                   *)
(*  1. If g = Nil (no GHOST head), the estimate is Nil.                    *)
(*  2. If C_{r,v} = {} and g != nil, the estimate defaults to g(V_{r,v})   *)
(*     as we assume all unobserved votes favor g(V_{r,v}).                 *)
(*  3. The round estimate is the highest block in the chain derived from   *)
(*     the prevote GHOST (g(V_{r,v})) that could achieve a supermajority   *)
(*     of precommits and thus be committed.                                *)
(***************************************************************************)
Estimate(PV, PC) == 
    LET 
        g == GHOST(PV)
        EVPC == CalculateEquivocations(PC)
            \* Set of equivocating precommits voters in round r.
        \* @type: Set($message);
        VPC == {m \in PC : m.voter \notin EVPC}
            \* Set of precommits for round r, excluding those from 
            \* equivocating voters.
        RVPC == NotObservedVote(PC)
            \* Set of precommits voters not observed for round r.
    IN 
        IF g = Nil THEN Nil ELSE
        LET 
            B == {b \in Blocks : 
                /\ \/ Descendant(b, g)
                   \/ b = g
                /\ AchieveSupermajority(b, VPC, EVPC, RVPC)}
                \* Set of blocks that can achieve a supermajority of precommits.
        IN 
            CHOOSE b \in B : (\A c \in B : height[b] >= height[c])
            \* highest block that can acheive a supermajority of precommits
            \* up to the g(V).

(***************************************************************************)
(* Finds the head of the chain starting from a given estimate e:           *)
(*  - The head is determined using a predefined rule (e.g., longest chain).*)
(*  - The resulting block must be a descendant of the starting block b or. *)
(*    be equal to block (it is already the lastest block in the chain).    *)
(***************************************************************************)
\* @type: ($block) => $block;
LongestChain(e) == 
    LET 
        B == {b \in Blocks : Descendant(e, b)} \cup {e}
    IN 
        CHOOSE b \in B : (\A c \in B : height[b] >= height[c])
            \* If multiple blocks have the same height the CHOOSE operator
            \* will CHOOSE the same block each time (deterministic).

(***************************************************************************)
(* Round Completable                                                       *)
(* - Way to safely conclude that estimate E_{r,v} >= for all B that might  *)
(*   be finalized in round r.                                              *)
(* Definition of Completable:                                              *)
(*  - A voter v considers round r completable if one of the following      *)
(*    conditions is met:                                                   *)
(*      1. E_{r,v} < g(V_{r,v}), or                                        *)
(*      2. It is impossible for the precommits C_{r,v} to form a           *)
(*         supermajority for any children of g(V_{r,v}). (b' > g(V_{r,v})) *)
(*  - These conditions guarantee that voter v can safely conclude that:    *)
(*    E_{r,v} >= B for all B that could be finalized in round r.           *)
(*  - This ensures that the round estimate is either an ancestor of the    *)
(*    prevote GHOST head or is the same block, and no child of this block  *)
(*    can possibly gather enough precommits.                               *)
(*  - A round r is completable when our estimate chain E_{r,v} contains    *)
(*    everything that could have been finzlied in round r.                 *)
(*  - Uses the same logic as calculating the estimate (E_{r,v}).           *)
(***************************************************************************)
(* Note: The first condition, E_{r,v} < g(V_{r,v}), is not required        *)
(* because it is implied by the second condition. However, the first       *)
(* condition does not imply the second. As a result, it is sufficient to   *)
(* check only the second condition, with the first condition serving as an *)
(* optimization.                                                           *)
(* Additionally, if the second condition is FALSE, the first condition     *)
(* will also be FALSE automatically. This is because voting for a block    *)
(* inherently includes a vote for all of its ancestor blocks.              *)
(* A child of g(V_{r,v}) can receive supermajority of precommits.          *)
(***************************************************************************)
Completable(r, v) ==
    \E PV \in SUBSET prevotes[r], PC \in SUBSET precommits[r] :
    /\ Cardinality(PV) >= N - T
    /\ Cardinality(PC) >= N - T
    /\ LET 
            g == GHOST(PV)
            e == Estimate(PV, PC)
            EVPC == CalculateEquivocations(PC)
                \* Equivocating precommits in round r
            \* @type: Set($message);
            VPC == {m \in PC : m.voter \notin EVPC}
                \* Precommits for round r, excluding those from 
                \* equivocating voters.
            RVPC == NotObservedVote(PC)
                \* Precommits not observed for round r.
        IN 
            /\ g /= Nil
            /\ e /= Nil
            /\ height[g] >= height[ghost[v]]
                \* It is important that we don't reduce our g(S) of prevotes
                \* since it can only increase over time when receiving more
                \* prevotes, unless we look at prevotes for rounds greater
                \* than our current round.
            /\ \/ height[e] < height[g]
               \/ LET CG == {b \in Blocks :
                    /\ Descendant(g, b)
                    /\ AchieveSupermajority(b, VPC, EVPC, RVPC)}
                    \* CG is the childrens of g(prevotes) that can receive a
                    \* supermajority of precommits.
                  IN 
                    CG = {}
            /\ ghost' = [ghost EXCEPT ![v] = g]
            /\ estimate' = [estimate EXCEPT ![v] = e]

(***************************************************************************)
(* Note:                                                                   *)
(*  - This approach relies on the following assumptions:                   *)
(*      1. When analyzing precommits, we know that honest voters observed  *)
(*         at least 2f + 1 prevotes for the block they precommitted to.    *)
(*      2. By the gossip assumption, all necessary prevotes will           *)
(*         eventually be received by all honest voters.                    *)
(*  - These conditions ensure that round r will eventually be completable. *)
(***************************************************************************)

(***************************************************************************)
(* Protocol Actions (The GRANDPA Algorithm)                                *)
(* - https://arxiv.org/pdf/2007.01560                                      *)
(* - https://spec.polkadot.network/sect-finality                           *)
(***************************************************************************)

(***************************************************************************)
(* Step 1: Start the next round (r + 1) iff:                               *)
(*  - Voter is at step "done" (already cast prevote and precommit).        *)
(*  - Round r is completable.                                              *)
(*  - The voter v has cast votes in all previous rounds (0..r).            *)
(*      - Should be implied by step[v] when it is equal to "done".         *)
(*  - Let t_r denote the time voter v starts round r + 1.                  *)
(***************************************************************************)
StartNewRound(v) ==
    /\ step[v] = "done"
    \* Bound the number of rounds for model checking.
    /\ round[v] + 1 \in Rounds
    /\ Completable(round[v], v)
    /\ round' = [round EXCEPT ![v] = @ + 1]
    /\ step' = [step EXCEPT ![v] = "prevote"]
    /\ UNCHANGED <<height, parent, prevotes, precommits, finalized>>

(***************************************************************************)
(* Step 2: Broadcast an Estimate (E_r{r-1,v}) for round r iff:             *)
(*  - Voter v is the primary for round r.                                  *)
(* Note: The Estimate (E_{r-1,v}) is based on prevotes and precommits      *)
(* from round r - 1.                                                       *)
(***************************************************************************)
PrimaryBroadcastEstimate(v) == 
    LET 
        \* @type: $block;
        e == estimate[v]
    IN
    /\ FALSE
        \* Might add this functionality but it's for liveness.

(***************************************************************************)
(* Step 3: Cast a prevote for round r iff:                                 *)
(*  - Voter is at step "prevote" (not cast a prevote in this round).       *)
(*  - The current time >= t_r + 2T, or round r is completable.             *)
(*  - Broadcast a prevote for the head of the chain containing:            *)
(*      - The Estimate (E_{r-1}), or a block B proposed by the primary,    *)
(*        where: g(V_{r-1}) >= B > E_{r-1}.                                *)
(***************************************************************************)
castprevote(r, v, b, t) ==
    LET 
        \* @type: $message;
        m == [voter |-> v, round |-> r, block |-> b, type |-> t]
    IN
        /\ prevotes' = [prevotes EXCEPT ![r] = @ \cup {m}]
        /\ step' = [step EXCEPT ![v] = "precommit"]
        /\ UNCHANGED <<height, parent,precommits, round, finalized, 
                       ghost, estimate>>

Castprevote(v) ==
    LET r == round[v] IN
    /\ step[v] = "prevote"
    /\ LET 
            b == LongestChain(estimate[v])
        IN 
            \* Find head of chain to cast a prevote for based on estimate
            \* from the previous round.
            /\ castprevote(r, v, b, "pv")

(***************************************************************************)
(* Step 4: Cast a precommit for round r iff:                               *)
(*  - Voter is at step "precommit" (not cast a precommit in this round).   *)
(*  - Enough prevotes have been received such that: g(V_r) >= E_{r-1}.     *)
(*  - The current time >= t_r + 4T, or round r is completable.             *)
(*  - Then cast a precommit for g(V_r).                                    *)
(*  - Update voter ghost view to g(V_r).                                   *)
(***************************************************************************)
castprecommit(r, v, b, t) ==
    LET 
        \* @type: $message;
        m == [voter |-> v, round |-> r, block |-> b, type |-> t]
    IN
        /\ precommits' = [precommits EXCEPT ![r] = @ \cup {m}]
        /\ step' = [step EXCEPT ![v] = "done"]
        /\ ghost' = [ghost EXCEPT ![v] = b]
            \* This is the only place where its possible for 
            \* g(V_{r,v}) < g(V_{r-1,v}). 
        /\ UNCHANGED <<height, parent, prevotes, round, finalized, 
                       estimate>>

Castprecommit(v) ==
    LET r == round[v] IN
    /\ step[v] = "precommit"
    /\ \E S \in SUBSET prevotes[r] : 
        /\ Cardinality(S) >= N - T
        /\ LET 
                g == GHOST(S)
                e == estimate[v]
           IN 
                IF g = Nil THEN FALSE ELSE 
                /\ height[g] >= height[e]
                /\ castprecommit(r, v, g, "pc")

(***************************************************************************)
\* Note: C_{r,v} and V_{r,v} may change with time (received more votes).
\* E_{r-1,v} can also change which is a function dependent on V_{r-1,v} and
\* C_{r-1,v} (if the voter sees more votes from the previous round).
(***************************************************************************)

(***************************************************************************)
(* Finalizable:                                                            *)
(* If for some round r, at any point after the precommit step of round r,  *)
(* we have that B = g(C_{r,v}) is later than our last finalized block and  *)
(* V_{r,v} has a supermajority, then we finalize B.                        *)
(*                                                                         *)
(* A voter v can update their finalized view to block b iff:               *)
(*  1. Block b have been finalized in a round r that is less than the      *)
(*     current round of voter v (i.e., round r was completable for v).     *)
(*     or we are at voters v round and the step is "done", this also means *)
(*     the current round is completable.                                   *)
(*  2. The height of block b is greater than the height of the current     *)
(*     finalized block.                                                    *)
(*  3. There is a supermajority of prevotes and precommits for block b     *)
(*     in round r.                                                         *)
(*  4. The current finalized block is an ancestor of block b.              *)
(*  5. If the above conditions (1,2,3,4) are satisfied, the voter updates  *)
(*     their finalized view to block b.                                    *)
(***************************************************************************)
Finalizable(r, v, b) == 
    \* Such that we can avoid checking for genesis round, which is
    \* automatically finalized.
    /\ r > 0
    /\ \/ r < round[v]
       \/ step[v] = "done" /\ round[v] = r
    /\ height[b] > height[finalized[v]]
    /\ \E PV \in SUBSET prevotes[r], PC \in SUBSET precommits[r] :
        /\ Cardinality(PV) >= N - T
        /\ Cardinality(PC) >= N - T
        /\ b \in GHOSTSupermajority(PV)
        /\ b \in GHOSTSupermajority(PC)
    /\ Descendant(finalized[v], b)
    /\ finalized' = [finalized EXCEPT ![v] = b]
    /\ UNCHANGED <<height, parent, prevotes, precommits, round, step,
                   ghost, estimate>>

(***************************************************************************)
(* Logic for a faulty voter.                                               *)
(*  - A faulty voter can vote for any block (does not need to be proposed).*)
(*  - The round must be > 0 as there is no reason to vote for any blocks   *)
(*    in round 0 as genesis is already GRANDPA finalized in round 0.       *)
(***************************************************************************)
FaultyStep == 
    \E v \in FVoters, b \in Blocks, r \in Rounds, t \in {"pv", "pc"} : 
            /\ r > 0
            /\ LET 
                    \* @type: $message;
                    m == [voter |-> v, round |-> r, block |-> b, type |-> t]
               IN 
                 /\ IF t = "pv" 
                    THEN 
                        /\ prevotes' = [prevotes EXCEPT ![r] = @ \cup {m}]
                        /\ precommits' = precommits
                    ELSE 
                        /\ precommits' = [precommits EXCEPT ![r] = @ \cup {m}]
                        /\ prevotes' = prevotes
                 /\ UNCHANGED <<height, parent, round, finalized, step,
                                ghost, estimate>>

(***************************************************************************)
(* Below are defined the next-state action and the complete spec.          *)
(***************************************************************************)
Environment == \E b, p \in Blocks : \E h \in Heights : Propose(b, p, h)

CorrectStep == \E v \in CVoters : 
                    \*\/ PrimaryBroadcastEstimate(v)
                    \/ Castprevote(v)
                    \/ Castprecommit(v)
                    \/ StartNewRound(v)
                    \*\/ \E b \in Blocks : \E r \in Rounds : 
                    \*        Finalizable(r, v, b)

System == CorrectStep \/ FaultyStep

Next == Environment \/ System

Spec == Init /\ [][Next]_vars

NextWithoutFaulty == Environment \/ CorrectStep

Spec2 == InitWithFaults /\ [][NextWithoutFaulty]_vars

(***************************************************************************)
(* A block is finalized if a quorum of voters voted for the block,         *)
(* i.e. it has a certificate of both prevotes and precommits.              *)
(*  - The block must be proposed (round != -1).                            *)
(*  - Needs to have a GHOST supermajority for both prevotes and precommits.*)
(*    in the same round.*)
(***************************************************************************)
Finalized(b, r) == 
    /\ Proposed(b)
    /\ b \in GHOSTSupermajority(prevotes[r])
    /\ b \in GHOSTSupermajority(precommits[r])

(***************************************************************************)
(* Invariants (Safety)                                                     *)
(***************************************************************************)

\* Verify that for all rounds r the amount of equivocations does not exceed
\* the boundary of T for both prevotes and precommits.
\* If equivocations is <= T in a set of votes then the set is said to be safe.
SafeSet == \A r \in Rounds :
                /\ Cardinality(CalculateEquivocations(prevotes[r])) <= T
                    \* prevotes
                /\ Cardinality(CalculateEquivocations(precommits[r])) <= T
                    \* precommits

\* If two blocks are finalized in the same round they must be the same block,
\* or they must lay on the same chain.
\* In GRANDPA it is possible to finalize multiple blocks in one round.
NonConflictingRoundFinalized == \E b1, b2 \in Blocks : \E r \in Rounds :
                                    /\ Finalized(b1, r) 
                                    /\ Finalized(b2, r) 
                                    => 
                                    \/ b1 = b2
                                    \/ Descendant(b1, b2) 
                                    \/ Descendant(b2, b1)

\* No conflicting finalized chains exists
\* For all finalized blocks b1 and b2 they must either be the same block or
\* b1 must be a descendant of b2 or b2 must be a descendant of b1.
\* This makes sure that all finalized blocks (no matter what round) is
\* part of the same chain.
NonConflictingChains == \A b1, b2 \in Blocks : \E r1, r2 \in Rounds : 
                            /\ Finalized(b1, r1) 
                            /\ Finalized(b2, r2) 
                            => 
                            \/ b1 = b2 
                            \/ Descendant(b1, b2) 
                            \/ Descendant(b2, b1)

\* NoConflictingEstimates states that for all v1 and v2 in CVoters,  
\* at least one of the following must hold:  
\* 1. The estimates of v1 and v2 are the same.  
\* 2. The estimate of v1 is a descendant of the estimate of v2.  
\* 3. The estimate of v2 is a descendant of the estimate of v1.  
NoConflictingEstimates == \A v1, v2 \in CVoters :
                            \/ estimate[v1] = estimate[v2]
                            \/ Descendant(estimate[v1], estimate[v2])
                            \/ Descendant(estimate[v2], estimate[v1])

\* For all honest voters that sees round r completable then round 0..r-1 
\* must be completable.
CompletableCheck == TRUE

(***************************************************************************)
(* Temporal Properties (Liveness)                                          *)
(***************************************************************************)

=============================================================================