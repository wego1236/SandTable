----------------------------  MODULE rsRaft ----------------------------- 
(***************************************************************************)
(* This is the TLA+ specification for Raft-RS in TiKV with version 0.7.0   *)
(*                                                                         *)
(* - Leader election:                                                      *)
(* - Log replication:                                                      *)
(*                                                                         *)
(* Currently, the specification assumes:                                   *)
(* - No snapshots                                                          *)
(* - No read-only requests                                                 *)
(* - No non-voting nodes                                                   *)
(* - No disk failures                                                      *)
(* - No membership change                                                  *)
(***************************************************************************)

EXTENDS Sequences, Naturals, Integers, FiniteSets, TLC, SequencesExt

(***************************************************************************)
(* Constants definitions                                                   *)
(***************************************************************************)
\* The set of servers
CONSTANT Servers
\* Server states, Corresponding to raft-rs StateRole
CONSTANTS Follower, Candidate, Leader 
\* Raft message types
CONSTANTS M_RV, M_RVR, M_AE, M_AER, M_PRV, M_PRVR, M_HB, M_HBR, M_SNAP
\* The set of commands
CONSTANTS Commands 
\* The abstraction of null operation
CONSTANTS NoOp
\* Misc: state constraint parameters and placeholder
CONSTANTS Nil  
\* The set of ProgressState
CONSTANTS Probe, Replicate, Snapshot

(***************************************************************************
  Variables definitions
 ***************************************************************************)
\* Persistent state on all servers
VARIABLES currentTerm,                 \* Latest term server has seen (initialized to 0 on first boot, increases monotonically) , Corresponding to raft-rs RaftCore.term
          votedFor,                    \* CandidateId that received vote in current term (or null if none), Corresponding to raft-rs RaftCore.vote
          log                          \* Log entries; each entry contains command for state machine, and term when entry was received by leader, Corresponding to raft-rs RaftCore.raft_log

\* Snapshot metadata
VARIABLES snapshotLastIdx,  \* the last entry in the log the snapshot replaces
          snapshotLastTerm  \* the term of this entry

\* Volatile state on all servers
VARIABLES raftState,                   \* State of servers, in {Follower, Candidate, Leader} , Corresponding to raft-rs RaftCore.state
          commitIndex,                 \* Index of highest log entry known to be committed
          leader_id                    \* The potential leader of the cluster, Corresponding to raft-rs RaftCore.leader_id


\* Volatile state on leader     
VARIABLES nextIndex,                   \* for each server, index of the next log entry to send to that  server, Corresponding to raft-rs Progress.next_idx
          matchIndex                   \* for each server, index of highest log entry known to be replicated on server, Corresponding to raft-rs Progress.matched

\* intermediate variable
VARIABLES voted_for_me   \* Record nodes that have voted for me, Corresponding to raft-rs Progress.voted
VARIABLES voted_reject   \* Record nodes that have not voted for me, Corresponding to raft-rs Progress.voted
VARIABLES check_quorum   \* check_quorum variables
VARIABLE progress        \* The status of each follower's receive log, which is used in receiving append, which contains probe and replicate. Corresponding to raft-rs Progress.state
VARIABLE inflight        \* Number of letters transmitted during the recording process. Corresponding to raft-rs Progress.int (Inflights)  
VARIABLE pending_snapshot 
VARIABLES pr_pending



(***************************************************************************
  Network variables and instance
 ***************************************************************************)
\* The network is modelled through these variables
VARIABLES netman, 
          netcmd,
          msgs
INSTANCE FifoNetwork WITH FLUSH_DISCONN <- TRUE, NULL_MSG <- Nil,
    _msgs <- msgs, _netman <- netman, _netcmd <- netcmd


(***************************************************************************)
(* Self manipulated invariants checking                                    *)
(***************************************************************************)
VARIABLES inv \* Invariants that guarantee correctness

(***************************************************************************)
(* Vars groups                                                             *)
(***************************************************************************)
serverVars    == <<currentTerm, votedFor, raftState>>
leaderVars    == <<nextIndex, matchIndex>>
candidateVars == <<voted_for_me, voted_reject>>
logVars       == <<log, commitIndex>>
snapVars      == <<snapshotLastIdx, snapshotLastTerm>>
nodeVars      == <<leader_id, check_quorum, progress, inflight, pending_snapshot, pr_pending>>
netVars       == <<netman, netcmd, msgs>>
noNetVars     == <<serverVars, leaderVars, candidateVars, logVars, nodeVars, snapVars>>
vars          == <<noNetVars, netVars, inv>>


(***************************************************************************)
(* State constraints helper                                                *)
(***************************************************************************)
CONSTANTS Parameters  \* to control the model scale

GetParameterSet(p)  == IF p \in DOMAIN Parameters THEN Parameters[p] ELSE {}

CheckParameterHelper(n, p, Test(_,_)) ==
    IF p \in DOMAIN Parameters
    THEN Test(n, Parameters[p])
    ELSE TRUE
CheckParameterMax(n, p) == CheckParameterHelper(n, p, LAMBDA i, j: i <= j)

PrePrune(n, p) == CheckParameterHelper(n, p, LAMBDA i, j: i < j)


(***************************************************************************)
(* Type Ok. Used as a check on writing format                              *)
(***************************************************************************)

TypeOkServerVars == 
    /\ currentTerm \in [ Servers -> Nat ]
    /\ votedFor    \in [ Servers -> Servers \cup {Nil} ]
    /\ raftState   \in [ Servers -> { Follower, Candidate, Leader } ] 

TypeOkLeaderVars ==
    /\ nextIndex   \in [ Servers -> [ Servers -> Nat \ {0} ]]
    /\ matchIndex  \in [ Servers -> [ Servers -> Nat ]]

\* TypeOkCandidateVars ==
\*     /\ votesGranted  \in [ Servers -> {} ]

TypeOkLogVars ==
    \* log data structure is complex, we skip checking it
    /\ commitIndex \in [ Servers -> Nat ]

TypeOk ==
    /\ TypeOkServerVars
    /\ TypeOkLeaderVars
    /\ TypeOkLogVars


(***************************************************************************
  Init variables
 ***************************************************************************)
InitServerVars ==
    /\ currentTerm = [ i \in Servers |-> 1 ]
    /\ votedFor    = [ i \in Servers |-> Nil ]
    /\ raftState   = [ i \in Servers |-> Follower ]

InitLeaderVars ==
    /\ nextIndex  = [ i \in Servers |-> [ j \in Servers |-> 1 ]]
    /\ matchIndex = [ i \in Servers |-> [ j \in Servers |-> 0 ]]

InitCandidateVars ==
    /\ voted_for_me = [ i \in Servers |-> {} ]
    /\ voted_reject = [ i \in Servers |-> {} ]

InitLogVars ==
    /\ log = [ i \in Servers |-> << [term |-> 1, data |-> Nil, index |-> 1]>> ]
    /\ commitIndex = [ i \in Servers |-> 1 ]
InitInv == inv = <<>>

InitSnapShotVars == 
    /\ snapshotLastIdx = [ i \in Servers |-> 0 ]
    /\ snapshotLastTerm = [ i \in Servers |-> 0 ]

InitNodeVars ==  
    /\ leader_id = [ i \in Servers |-> Nil]
    /\ check_quorum = [i \in Servers |-> FALSE]  \* Used to determine if check_quorum is on
    /\ progress = [ i \in Servers |-> [ j \in Servers |-> <<Probe, FALSE>>]] 
    /\ inflight = [ i \in Servers |-> [ j \in Servers |-> 0 ]]
    /\ pr_pending = [ i \in Servers |-> [ j \in Servers |-> 0 ]]
    /\ pending_snapshot = [ i \in Servers |-> 0]

InitNetVars ==
    /\ InitFifoNetworkAddNetman(Servers, <<"Init", Cardinality(Servers)>>, 
                [n_elec |-> 0, n_ae |-> 0, n_hb |-> 0, n_op |-> 0, n_restart |-> 0, n_rqSnap |-> 0,    n_becomeLeader |-> 0, no_inv |-> GetParameterSet("NoInv")])


Init ==
    /\ InitServerVars
    /\ InitLeaderVars
    /\ InitCandidateVars
    /\ InitLogVars
    /\ InitInv
    /\ InitNodeVars
    /\ InitNetVars
    /\ InitSnapShotVars

(***************************************************************************
  Helper functions
 ***************************************************************************)
NumServer == Cardinality(Servers)

Min(x,y) == IF x < y THEN x ELSE y
Max(x,y) == IF x < y THEN y ELSE x

IsQuorum(ss) == Cardinality(ss) * 2 > Cardinality(Servers)
IsQuorumNum(num) == num * 2 > Cardinality(Servers)

CheckStateIs(n, s)   == raftState[n] = s
CheckStateIsNot(n, s) == raftState[n] /= s

Update(var, n, value) == [var EXCEPT ![n] = value]
UpdateCurrentTerm(n, term) == currentTerm' = Update(currentTerm, n, term)
UpdateLeaderId(n, id) == leader_id' = Update(leader_id, n, id)
UpdatePendingSnap(n, snap_num) == pending_snapshot' = Update(pending_snapshot, n, snap_num)
UpdateVotedFor(n, node) == votedFor' = Update(votedFor, n, node)
UpdateState(n, s) == raftState' = Update(raftState, n, s)
UpdateVotedForMe(n, value) == voted_for_me' = Update(voted_for_me, n, value)
AddVotedForMe(me, node) == voted_for_me' = [ voted_for_me EXCEPT ![me] = @ \cup {node} ]
ClearVotedForMe(me) == voted_for_me' = [ voted_for_me EXCEPT ![me] = {} ]
UpdateVotesReject(n, value) == voted_reject' = Update(voted_reject, n, value)
AddVotesReject(me, node) == voted_reject' = [ voted_reject EXCEPT ![me] = @ \cup {node}]
ClearVotesReject(me) == voted_reject' = [ voted_reject EXCEPT ![me] = {} ]
UpdateMatchIdx(me, node, idx) == matchIndex' = [ matchIndex EXCEPT ![me][node] = idx ]
UpdatePrPending(me, node, idx) == pr_pending' = [ pr_pending EXCEPT ![me][node] = idx ]
UpdateNextIdx(me, node, idx) == nextIndex' = [ nextIndex EXCEPT ![me][node] = IF idx < 1 THEN 1 ELSE idx ]
UpdateProgress(me, node, state) == progress' = [progress EXCEPT ![me][node] = state ]
UpdateInflight(me, node, num) == inflight' = [inflight EXCEPT ![me][node] = num ]
UpdateCommitIdx(n, idx) == commitIndex' = Update(commitIndex, n, idx)
UpdateSnapIdx(me, idx) == snapshotLastIdx' = Update(snapshotLastIdx, me, idx)
UpdateSnapTerm(me, term) == snapshotLastTerm' = Update(snapshotLastTerm, me, term)
AllUpdateNextIdx(me, idx) ==
    LET f == [i \in Servers |-> idx]
    IN  nextIndex' = [nextIndex EXCEPT ![me] = f]
AllUpdateMatchIdx(me, idx) == 
    LET f == [i \in Servers |-> idx]
    IN  matchIndex' = [matchIndex EXCEPT ![me] = f]
AllUpdateProgress(me, prstate) == 
    LET f == [i \in Servers |-> prstate]
    IN  progress' = [progress EXCEPT ![me] = f]
AllUpdateInflight(me, num_msg) == 
    LET f == [i \in Servers |-> num_msg]
    IN  inflight' = [inflight EXCEPT ![me] = f]
AllUpdatePrPending(me, pending) == 
    LET f == [i \in Servers |-> pending]
    IN  pr_pending' = [pr_pending EXCEPT ![me] = f]

(***************************************************************************)
(* Log helpers                                                             *)
(***************************************************************************)
\* idx = 1, data = Nil  
LogAppend(log_, entry) == Append(log_, entry)

LogCount(log_) == Len(log_) 

\* originale version, withous snapshot, only for simple log
LogGetEntry(log_, idx) ==
    IF idx > LogCount(log_) \/ idx <= 0 
    THEN Nil 
    ELSE log_[idx]
LogGetEntryOne(log_, idx) ==
    IF idx > LogCount(log_) \/ idx <= 0 
    THEN <<>>
    ELSE SubSeq(log_, idx, idx)
LogGetEntriesFrom(log_, idx) ==
    IF idx > LogCount(log_) \/ idx <= 0 THEN <<>>
    ELSE SubSeq(log_, idx, LogCount(log_))
LogGetEntriesTo(log_, idx) ==
    IF Len(log_) < idx THEN log_
    ELSE SubSeq(log_, 1, idx)


\* Get last idx of server s.
LastIdx(log_, n) == 
    IF LogCount(log_) = 0
    THEN snapshotLastIdx'[n]
    ELSE log_[LogCount(log_)].index \* last entry's idx

FirstIdx(log_, n) ==
    IF LogCount(log_) = 0
    THEN snapshotLastIdx[n] + 1
    ELSE log_[1].index

TruncatedIdx(log_, idx, n) == \* 用作现有idx 经过压缩之后 获得真正的log索引
    LET firstIdx == FirstIdx(log_, n)
        lastIdx == LastIdx(log_, n)
        newIndex == idx - firstIdx + 1 \* 这里和 raft-rs不同的是 我们是从下标1 开始统计， raftrs是从下标0
    IN  IF idx > lastIdx \/ idx < firstIdx
        THEN -1 
        ELSE newIndex


\* used in server's real log, because of snapshot
LogGetEntry2(log_, idx, n) ==
    LET newIndex == TruncatedIdx(log_, idx, n)
    IN  IF newIndex = -1
        THEN Nil 
        ELSE log_[newIndex]
    
LogGetEntryOne2(log_, idx, n) ==
    LET newIndex == TruncatedIdx(log_, idx, n)
    IN  IF newIndex = -1
        THEN <<>>
        ELSE SubSeq(log_, newIndex, newIndex)
    
LogGetEntriesFrom2(log_, idx, n) ==
    LET newIndex == TruncatedIdx(log_, idx, n)
    IN  IF newIndex = -1
        THEN <<>>
        ELSE SubSeq(log_, newIndex, LogCount(log_))

  
LogGetEntriesTo2(log_, idx, n) ==
    LET newIndex == TruncatedIdx(log_, idx, n)
    IN  IF newIndex = -1
        THEN <<>>
        ELSE SubSeq(log_, 1, newIndex)

LogGetTerm2(log_, idx, info, n) ==
    LET newIndex == TruncatedIdx(log_, idx, n)
    IN  IF newIndex = -1
        THEN 0
        ELSE IF newIndex = 0 THEN 0 ELSE log_[newIndex].term
    
\* LogDeleteEntriesFrom(log_, idx, base ) == 
\*     LET newIdx == idx - base
\*     IN SubSeq(log_, 1, newIdx - 1)
    
LogCurrentIdx(log_, n) == LastIdx(log_, n)


LogLastTerm(log_, n) ==
    LET idx == TruncatedIdx(log_, LastIdx(log_, n), n)
        term == 
            IF idx = -1 
            THEN snapshotLastTerm[n]
            ELSE IF idx = 0
                 THEN 0
                 ELSE log_[idx].term 
    IN term

\* just for temp log
LogLastIdx(log_) ==
    LET idx == LogCount(log_)
        index == IF idx = 0 THEN 0 ELSE log_[idx].index
    IN index




\* log_ is the log of the original node, entries is the logs that need to be added in the AE letter, we need to find a suitable location to overwrite the conflicting logs according to the incoming prevLogIdx, and add the subsequent logs.  
\* in maybe_append@raft_log.rs 
LogGetMatchEntries(log_, entries, prevLogIdx, n) ==
    LET F[i \in 0..Len(entries)] ==
            IF i = 0 THEN Nil
            ELSE LET ety1 == LogGetEntry2(log_, prevLogIdx + i, n) \* Original log Entry at prevLogIdx + i
                     ety2 == LogGetEntry(entries, i)\* The entries ith one to be added
                     entries1 == LogGetEntriesTo2(log_, prevLogIdx + i - 1, n)  \* log_ from first_index to prevLogIdx + i - 1
                     entries2 == LogGetEntriesFrom(entries, i) \* entries from i to Len(entries)
                 IN IF /\ F[i-1] = Nil
                       /\ \/ ety1 = Nil  \* The original log does not have the ith one, indicating that all subsequent ones need to be added directly.
                          \/ ety1.term /= ety2.term \* The i-th mismatch of the original log indicates that it needs to be overwritten from the i-th onwards with all newly added
                    THEN entries1 \o entries2
                    ELSE F[i-1]
        result == F[Len(entries)]
    IN IF result = Nil THEN log_ ELSE result  


(***************************************************************************)
(* Msg constructors                                                        *)
(***************************************************************************)
\* Send the letter to the remaining nodes, constructing the letter according to the rules of the Contrustor2/3 function
_BatchExcludesReqMsgsArg(n, excludes, Constructor2(_, _), Constructor3(_, _, _), arg) ==
    LET dsts == Servers \ excludes
        size == Cardinality(dsts)
        F[i \in 0..size] ==
            IF i = 0 THEN <<<<>>, dsts>>
            ELSE LET ms == F[i-1][1]
                     s == CHOOSE j \in F[i-1][2]: TRUE
                     m == IF arg = Nil
                          THEN Constructor2(n, s)
                          ELSE Constructor3(n, s, arg)
                     remaining == F[i-1][2] \ {s}
                 IN <<Append(ms, m), remaining>>
    IN F[size][1]

_Dummy2(a, b) == TRUE
_Dummy3(a, b, c) == TRUE

BatchReqMsgs(n, Constructor(_, _)) ==
    _BatchExcludesReqMsgsArg(n, {n}, Constructor, _Dummy3, Nil)
BatchReqMsgsArg(n, Constructor(_, _, _), arg) ==
    _BatchExcludesReqMsgsArg(n, {n}, _Dummy2, Constructor, arg)
ConstructMsg(src, dst, type, body) ==
    [ src |-> src, dst |-> dst, type |-> type, data |-> body ]

\* func：new_message(MsgRequestVote)@raft.rs  
RequestVote(i, j) ==  
    LET body == [ term |-> currentTerm'[i],
                  candidate_id |-> i,
                  index |-> LogCurrentIdx(log[i], i),
                  log_term |-> LogLastTerm(log[i], i),
                  commit |-> commitIndex[i],
                  commitTerm |-> LogGetTerm2(log[i], commitIndex[i], "RequestVote", i)]
        msg_type ==  M_RV
    IN ConstructMsg(i, j, msg_type, body)

\* func：new_message(MsgRequestVoteResponse)@raft.rs   
RequestVoteResponse(m, voted, tempLeaderId) ==  
    LET i == m.dst
        j == m.src
        req == m.data    
        \* can_vote corresponding to step()@raft.rs, which define the situation it can vote or not
        can_vote == \/ voted = j
                    \/ /\ voted = Nil
                       /\ tempLeaderId = Nil 
        meTerm == currentTerm'[i]
        rejectMeTermIsBigger == meTerm > req.term
        meLastTerm == LogLastTerm(log[i], i)
        rejectMeLogNewer == \/ req.log_term < meLastTerm
                            \/ /\ req.log_term = meLastTerm
                               /\ req.index < LogCurrentIdx(log[i], i)        
        voteStatus == IF rejectMeTermIsBigger THEN "not-vote: term bigger"   ELSE
                      IF ~can_vote            THEN "not-vote: can not vote" ELSE
                      IF rejectMeLogNewer     THEN "not-vote: log newer"     ELSE "voted"
        granted == voteStatus = "voted"
        reject == ~granted
        send_commit == IF reject THEN commitIndex[i] ELSE 0
        send_commit_term == IF reject THEN LogGetTerm2(log[i], commitIndex[i], "RequestVoteResponse", i) ELSE 0
        body == [ request_term |-> req.term,
                  term |-> Max(req.term, meTerm),
                  reject |-> reject,
                  commit |-> send_commit,
                  commitTerm |-> send_commit_term]
    IN ConstructMsg(i, j, M_RVR, body) @@ [ status |-> voteStatus ]



SendSnapshot(i, j) ==
    LET meteIdx == commitIndex'[i]
        metaTerm == IF commitIndex'[i] > snapshotLastIdx'[i]
                    THEN LogGetTerm2(log[i], commitIndex'[i], "SendSnapshot", i)
                    ELSE snapshotLastTerm'[i]
        body    == [ term           |-> currentTerm[i],
                     metaIndex        |-> meteIdx,
                     metaTerm       |-> metaTerm ]
    IN ConstructMsg(i, j, M_SNAP, body) 

\* func: prepare_send_entries 
AppendEntriesNext(i, j, next) ==   
    LET prev_log_idx == next[i][j] - 1
        body == [ term |-> currentTerm'[i],
                leader_id |-> i,
                commit |-> commitIndex'[i],
                index |->  prev_log_idx,  \* prev_log_idx
                log_term |-> IF LastIdx(log'[i], i) >= prev_log_idx 
                            THEN LogGetTerm2(log'[i], prev_log_idx, "AppendEntriesNext",  i) 
                            ELSE 0 ,
                entries |-> LogGetEntryOne2(log'[i], next[i][j], i) ]  \* The model restricts AppendEntry messages to one entry at a time.
   IN ConstructMsg(i, j, M_AE, body)


\* func: send_heartbeat 
HeartBeatNext(i, j, next) ==  
    LET body == [ term |-> currentTerm[i],
                  commit |-> Min(matchIndex[i][j], commitIndex[i])]
    IN ConstructMsg(i, j, M_HB, body)

HeartBeatResponse(m) ==
    LET body == [ term |-> currentTerm'[m.dst],
                  commitIdx |-> commitIndex'[m.dst] ]
    IN ConstructMsg(m.dst, m.src, M_HBR, body)

\* new_message(MsgAppendResponse)@raft.rs  
AERFailLogStale(m) ==  \* func: handle_append_entries
    LET body == [ reject |-> FALSE,
                  term |-> Max(currentTerm[m.dst], m.data.term),
                  index |-> commitIndex[m.dst],
                  re |-> Nil,                 
                  commit |-> commitIndex[m.dst] ]
    IN ConstructMsg(m.dst, m.src, M_AER, body)

\* new_message(MsgAppendResponse)@raft.rs  
AERFailTermMismatch(m, hint_index, hint_term) ==
    LET body == [ reject |-> TRUE,
                  term |-> Max(currentTerm[m.dst], m.data.term),  
                  index |-> m.data.index,  
                  reject_hint |-> hint_index,           
                  log_term |-> hint_term,
                  request_snapshot |-> 0, 
                  commit |-> commitIndex[m.dst] ]
    IN ConstructMsg(m.dst, m.src, M_AER, body)

SnapFail(m) == 
    LET body == [ reject |-> FALSE,
                  term |-> currentTerm'[m.dst],
                  request_snapshot |-> 0, 
                  index |-> commitIndex'[m.dst] ]
    IN ConstructMsg(m.dst, m.src, M_AER, body)

SnapSuccess(m) == 
    LET body == [ reject |-> FALSE,
                  term |-> currentTerm'[m.dst],
                  request_snapshot |-> 0, 
                  index |-> snapshotLastIdx'[m.dst] ] \* 这里不能使用 lastidx 因为我们的log 设计问题，这里log清除之后一定是这个使用snap 我们简化为这个
    IN ConstructMsg(m.dst, m.src, M_AER, body)

\* new_message(MsgAppendResponse)@raft.rs  
AppendEntriesResponseSuccess(m) == 
    LET data == m.data
        body == [ reject |-> FALSE,
                  term |-> currentTerm'[m.dst],
                  index |-> data.index + Len(data.entries),
                  commitIdx |-> commitIndex'[m.dst]]
    IN ConstructMsg(m.dst, m.src, M_AER, body)


\* At bcast_append the next_index of the node to the target node is updated for each letter.(in prepare_send_entries@raft.rs) 
BatchUpdateNextWithMsg(n, new_msgs) ==
    LET lenMsg == Len(new_msgs)
        F[i \in 0..lenMsg] ==
            IF i = 0 THEN <<{}, Servers, (n :> 1)>>
            ELSE LET dst == new_msgs[i].dst
                     ety == new_msgs[i].data.entries
                     etyLastIdx == LogLastIdx(ety)
                IN IF \/ ety = <<>> \* If the content of the letter is empty, no need to update
                      \/ progress[n][dst][1] = Probe \* If a node is in the Probe state, sending at this point will block( maybe_send_append().is_paused() @ raft.rs)
                   THEN <<F[i-1][1] , F[i-1][2], F[i-1][3] @@ (dst :> etyLastIdx) >> 
                   ELSE <<F[i-1][1] \cup {n}, F[i-1][2] \ {n}, F[i-1][3] @@ (dst :> etyLastIdx)>>
        updateServer == F[lenMsg][1]
        remainServer == F[lenMsg][2]
        updateMap == F[lenMsg][3]
        next_keep == [ s \in remainServer |-> nextIndex[n][s] ] 
        next_update == [ s \in updateServer |-> updateMap[s] ] 
    IN nextIndex' = [ nextIndex EXCEPT ![n] = next_keep @@ next_update ]



(***************************************************************************)
(* Raft actions                                                            *)
(***************************************************************************)

\* func reset
reset(i) == 
    /\ ClearVotedForMe(i)
    /\ ClearVotesReject(i)
    /\ AllUpdateNextIdx(i, LastIdx(log[i], i) + 1)
    /\ AllUpdateMatchIdx(i, 0)
    /\ AllUpdateProgress(i, <<Probe, FALSE>>)
    /\ AllUpdateInflight(i, 0)
    /\ AllUpdatePrPending(i, 0)

(***************************************************************************)
(* Become candidate                                                        *)
(***************************************************************************)

\* func: become_candidate
BecomeCandidate(i) ==  
    /\ UpdateCurrentTerm(i, currentTerm[i] + 1)
    /\ UpdateVotedFor(i, i)
    /\ UNCHANGED << check_quorum, logVars, snapVars>>
    /\ reset(i)
    /\ UpdatePendingSnap(i, 0)
    /\ UpdateLeaderId(i, Nil)
    /\ UpdateState(i, Candidate)
    /\ LET ms == BatchReqMsgs(i, RequestVote)
       IN NetUpdate2(NetmanIncField("n_elec", NetBatchAddMsg(ms)), <<"BecomeCandidate", i>>)



(***************************************************************************)
(* Become leader                                                           *)
(***************************************************************************)

\* func: become_leader@raft.rs
BecomeLeader(i, m) ==  
    /\ LET noop == [ term |-> currentTerm[i], data |-> Nil, index |-> LastIdx(log[i], i) + 1 ]
       IN log' = Update(log, i, LogAppend(log[i], noop))
    /\ UpdateState(i, Leader)
    /\ UpdateLeaderId(i, i)
    /\ ClearVotedForMe(i)
    /\ UpdatePendingSnap(i, 0)
    /\ ClearVotesReject(i)
    /\ matchIndex' = [ matchIndex EXCEPT ![i] = ( i :> LastIdx(log'[i], i) ) @@ [ j \in Servers |-> 0 ] ] 
    /\ AllUpdateProgress(i, <<Probe, TRUE>>) \* All progress needs to be in probe mode  
    /\ AllUpdateInflight(i, 0) \* All inflight needs to be 0 (no message send)
    /\ AllUpdatePrPending(i, 0) \* All pr.pending_request_snapshot needs to be 0 
    /\ LET next == [ nextIndex EXCEPT ![i] = ( i :> matchIndex'[i][i] + 1 ) @@ [ j \in Servers |-> LastIdx(log[i], i) + 1] ]
           ms == BatchReqMsgsArg(i, AppendEntriesNext, next)
       IN  /\ nextIndex' = next 
           /\ NetUpdate2(NetReplyBatchAddMsg(ms, m), <<"RecvRequestVoteResponse", "Won-BecomeLeader", i>>) \* bcast_send

\* func: become_leader@raft.rs
BecomeLeader1(i) ==  
    /\ UNCHANGED << commitIndex, snapVars,  votedFor, check_quorum>> 
    /\ LET new_term == currentTerm[i] + 1
           noop == [ term |-> new_term, data |-> Nil, index |-> LastIdx(log[i], i) + 1 ]
       IN log' = Update(log, i, LogAppend(log[i], noop))
    /\ UpdateState(i, Leader)
    /\ UpdateLeaderId(i, i)
    /\ UpdatePendingSnap(i, 0)
    /\ UpdateCurrentTerm(i, currentTerm[i] + 1)
    /\ ClearVotedForMe(i)
    /\ ClearVotesReject(i)
    /\ matchIndex' = [ matchIndex EXCEPT ![i] = ( i :> LastIdx(log'[i], i) ) @@ [ j \in Servers |-> 0 ] ] 
    /\ AllUpdateProgress(i, <<Probe, TRUE>>) \* All progress needs to be in probe mode  
    /\ AllUpdateInflight(i, 0) \* All inflight needs to be 0 (no message send)
    /\ AllUpdatePrPending(i, 0) \* All pr.pending_request_snapshot needs to be 0 
    /\ LET next == [ nextIndex EXCEPT ![i] = ( i :> matchIndex'[i][i] + 1 ) @@ [ j \in Servers |-> LastIdx(log[i], i) + 1] ]
           ms == BatchReqMsgsArg(i, AppendEntriesNext, next)
       IN  /\ nextIndex' = next 
           /\ NetUpdate2(NetmanIncField("n_becomeLeader", NetBatchAddMsg(ms)), <<"DoBecomeLeader", i>>)

(***************************************************************************)
(* Become follower                                                         *)
(***************************************************************************)

SetCurrentTerm(i, term) ==  
    /\ UpdateCurrentTerm(i, term)
    /\ UpdateVotedFor(i, Nil)

_BecomeFollower(i) ==  
    /\ UpdateState(i, Follower)
    /\ UpdateLeaderId(i, Nil)
    /\ reset(i)   

\* func : become_follower@raft.rs
BecomeFollower(i, term) ==
    /\ SetCurrentTerm(i, term)
    /\ _BecomeFollower(i)
    /\ UNCHANGED pending_snapshot

BecomeFollowerInLost(i, term) ==
    /\ UNCHANGED <<votedFor, pending_snapshot>>
    /\ UpdateCurrentTerm(i, term)
    /\ _BecomeFollower(i)


BecomeFollowerWithLeader(i, term, leaderId) ==
    /\ SetCurrentTerm(i, term)
    /\ UpdateState(i, Follower)
    /\ UpdateLeaderId(i, leaderId)
    /\ UNCHANGED pending_snapshot
    /\ reset(i)

BecomeFollowerWithLeaderWithouPending(i, term, leaderId) ==
    /\ SetCurrentTerm(i, term)
    /\ UpdateState(i, Follower)
    /\ UpdateLeaderId(i, leaderId)
    /\ reset(i)

(***************************************************************************)
(* Recv requestvote                                                        *)
(***************************************************************************)

\* func: maybe_commit_by_vote@raft.rs
maybe_commit_by_vote(n, commitIdx, commitTerm) ==
    IF  \/ commitIdx = 0 
        \/ commitTerm = 0
        \/ raftState'[n] = Leader
    THEN  UNCHANGED commitIndex
    ELSE IF \/ commitIdx <= commitIndex[n]
         THEN UNCHANGED commitIndex
         ELSE IF /\ commitIdx > commitIndex[n]
                 /\ commitTerm = LogGetTerm2(log[n], commitIdx, "maybe_commit_by_vote", n)
              THEN UpdateCommitIdx(n, commitIdx)
              ELSE UNCHANGED commitIndex

HandleMsgRV(m) == 
    LET data == m.data
        dst == m.dst
        src == m.src
        demote == currentTerm[dst] < data.term
        stale == currentTerm[dst] > data.term
        msg == RequestVoteResponse(m, IF demote THEN Nil ELSE votedFor[dst], IF demote THEN Nil ELSE leader_id[dst])      \* Pass in intermediate values based on demote status.
    IN IF stale \* stale message drop
       THEN /\ UNCHANGED noNetVars 
            /\ NetUpdate2(NetDelMsg(m), 
                    <<"RecvRequestVote", "stale message ignore",  dst, src, m.seq>>)
       ELSE /\ UNCHANGED <<check_quorum, snapVars, pending_snapshot>> 
            /\ IF demote  \* Received a newerletter and became a follower.
               THEN /\ UpdateCurrentTerm(dst, data.term)
                    /\ UpdateState(dst, Follower)
                    /\ UpdateLeaderId(dst, Nil)
                    /\ reset(dst)
               ELSE UNCHANGED <<currentTerm, raftState, leader_id, leaderVars, candidateVars, progress, inflight, pr_pending>>
            /\ IF ~msg.data.reject  \* Determine whether to vote based on RequestVote letter
               THEN /\ UpdateVotedFor(dst, src)
                    /\ UNCHANGED <<commitIndex>>
               ELSE /\ IF demote \* If there is a no vote the default is not to change the vote value, but due to the demote state, the node will reset and thus the vote will become nil
                       THEN UpdateVotedFor(dst, Nil)
                       ELSE UNCHANGED <<votedFor>> 
                    /\ maybe_commit_by_vote(dst, data.commit, data.commitTerm) \* func: maybe_commit_by_vote @ raft.rs
            /\ UNCHANGED <<log>>
            /\ NetUpdate2(NetReplyMsg(msg, m), 
                    <<"RecvRequestVote", msg.status, dst, src, m, IF ~msg.data.reject THEN "vote" ELSE "not-vote">>)


(***************************************************************************)
(* Recv requestvote response                                               *)
(***************************************************************************)

\* func : poll@raft.rs
Poll(grant, reject) ==
    LET grantNum == Cardinality(grant) + 1 \* +1 is voted for myself
        rejectNum == Cardinality(reject)
    IN IF IsQuorumNum(grantNum)
       THEN "Won"
       ELSE IF IsQuorumNum(rejectNum)
            THEN "Lost"
            ELSE "Pending"




HandleMsgRVR( m) ==
    LET resp == m.data
        src == m.src
        dst == m.dst
        demote == resp.term > currentTerm[dst] 
        isCandidate == raftState[dst] = Candidate
        stale == resp.term < currentTerm[dst] 
    IN /\ IF demote \* Received a newerletter and became a follower.
          THEN /\ UNCHANGED <<logVars, check_quorum, snapVars>>
               /\ BecomeFollower(dst, resp.term)
               /\ NetUpdate2(NetDelMsg(m), <<"RecvRequestVoteResponse", "term is smaller", dst, src, m>>)
          ELSE IF  stale \* stale message drop
               THEN /\ UNCHANGED noNetVars
                    /\ NetUpdate2(NetDelMsg(m), <<"RecvRequestVoteResponse", "vote is stale", dst, src, m>>)
               ELSE IF ~isCandidate \* only candidate process M_RVR
                    THEN /\ UNCHANGED noNetVars
                         /\ NetUpdate2(NetDelMsg(m), <<"RecvRequestVoteResponse", "not candidate", dst, src, m>>)
                    ELSE    /\ UNCHANGED <<check_quorum, snapVars, pending_snapshot>>
                            /\ LET newVotedForMe == IF ~resp.reject 
                                                    THEN voted_for_me[dst] \cup {src} 
                                                    ELSE voted_for_me[dst]  
                                newVotedReject == IF ~resp.reject 
                                                    THEN voted_reject[dst]  
                                                    ELSE voted_reject[dst]\cup {src}
                                res == Poll(newVotedForMe, newVotedReject)
                                IN  IF res = "Won"
                                    THEN /\ UNCHANGED << commitIndex>>  \* The reason for this is that in becomeLeader we need to broadcast the AE letter globally, and the AE letter carries the latest commitIndex,  but we don't update the commitIndex until below in maybe_commit_by_vote,  and it has to use the latest commitIndex, so we need to write it here. 
                                        /\ UNCHANGED << votedFor, currentTerm>>
                                        /\ BecomeLeader(dst, m)                             
                                    ELSE /\ UNCHANGED <<log, inflight, pr_pending>>  
                                         /\ IF res = "Lost"
                                            THEN /\ BecomeFollowerInLost(dst, currentTerm[dst])
                                                 /\ NetUpdate2(NetDelMsg(m), <<"RecvRequestVoteResponse", "Lost", dst, src, m>>)
                                            ELSE /\ NetUpdate2(NetDelMsg(m), <<"RecvRequestVoteResponse", "Pending", dst, src, m>>)
                                                 /\ UpdateVotedForMe(dst, newVotedForMe)
                                                 /\ UpdateVotesReject(dst, newVotedReject)
                                                 /\ UNCHANGED << serverVars, leader_id, progress, leaderVars>>  
                            /\ maybe_commit_by_vote(dst, resp.commit, resp.commitTerm) 

(***************************************************************************)
(* Send appendentries to all other nodes                                   *)
(***************************************************************************)
SendAppendentriesAll(n) ==  \* func: bcast_append
    /\ UNCHANGED <<logVars, serverVars, matchIndex, candidateVars, nodeVars, snapVars>>
    /\ LET ms == BatchReqMsgsArg(n, AppendEntriesNext, nextIndex)
       IN /\ BatchUpdateNextWithMsg(n, ms) 
          /\ NetUpdate2(NetmanIncField("n_ae", NetBatchAddMsg(ms)), <<"SendAppendentriesAll", n>>)

(***************************************************************************)
(* Send heartbeat(empty log appendentries) to all other nodes              *)
(***************************************************************************)
SendHeartBeatAll(n) ==  \* func: bcast_heart
    /\ UNCHANGED <<logVars, serverVars, leaderVars, candidateVars, nodeVars, snapVars>>
    /\ LET ms == BatchReqMsgsArg(n, HeartBeatNext, nextIndex)
       IN  NetUpdate2(NetmanIncField("n_hb", NetBatchAddMsg(ms)), <<"SendHeartBeatAll", n>>)

(***************************************************************************)
(* Recv appendentries                                                      *)
(***************************************************************************)
AcceptLeader(me, leader) == 
    /\ UpdateState(me, Follower)
    /\ UpdateLeaderId(me, leader)
    /\  IF raftState[me] = Follower
        THEN UNCHANGED <<candidateVars, leaderVars, progress, inflight, pr_pending>>
        ELSE reset(me)

\* func: find_conflict_by_term
find_conflict_by_term(me, index, term) ==
    LET hint_index == Min(index, LastIdx(log[me], me))
        F[i \in 0..hint_index ] == 
            IF hint_index = 0 
            THEN <<0, 0>>
            ELSE IF i = 0
                 THEN << >>
                 ELSE IF term >= LogGetTerm2(log[me] ,i, "find_conflict_by_term", me) 
                      THEN <<i, LogGetTerm2(log[me] ,i, "find_conflict_by_term", me) >>
                      ELSE F[i-1]
    IN F[hint_index]

\* func: raft_log.maybe_commit()
SetCommitIdx(n, idx) ==   
    \* /\ Assert(idx <= LastIdx(log'[n], n), <<"SetCommitIdx: idx <= LogCurrentIdx(log'[n])", n, idx, log', LastIdx(log'[n], n)>>)
    /\ IF idx > commitIndex[n]
       THEN UpdateCommitIdx(n, idx)
       ELSE UNCHANGED <<commitIndex>> 

 \* new_message(send_request_snapshot)@raft.rs  
SendRequestSnapshot(n) == 
    LET body == [ reject |-> TRUE,
                  reject_hint |-> LastIdx(log[n], n),
                  term |-> currentTerm[n],
                  index |-> commitIndex'[n],
                  request_snapshot |-> pending_snapshot'[n],
                  log_term |-> LogLastTerm(log[n], n)]
        to == leader_id[n]          
    IN ConstructMsg(n, to, M_AER, body)

HandleMsgAE(m) ==  \* func: handle_append
    LET data == m.data
        src == m.src
        dst == m.dst
        demote == data.term > currentTerm[dst]
        stale == data.term < currentTerm[dst]
        snap_req == pending_snapshot[dst] /= 0
        log_stale == data.index < commitIndex[dst]
        ask_snap_msg == SendRequestSnapshot(dst)
        log_stale_msg == AERFailLogStale(m)
        success == AppendEntriesResponseSuccess(m)
    IN IF stale \* drop stale message
       THEN /\ UNCHANGED noNetVars
            /\ NetUpdate2(NetDelMsg(m), <<"RecvAppendentries", "stale message ignore", dst, src, m>>)
       ELSE /\ UNCHANGED <<check_quorum, inflight, snapVars, pending_snapshot, pr_pending>> 
            /\ IF demote \* Received a newer letter and became a follower, but there are related variables that need to be updated later, so only their term values are updated here.
               THEN SetCurrentTerm(dst, data.term)
               ELSE UNCHANGED <<currentTerm, votedFor>>
            /\ AcceptLeader(dst, data.leader_id) \* Update the leader_id and make sure the node state is follower
            /\ IF snap_req
               THEN /\ UNCHANGED <<logVars>>
                    /\ NetUpdate2(NetReplyMsg(ask_snap_msg, m), <<"RecvAppendentries", "snap_shot ask", dst, src, m>>)
               ELSE /\  IF log_stale \* if m.index < self.raft_log.committed @ raft.rs
                        THEN /\ UNCHANGED <<logVars>>
                             /\ NetUpdate2(NetReplyMsg(log_stale_msg, m), <<"RecvAppendentries", "log stale commit", dst, src, m>>)
                        ELSE LET ety == LogGetEntry2(log[dst], data.index, dst)
                                 noPrevLog == ety = Nil
                                 termMatch == \/ /\ noPrevLog
                                                 /\ data.log_term = 0 
                                              \/ /\ ~noPrevLog
                                                 /\ ety.term = data.log_term
                             IN  IF termMatch \* maybe_append@raft_log.rs
                                 THEN    /\ log' = Update(log, dst, LogGetMatchEntries(log[dst], data.entries, data.index, dst))
                                         /\  IF commitIndex[dst] < data.commit
                                             THEN LET lastLogIdx == Max(LastIdx(log'[dst], dst), 1)
                                                      idxToCommit == Min(lastLogIdx, data.commit)
                                                  IN SetCommitIdx(dst, idxToCommit)
                                             ELSE UNCHANGED commitIndex
                                         /\ NetUpdate2(NetReplyMsg(success, m), <<"RecvAppendentries", "success", dst, src, m>>)
                                 ELSE LET conflict == find_conflict_by_term(dst, data.index, data.log_term) \* find_conflict_by_term @ raft_log.rs
                                            fail == AERFailTermMismatch(m, conflict[1], conflict[2])
                                      IN  /\ UNCHANGED <<logVars>>
                                          /\ NetUpdate2(NetReplyMsg(fail, m), <<"RecvAppendentries", "term Mismatch", dst, src, m>>)
            


(***************************************************************************)
(* Recv appendentries response                                             *)
(***************************************************************************)   
\* The reason for this is that we have multiple designs for calculating whether or not a paused operation has occurred, 
\* and handle_aer needs to calculate both old and new paused for the unification step.
IsPaused(me, node, _inflight, _progress) ==
    \/ /\ _progress[me][node][1] = Probe
       /\ _progress[me][node][2] = TRUE \* Here, true means pause.
    \/ _progress[me][node][1] = Snapshot
    \/ /\ _progress[me][node][1] = Replicate
       /\ _inflight[me][node] /= 0 \* We only send one packet at a time, so it must be FULL when there is data, i.e. it will PAUSE


FlushSendAppendentries(me, m, tempNextIdx, tempInflight, info) == 
    LET F[i \in 0..NumServer] ==
        IF i = 0 THEN <<{}, Servers>>
        ELSE LET n == CHOOSE n \in F[i-1][2]: TRUE
                 idx == LastIdx(log'[me], me)
             IN    IF n = me
                   THEN <<F[i-1][1] \cup {n}, F[i-1][2] \ {n}>>
                   ELSE LET pause == IsPaused(me, n, tempInflight, progress')
                        IN IF pause 
                           THEN <<F[i-1][1] \cup {n}, F[i-1][2] \ {n}>> \* 不会发送
                           ELSE <<F[i-1][1], F[i-1][2] \ {n}>> \* 未暂停 就会发送
        excludes == F[NumServer][1]
        excludes2 == F[NumServer][1] \ {me}
        ms == _BatchExcludesReqMsgsArg(me, excludes, _Dummy2, AppendEntriesNext, tempNextIdx)
        next_keep == [ s \in excludes2 |-> tempNextIdx[me][s] ]
        next_me == IF tempNextIdx[me][me] < LastIdx(log'[me], me) + 1  
                   THEN (me :> LastIdx(log'[me], me) + 1)
                   ELSE (me :>  tempNextIdx[me][me] )
        next_update == [ s \in Servers \ excludes |-> IF tempNextIdx[me][s] <= LastIdx(log'[me], me)
                                                      THEN tempNextIdx[me][s] + 1
                                                      ELSE tempNextIdx[me][s]  ] 
        inflight_keep == [ s \in excludes |-> tempInflight[me][s]]
        inflight_update == [ s \in Servers \ excludes |-> IF tempNextIdx[me][s] <= LastIdx(log'[me], me)
                                                      THEN tempNextIdx[me][s] 
                                                      ELSE 0] 
    IN /\ nextIndex' = [ nextIndex EXCEPT ![me] = next_keep @@ next_update @@ next_me]
       /\ inflight' = [inflight EXCEPT ![me] = inflight_keep @@ inflight_update]
       /\ IF m = Nil  \* RecvEntry: client request
          THEN NetUpdate2(NetmanIncField("n_op", NetBatchAddMsg(ms)), info)
          ELSE NetUpdate2(NetReplyBatchAddMsg(ms, m), info)

\* (maybe_update + maybe_commit) in handle_append_response@raft.rs
AdvanceCommitIdx(me, m, succ_rsp, tempNextIndex, tempInflight, old_pause) ==  
    LET F[i \in 0..NumServer] ==
            IF i = 0 THEN <<<<>>, Servers>>
            ELSE LET n == CHOOSE n \in F[i-1][2]: TRUE
                 IN <<Append(F[i-1][1], matchIndex'[me][n]), F[i-1][2] \ {n}>>
        sorted_match_idx == SortSeq(F[NumServer][1], LAMBDA x, y: x > y)
        commit == sorted_match_idx[NumServer \div 2 + 1]
        pause == IsPaused(me, m.src, tempInflight, progress')
        is_ae == succ_rsp.type = M_AE
        empty_entries == Len(succ_rsp.data.entries) = 0
    IN IF /\ commit > commitIndex[me]
          /\ currentTerm[me] = LogGetTerm2(log[me], commit, "AdvanceCommitIdx", me)
       THEN /\ SetCommitIdx(me, commit) \* commit change, maybe send_bcast
            /\ FlushSendAppendentries(me, m, tempNextIndex, tempInflight,  <<"RecvAppendentriesResponse", "commit change", m.dst, m.src, m>>)  \* bcast_append
       ELSE /\ UNCHANGED commitIndex 
            /\ IF old_pause \* If it's an "old pause", it sends empty_entries regardless.
               THEN IF pause 
                    THEN /\ NetUpdate2(NetDelMsg(m), <<"RecvAppendentriesResponse", "old_pause_pause", m.dst, m.src, m>>) 
                         /\ UNCHANGED inflight
                         /\ nextIndex' = tempNextIndex
                    ELSE /\ NetUpdate2(NetReplyMsg(succ_rsp, m), <<"RecvAppendentriesResponse", "old_pause_send", m.dst, m.src, m>>) 
                         /\ IF is_ae 
                            THEN /\ IF empty_entries
                                    THEN /\ UpdateInflight(me, m.src, 0) 
                                         /\ nextIndex' = tempNextIndex
                                    ELSE /\ UpdateInflight(me, m.src, succ_rsp.data.entries[1].index) 
                                         /\ UpdateNextIdx(me, m.src, succ_rsp.data.entries[1].index + 1)
                            ELSE /\ UNCHANGED inflight
                                 /\ nextIndex' = tempNextIndex              
               ELSE \* 否则 只在不空的时候发送 (aggressive)
                    IF pause \* If it's an "old pause", it sends empty_entries regardless.
                    THEN /\ NetUpdate2(NetDelMsg(m), <<"RecvAppendentriesResponse", "aggressive_pause", m.dst, m.src, m>>) 
                         /\ UNCHANGED inflight
                         /\ nextIndex' = tempNextIndex
                    ELSE IF is_ae /\ empty_entries 
                         THEN /\ NetUpdate2(NetDelMsg(m), <<"RecvAppendentriesResponse", "aggressive_empty", m.dst, m.src, m>>) 
                              /\ UNCHANGED inflight
                              /\ nextIndex' = tempNextIndex
                         ELSE /\ NetUpdate2(NetReplyMsg(succ_rsp, m), <<"RecvAppendentriesResponse", "aggressive_has", m.dst, m.src, m>>) 
                              /\ IF is_ae 
                                 THEN /\ UpdateInflight(me, m.src, succ_rsp.data.entries[1].index)  \* replicate 
                                      /\ UpdateNextIdx(me, m.src, succ_rsp.data.entries[1].index + 1)
                                 ELSE /\ UNCHANGED inflight 
                                      /\ nextIndex' = tempNextIndex  
    \*    ELSE /\ UNCHANGED commitIndex    
    \*         /\ IF ~pause
    \*            THEN IF old_pause
    \*                 THEN /\ NetUpdate2(NetReplyMsg(succ_rsp, m), <<"RecvAppendentriesResponse", "commit still send", m.dst, m.src, m>>) 
    \*                      /\ IF ~empty_entries
    \*                         THEN UpdateInflight(me, m.src, succ_rsp.data.entries[1].index) 
    \*                         ELSE UpdateInflight(me, m.src, 0) 
    \*                      /\ IF empty_entries  
    \*                         THEN nextIndex' = tempNextIndex
    \*                         ELSE UpdateNextIdx(me, m.src, succ_rsp.data.entries[1].index + 1)
    \*                 ELSE IF empty_entries
    \*                      THEN /\ NetUpdate2(NetDelMsg(m), <<"RecvAppendentriesResponse", "commit still pause", m.dst, m.src, m>>) 
    \*                           /\ UpdateInflight(me, m.src, 0) 
    \*                           /\ nextIndex' = tempNextIndex
    \*                      ELSE /\ NetUpdate2(NetReplyMsg(succ_rsp, m), <<"RecvAppendentriesResponse", "commit still send", m.dst, m.src, m>>) 
    \*                           /\ UpdateInflight(me, m.src, succ_rsp.data.entries[1].index) 
    \*                           /\ UpdateNextIdx(me, m.src, succ_rsp.data.entries[1].index + 1)
    \*            ELSE /\ NetUpdate2(NetDelMsg(m), <<"RecvAppendentriesResponse", "commit still pause", m.dst, m.src, m>>) 
    \*                 /\ UNCHANGED inflight
    \*                 /\ nextIndex' = tempNextIndex

\* maybe_decr_to @ progress.rs
maybe_decr_to(dst, src, m, next_probe_index) == 
    LET rejected == m.data.index
        match_hint == m.data.reject_hint
        pending == m.data.request_snapshot 
    IN  /\  IF progress[dst][src][1] = Replicate
            THEN IF \/ rejected < matchIndex[dst][src] 
                    \/ /\ rejected = matchIndex[dst][src] 
                       /\ pending = 0
                THEN /\ UNCHANGED << nextIndex, progress, pr_pending>>
                     /\ NetUpdate2(NetDelMsg(m), <<"RecvAppendentriesResponse", "decr_replicate stale", dst, src, m>>)
                ELSE /\ IF pending = 0 
                        THEN UNCHANGED pr_pending
                        ELSE UpdatePrPending(dst, src, pending)  
                     /\ UpdateNextIdx(dst, src, matchIndex[dst][src] + 1) \* 不涉及 snapshot 所以 become_probe中 直接进行 else分支  
                     /\ LET need_snap == \/ nextIndex'[dst][src] < FirstIdx(log'[dst], dst) 
                                         \/ pr_pending'[dst][src] /= 0 \* 根据 progress中的pending_request_snapshot进行对比
                            one_rsp == IF need_snap
                                       THEN SendSnapshot(dst, src)
                                       ELSE AppendEntriesNext(dst, src, nextIndex')
                        IN /\ NetUpdate2(NetReplyMsg(one_rsp, m), <<"RecvAppendentriesResponse", "decr_replicate send", dst, src, m>>) \* 一定会变为probe become_probe
                           /\ IF need_snap
                              THEN UpdateProgress(dst, src, <<Snapshot, one_rsp.data.metaIndex>>) \* pr.become_snapshot
                              ELSE IF Len(one_rsp.data.entries) = 0 \* simulate prepare_send_entries determines if the sent entries are empty to update the progress
                                   THEN UpdateProgress(dst, src, <<Probe, FALSE>>)
                                   ELSE UpdateProgress(dst, src, <<Probe, TRUE>>)              
            ELSE /\ IF /\ \/ nextIndex[dst][src] = 0 \* probe or snapshot
                          \/ nextIndex[dst][src] - 1 /= rejected
                       /\ pending = 0
                    THEN /\ UNCHANGED << nextIndex, progress, pr_pending>>
                         /\ NetUpdate2(NetDelMsg(m), <<"RecvAppendentriesResponse", "decr_probe stale", dst, src, m>>)
                    ELSE /\ IF pending /= 0 
                            THEN /\ IF pr_pending[dst][src] = 0
                                    THEN UpdatePrPending(dst, src, pending) 
                                    ELSE UNCHANGED pr_pending 
                                 /\ UNCHANGED nextIndex
                            ELSE /\ LET new_match == Min(rejected, next_probe_index + 1)
                                        new_next_idx == Max(new_match, 1)  
                                    IN  UpdateNextIdx(dst, src, new_next_idx)
                                 /\ UNCHANGED pr_pending
                         /\ LET  need_snap == \/ nextIndex'[dst][src] < FirstIdx(log'[dst], dst) 
                                              \/ pr_pending'[dst][src] /= 0
                                 one_rsp == IF need_snap
                                            THEN SendSnapshot(dst, src)
                                            ELSE AppendEntriesNext(dst, src, nextIndex')  
                                 pause == IsPaused(dst, src, inflight, progress) 
                            IN  /\ IF pause 
                                   THEN NetUpdate2(NetDelMsg(m), <<"RecvAppendentriesResponse", "decr_probe pause", dst, src, m>>)
                                   ELSE NetUpdate2(NetReplyMsg(one_rsp, m), <<"RecvAppendentriesResponse", "decr_probe send", dst, src, m>>)
                                /\ IF need_snap
                                   THEN UpdateProgress(dst, src, <<Snapshot, one_rsp.data.metaIndex>>) \* pr.become_snapshot
                                   ELSE IF Len(one_rsp.data.entries) = 0
                                        THEN UpdateProgress(dst, src, <<Probe, FALSE>>)
                                        ELSE UpdateProgress(dst, src, <<Probe, TRUE>>)
                        
\* func: handle_append
HandleMsgAER(m) ==  
    LET resp == m.data
        src == m.src
        dst == m.dst
        stale == resp.term < currentTerm[dst]
        demote == resp.term > currentTerm[dst]
        need_optimize == resp.reject /\ resp.log_term > 0
        next_probe_index == find_conflict_by_term(dst, resp.reject_hint, resp.log_term)[1]   
        failReason ==
            IF stale THEN "stale message ignore" ELSE
            IF resp.term > currentTerm[dst] THEN "term is smaller" ELSE
            IF raftState[dst] /= Leader THEN "not leader" ELSE
            IF need_optimize THEN "retry" ELSE "success"
    IN      IF failReason /= "success"
            THEN IF failReason = "stale message ignore" \* drop stale message
                 THEN /\ UNCHANGED <<noNetVars>>
                      /\ NetUpdate2(NetDelMsg(m), <<"RecvAppendentriesResponse", "stale message ignore", dst, src, m>>)
                 ELSE IF failReason = "term is smaller" \* Received a newer letter and became a follower
                      THEN /\ UNCHANGED <<check_quorum, logVars, snapVars>>
                           /\ BecomeFollower(dst, resp.term) 
                           /\ NetUpdate2(NetDelMsg(m), <<"RecvAppendentriesResponse", "term is smaller", dst, src, m>>)
                      ELSE IF failReason = "not leader" \* node not leader, drop the message
                           THEN /\ UNCHANGED <<noNetVars>>
                                /\ NetUpdate2(NetDelMsg(m), <<"RecvAppendentriesResponse", "not leader", dst, src, m>>)
                           ELSE IF failReason = "retry" \* m.reject
                                THEN /\ UNCHANGED <<serverVars, candidateVars, leader_id, check_quorum, logVars, matchIndex, inflight, snapVars, pending_snapshot>>
                                     /\ maybe_decr_to(dst, src, m, next_probe_index)          
                                ELSE Assert(FALSE, <<"handle aer Unseen error situation", failReason>>)
            ELSE \* success
                \* 因为不涉及其他状态变换，我感觉在这里处理了snapshot的progress变化比较合适
                /\ UNCHANGED <<leader_id, log, serverVars, candidateVars, check_quorum, snapVars, pending_snapshot>>
                /\ LET  pending == m.data.request_snapshot
                        prboeToReplicate == progress[dst][src][1] = Probe
                        snapToProbe == /\ progress[dst][src][1] = Snapshot \* Simulate is_snapshot_caught_up will update if successful, pending_snapshot is empty
                                       /\ matchIndex'[dst][src] >= progress[dst][src][2]
                        \* 这里之所以这么写 是因为 如果resp.index < match 必会返回，不会发送包，基本上nextIndex 会改变，而之后更新progress状态，所以这里我们可以直接用这个来更新
                        \* match 在maybe_update 中 一定会变为resp.index
                        nnextBymaybeUpdate == Max(resp.index + 1, nextIndex[dst][src])
                        nextToUpdate == IF snapToProbe
                                        THEN Max(nnextBymaybeUpdate, pr_pending[dst][src] + 1)
                                        ELSE nnextBymaybeUpdate
                        old_pause == IsPaused(dst, src, inflight, progress)              
                        \* The simulation here is that a call to maybe_update in handle_append_response may update next_idx, but since it will be changed again in prepare_entries, a temporary variable is needed to retrieve the corresponding entries.
                        tempNextIndex == [nextIndex EXCEPT ![dst][src] = nextToUpdate]
                        \* The temp nextIndex is also needed here.
                        need_snap == \/ nextIndex[dst][src] < FirstIdx(log'[dst], dst) 
                                     \/ /\ ~snapToProbe \* 这里如果snapToProbe 为 true，那么一定不需要snapshot
                                        /\ pr_pending[dst][src] /= 0
                        temp_entries == LogGetEntryOne2(log'[dst], tempNextIndex[dst][src], dst)
                        one_rsp == IF need_snap
                                   THEN SendSnapshot(dst, src)
                                   ELSE AppendEntriesNext(dst, src, tempNextIndex)
                        repCanSend == inflight[dst][src] <= resp.index  \* The number of the arriving packet is stored in inflight, and in raft.rs, the replicate state will be free_to, so we'll simulate it directly here.
                        tempInflight == IF snapToProbe \* 这里我们利用tempinflight 来做是否pause的判断，因为所有会在中间状态进行改变
                                        THEN [inflight EXCEPT ![dst][src] = 0]
                                        ELSE IF prboeToReplicate
                                             THEN [inflight EXCEPT ![dst][src] = 0]
                                             ELSE IF repCanSend 
                                                  THEN [inflight EXCEPT ![dst][src] = 0]
                                                  ELSE inflight                 
                   IN IF resp.index > matchIndex[dst][src] \* maybe_update return true
                      THEN  /\ UpdateMatchIdx(dst, src, resp.index)
                            /\ UNCHANGED <<pr_pending>>
                            \* Here we need to update the progress and nextIndex status according to the content of the letter, corresponding to the handle_append_response of the maybe_update to maybe_commit processing logic
                            /\ IF snapToProbe
                               THEN /\ IF Len(temp_entries) = 0 \* 为了解决循环依赖，因为这里原版使用了 one_rsp.entries的内容， 不过需要commitIndex' 但是advance中才会更新 commitIndex
                                       THEN UpdateProgress(dst, src, <<Probe, FALSE>>)
                                       ELSE UpdateProgress(dst, src, <<Probe, TRUE>>)
                               ELSE /\ IF  prboeToReplicate
                                       THEN UpdateProgress(dst, src, <<Replicate, FALSE>>)
                                       ELSE UNCHANGED progress
                            /\ AdvanceCommitIdx(dst, m, one_rsp, tempNextIndex, tempInflight, old_pause)
                      ELSE /\ UNCHANGED << matchIndex, commitIndex, inflight, nextIndex, pending_snapshot, progress, pr_pending>> \* Direct RETURN doesn't do anything
                           /\ NetUpdate2(NetDelMsg(m), <<"RecvAppendentriesResponse", "maybe_update_fail", dst, src, m>>) 

(***************************************************************************)
(* Recv heartBeat                                                          *)
(***************************************************************************)

\* func: handle_heartbeat
HandleMsgHB(m) ==  
    LET data == m.data
        src == m.src
        dst == m.dst
        demote == currentTerm[dst] < data.term
        stale == data.term < currentTerm[dst]
        ask_snapReq == pending_snapshot[dst] /= 0 
        rsp == IF ask_snapReq
               THEN SendRequestSnapshot(dst)
               ELSE HeartBeatResponse(m)
    IN IF stale
       THEN /\ UNCHANGED noNetVars
            /\ NetUpdate2(NetDelMsg(m), <<"RecvHeartBeat", "stale message ignore", dst, src, m>>)
       ELSE /\ UNCHANGED <<log, snapVars>>
            /\ IF \/ demote
                  \/ raftState[dst] = Candidate
               THEN /\ BecomeFollowerWithLeader(dst, data.term, src) 
                    /\ UNCHANGED <<check_quorum>>
               ELSE UNCHANGED <<serverVars, nodeVars, candidateVars, leaderVars>> 
            /\ SetCommitIdx(dst, data.commit)
            /\ NetUpdate2(NetReplyMsg(rsp, m), <<"RecvHeartBeat", "success", dst, src, m>>)
           
(***************************************************************************)
(* Recv HeartBeatResponse                                                  *)
(***************************************************************************)
\* func: handle_heartbeat_response
HandleMsgHBR(m) ==  
    LET resp == m.data
        src == m.src
        dst == m.dst
        demote == resp.term > currentTerm[dst]
        stale == resp.term < currentTerm[dst]
    IN IF stale
       THEN /\ UNCHANGED noNetVars
            /\ NetUpdate2(NetDelMsg(m), <<"RecvHeartBeatResponse", "stale message ignore", dst, src, m>>)
       ELSE IF demote
            THEN /\ UNCHANGED << logVars, check_quorum, snapVars, pending_snapshot>>
                 /\ BecomeFollower(dst, resp.term)
                 /\ NetUpdate2(NetDelMsg(m), <<"RecvHeartBeatResponse", "term is smaller", dst, src, m>>) 
            ELSE /\ UNCHANGED <<serverVars, candidateVars, leader_id, check_quorum,  matchIndex, logVars, progress, snapVars, pending_snapshot, pr_pending>> 
                 /\  IF  matchIndex[dst][src] < LastIdx(log[dst], dst) 
                     THEN LET need_snap == \/ nextIndex[dst][src] < FirstIdx(log'[dst], dst) 
                                           \/ pr_pending'[dst][src] /= 0 
                              req_msg == IF need_snap
                                         THEN SendSnapshot(dst, src)
                                         ELSE AppendEntriesNext(dst, src, nextIndex)
                              send_entry == IF need_snap 
                                            THEN <<>>
                                            ELSE req_msg.data.entries
                              isReplicate == progress[dst][src][1] = Replicate
                              inflightToUpdate == IF send_entry /= <<>> 
                                                  THEN send_entry[1].index
                                                  ELSE 0 
                              nextIndexToUpdate == IF isReplicate
                                                   THEN IF send_entry /= <<>>
                                                        THEN nextIndex[dst][src] + 1
                                                        ELSE nextIndex[dst][src]
                                                   ELSE nextIndex[dst][src]
                          IN  /\ NetUpdate2(NetReplyMsg(req_msg, m), <<"RecvHeartBeatResponse",  "send append", dst, src, m>>) 
                              /\ UpdateInflight(dst, src ,inflightToUpdate)
                              /\ UpdateNextIdx(dst, src, nextIndexToUpdate)
                     ELSE /\ NetUpdate2(NetDelMsg(m), <<"RecvHeartBeatResponse", "not send", dst, src, m>>) 
                          /\ UpdateInflight(dst, src ,0)
                          /\ UNCHANGED nextIndex


\* in step_leader: msg_propose
RecvEntry(n, data) ==  
    /\ raftState[n] = Leader
    /\ UNCHANGED <<serverVars, candidateVars, leader_id, check_quorum, progress, commitIndex, snapVars, pending_snapshot, pr_pending>>
    /\ LET ety == [ term |-> currentTerm[n], data |-> data, index |->  LastIdx(log[n], n) + 1]
       IN log' = Update(log, n, LogAppend(log[n], ety))
    /\ IF matchIndex[n][n] < LastIdx(log'[n], n)  
       THEN UpdateMatchIdx(n, n, LastIdx(log'[n], n))
       ELSE UNCHANGED matchIndex    
    /\ FlushSendAppendentries(n, Nil, nextIndex, inflight, <<"RecvEntry", n, data>>)


(***************************************************************************
  restart node
 ***************************************************************************)

\* Server i restarts. Only currentTerm/votedFor/log restored (i.e. unchanged).
\* NOTE: snapshot variables are considered as parts of log
\* NOTE: last applied index should be cleared here if modelled.
Restart(i) ==
    /\ UNCHANGED <<currentTerm, votedFor, logVars, check_quorum, snapVars>>
    /\ raftState'       = [raftState           EXCEPT ![i] = Follower ]
    /\ leader_id'       = [ leader_id    EXCEPT ![i] = Nil]
    /\ voted_for_me'    = [ voted_for_me EXCEPT ![i] = {} ]
    /\ voted_reject'    = [ voted_reject EXCEPT ![i] = {} ]
    /\ nextIndex'         = [ nextIndex         EXCEPT ![i] = [j \in Servers |-> 1 ]]
    /\ matchIndex'        = [ matchIndex        EXCEPT ![i] = [j \in Servers |-> 0 ]]
    /\ progress'        = [ progress         EXCEPT ![i] = [j \in Servers |-> <<Probe, FALSE>>]]
    /\ inflight'        = [ inflight        EXCEPT ![i] = [j \in Servers |-> 0 ]]


(***************************************************************************
 handle_snapshot
 ***************************************************************************)

\* Log load from snapshot. Update logInfo and log
LogLoadFromSnapshot(s, lastIdx) ==
    /\ log'     = [ log     EXCEPT ![s] = <<[term |-> 1, data |-> Nil, index |-> 1]>> ] \* apply_snapshot entries.clear() 但是保留最后一个snapshot的数据
    /\ SetCommitIdx(s, lastIdx)

HandleMsgSnap(m) ==
    LET data == m.data
        src == m.src
        dst == m.dst
        demote == currentTerm[dst] < data.term
        isCandidate == raftState[dst] = Candidate
        stale == data.term < currentTerm[dst]
        fast_forward == 
            /\ LogGetTerm2(log[dst], data.metaIndex, "HandleSnap", dst) = data.metaTerm 
            /\ pending_snapshot[dst] = 0
        commit_already == data.metaIndex < commitIndex[dst]
    IN IF stale
       THEN /\ UNCHANGED noNetVars
            /\ NetUpdate2(NetDelMsg(m), <<"RecvSnapShot", "stale message ignore", dst, src, m>>)
       ELSE /\  IF demote \/ isCandidate
                THEN /\ BecomeFollowerWithLeaderWithouPending(dst, data.term, src)
                     /\ UNCHANGED <<check_quorum>>
                ELSE UNCHANGED <<serverVars, leader_id, check_quorum, progress, inflight, pr_pending, candidateVars, leaderVars>>
            /\ IF commit_already \/ fast_forward  \* snapshot restore false 
               THEN /\ UNCHANGED <<log, snapVars>>
                    /\  IF commit_already
                        THEN UNCHANGED commitIndex
                        ELSE SetCommitIdx(dst, data.metaIndex)
                    /\ LET fail_msg == SnapFail(m)
                       IN NetUpdate2(NetReplyMsg(fail_msg, m), <<"RecvSnapShot", "restore fail-commit_already", dst, src, m>>)
               ELSE /\ UpdatePendingSnap(dst, 0)
                    /\ UpdateSnapIdx(dst, data.metaIndex)  \* snapshot restore true
                    /\ UpdateSnapTerm(dst, data.metaTerm)
                    /\ LogLoadFromSnapshot(dst, data.metaIndex)               
                    /\ LET success_msg == SnapSuccess(m)
                       IN NetUpdate2(NetReplyMsg(success_msg, m), <<"RecvSnapShot", "restore success", dst, src, m>>)
                     

(***************************************************************************
  Log compact
 ***************************************************************************)

CompactLog(n) == 
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, nodeVars, commitIndex, snapVars>>
    /\ LET index == commitIndex[n]
       IN log' = Update(log, n, LogGetEntriesFrom2(log[n], index, n))

(***************************************************************************
  Snapshot request
 ***************************************************************************)

SnapRequest(n) == 
    /\ raftState[n] /= Leader
    /\ leader_id[n] /= Nil
    /\ pending_snapshot[n] = 0
    /\ UNCHANGED <<serverVars, leaderVars, candidateVars, logVars,  leader_id, check_quorum, progress, inflight, pr_pending,snapVars>>
    /\ LogLastTerm(log[n], n) = currentTerm[n]
    /\ UpdatePendingSnap(n , LastIdx(log[n], n))
    /\ LET msg == SendRequestSnapshot(n)
       IN NetUpdate2(NetmanIncField("n_rqSnap", NetAddMsg(msg)), <<"DoSnapRequest", n, msg.src, msg.dst, msg>>)
    
    
    

(***************************************************************************
  State constraints
 ***************************************************************************)
 \* Here are some state limits to prevent state explosion due to control tla+
GetRealLogLen(curLog) == SelectSeq(curLog, LAMBDA i: i.data /= NoOp)
GetMaxLogLen == Len(log[CHOOSE i \in Servers: \A j \in Servers \ {i}:
                            GetRealLogLen(log[i]) >= GetRealLogLen(log[j])])
GetMaxTerm == currentTerm[CHOOSE i \in Servers: \A j \in Servers \ {i}:
                            currentTerm[i] >= currentTerm[j]]

ScSent == CheckParameterMax(netman.n_sent, "MaxSentMsgs")
ScRecv == CheckParameterMax(netman.n_recv, "MaxRecvMsgs")
ScWire == CheckParameterMax(netman.n_wire, "MaxWireMsgs")
\* ScLog  == CheckParameterMax(GetMaxLogLen,  "MaxLogLength")
\* ScTerm == CheckParameterMax(GetMaxTerm,    "MaxTerm")
ScPart == CheckParameterMax(netman.n_part, "MaxPartitionTimes")
ScCure == CheckParameterMax(netman.n_cure, "MaxCureTimes")
ScOp   == CheckParameterMax(netman.n_op,   "MaxClientOperationsTimes")
ScAe   == CheckParameterMax(netman.n_ae,   "MaxAppendEntriesTimes")
ScElec == CheckParameterMax(netman.n_elec, "MaxElectionTimes")
ScDrop == CheckParameterMax(netman.n_drop, "MaxDropTimes")
ScDup  == CheckParameterMax(netman.n_dup,  "MaxDupTimes")
ScRestart == CheckParameterMax(netman.n_restart,  "MaxRestart")
ScUnorder == CheckParameterMax(netman.n_unorder, "MaxUnorderTimes")

SC == /\ ScSent /\ ScRecv /\ ScWire /\ ScRestart
      /\ ScPart /\ ScCure /\ ScOp /\ ScAe /\ ScElec


(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
ElectionSafety ==
    LET TwoLeader ==
            \E i, j \in Servers:
                /\ i /= j
                /\ currentTerm'[i] = currentTerm'[j]
                /\ raftState'[i] = Leader
                /\ raftState'[j] = Leader
    IN ~TwoLeader

LeaderAppendOnly ==
    \* compact 不检查
    IF netcmd'[1][1] = "DoCompact" THEN TRUE
    ELSE \A i \in Servers:
            IF raftState[i] = Leader /\ raftState'[i] = Leader
            THEN LET curLog == log[i]
                    nextLog == log'[i]
                IN IF Len(nextLog) >= Len(curLog)
                    THEN SubSeq(nextLog, 1, Len(curLog)) = curLog
                    ELSE FALSE
            ELSE TRUE

\* Every (index, term) pair determines a log prefix.
\* From page 8 of the Raft paper: "If two logs contain an entry with the same index and term, then the logs are identical in all preceding entries."
\* LogMatching ==
\*     \A i, j \in Servers : i /= j =>
\*         \A n \in 1..min(Len(log[i]), Len(log[j])) :
\*             log[i][n].term = log[j][n].term =>
\*             SubSeq(log[i],1,n) = SubSeq(log[j],1,n)

LogMatching ==
  ~UNCHANGED log =>  \* check the safety only if log has unchanged to avoid unnecessary evaluation cost
    \A i, j \in Servers:
        IF i /= j
        THEN LET iLog == log'[i]
                 jLog == log'[j]
                 len == Min(Len(iLog), Len(jLog))
                 F[k \in 0..len] ==
                    IF k = 0 THEN <<>>
                    ELSE LET key1 == <<iLog[k].term, k>>
                             value1 == iLog[k].data
                             key2 == <<jLog[k].term, k>>
                             value2 == jLog[k].data
                             F1 == IF key1 \in DOMAIN F[k-1]
                                   THEN IF F[k-1][key1] = value1
                                        THEN F[k-1]
                                        ELSE F[k-1] @@ ( <<-1, -1>> :> <<key1, value1, F[k-1][key1]>> )
                                   ELSE F[k-1] @@ (key1 :> value1)
                             F2 == IF key2 \in DOMAIN F1
                                   THEN IF F1[key2] = value2
                                        THEN F1
                                        ELSE F1 @@ ( <<-1, -1>> :> <<key2, value2, F1[key2]>> )
                                   ELSE F1 @@ (key2 :> value2)
                         IN F2
             IN IF << -1, -1>> \notin DOMAIN F[len] THEN TRUE
                ELSE FALSE
        ELSE TRUE

MonotonicCurrentTerm == \A i \in Servers: currentTerm' [i] >= currentTerm[i]

MonotonicCommitIdx == \A i \in Servers: commitIndex'[i] >= commitIndex[i]

MonotonicMatchIdx ==
    \A i \in Servers:
        IF raftState[i] = Leader /\ raftState'[i] = Leader  \* change
        THEN \A j \in Servers:  matchIndex'[i][j] >= matchIndex[i][j]
        ELSE TRUE


\* CommittedLogDurable ==
\*     \A i \in Servers:
\*         LET len     == Min(commitIndex'[i], commitIndex[i])
\*             logNext == SubSeq(log'[i], 1, len)
\*             logCur  == SubSeq(log[i], 1, len)
\*         IN IF len = 1 THEN TRUE
\*            ELSE /\ Len(logNext) >= len
\*                 /\ Len(logCur) >= len
\*                 /\ logNext = logCur


\* Inv 3: Committed log should be durable (i.e. cannot be rolled back)
\* CommittedLogDurable ==
\*     \A i \in Servers:
\*         LET lenNext == commitIndex'[i] - snapshotLastIdx'[i]
\*             lenCur  == commitIndex[i] - snapshotLastIdx[i]
\*             len     == Min(lenNext, lenCur)
\*             idx     == Min(commitIndex'[i], commitIndex[i])
\*             logNext == LogGetEntriesTo2(log'[i], idx, i)
\*             logCur  == LogGetEntriesTo2(log[i], idx, i)
\*         IN IF len = 0 \/ Len(logNext) = 0 \/ Len(logCur) = 0 THEN TRUE
\*            ELSE /\ Len(logNext) >= len
\*                 /\ Len(logCur) >= len
                
\*                 /\ SubSeq(logNext, Len(logNext) + 1 - len, Len(logNext)) =
\*                    SubSeq(logCur, Len(logCur) + 1 - len, Len(logCur))

CommittedLogDurable ==
    \A i \in Servers:
        LET len     == Min(commitIndex'[i] - snapshotLastIdx'[i], commitIndex[i] - snapshotLastIdx[i])
            logNext == LogGetEntriesTo2(log'[i], len, i)
            logCur  == LogGetEntriesTo2(log[i], len, i)
        IN IF len = 1 \/ Len(logNext) = 0 \/ Len(logCur) = 0 THEN TRUE
           ELSE /\ Len(logNext) >= len
                /\ Len(logCur) >= len
                /\ logNext = logCur

CommittedLogReplicatedMajority ==
     \A i \in Servers:
        IF raftState'[i] /= Leader \/ commitIndex'[i] <= 1
        THEN TRUE
        ELSE LET entries == LogGetEntriesTo2(log'[i], commitIndex'[i], i)
                 len     == Len(entries)
                 nServer == Cardinality(Servers)
                 F[j \in 0..nServer] ==
                    IF j = 0
                    THEN <<{}, {}>>
                    ELSE LET k == CHOOSE k \in Servers: k \notin F[j-1][1]
                             logLenOk == LastIdx(log'[k], k) >= commitIndex'[i]
                             kEntries == LogGetEntriesTo2(log'[k], commitIndex'[i], k)
                             minLen == Min(len, Len(kEntries))
                         IN IF /\ logLenOk
                               /\ \/ minLen = 0
                                  \/ SubSeq(entries, Len(entries) + 1 - minLen,
                                            Len(entries)) = 
                                     SubSeq(kEntries, Len(kEntries)+1 - minLen,
                                            Len(kEntries))
                             THEN <<F[j-1][1] \union {k}, F[j-1][2] \union {k}>>
                             ELSE <<F[j-1][1] \union {k}, F[j-1][2]>>
             IN IsQuorum(F[nServer][2])

NextIdxGtMatchIdx ==
    \A i \in Servers:
        IF raftState'[i] = Leader
        THEN \A j \in Servers \ {i}: nextIndex'[i][j] > matchIndex'[i][j]
        ELSE TRUE

NextIdxGtZero ==
    \A i \in Servers:
        IF raftState'[i] = Leader
        THEN \A j \in Servers: nextIndex'[i][j] > 0
        ELSE TRUE

SelectSeqWithIdx(s, Test(_,_)) == 
    LET F[i \in 0..Len(s)] == 
        IF i = 0
        THEN <<>>
        ELSE IF Test(s[i], i)
             THEN Append(F[i-1], s[i])
             ELSE F[i-1]
    IN F[Len(s)]

FollowerLogLELeaderLogAfterAE ==
    LET cmd  == netcmd'[1]
        cmd1 == cmd[1]
        cmd2 == cmd[2]
        follower == cmd[3]
        leader   == cmd[4]
    IN IF cmd1 = "RecvAppendentries" /\ cmd2 \in { "success", "term Mismatch" }
       THEN IF log[follower] /= log'[follower]
            THEN LastIdx(log'[follower], follower) <= LastIdx(log'[leader], leader)
            ELSE TRUE
       ELSE TRUE

CommitIdxLELogLen ==
    IF netcmd'[1][1] = "RecvSnapShot" THEN TRUE
    ELSE \A i \in Servers: commitIndex'[i] <= LastIdx(log'[i], i)

LeaderCommitCurrentTermLogs ==
    \A i \in Servers:
        IF raftState'[i] = Leader
        THEN IF commitIndex[i] /= commitIndex'[i]
             THEN LogGetTerm2(log'[i], commitIndex'[i], "LeaderCommitCurrentTermLogs", i) = currentTerm'[i]
             ELSE TRUE
        ELSE TRUE

NewLeaderTermNotInLog ==
    \A i \in Servers:
        IF raftState'[i] = Leader /\ raftState[i] /= Leader
        THEN \A j \in Servers \ {i}:
                \A n \in DOMAIN log'[j]:
                    log'[j][n].term /= currentTerm'[i]
        ELSE TRUE

LeaderTermLogHasGreatestIdx ==
    \A i \in Servers:
        IF raftState'[i] = Leader
        THEN \A j \in Servers \ {i}:
                LET IncTermLogCount(a, b) == IF a.term = currentTerm'[i] THEN b + 1 ELSE b
                IN FoldSeq(IncTermLogCount, 0, log'[i]) >= FoldSeq(IncTermLogCount, 0, log'[j])
        ELSE TRUE

CheckLeader ==
    \A i \in Servers:
       raftState[i] /= Leader

InvSequence == <<
    \* ElectionSafety,
    \* LeaderAppendOnly,
    \* \* LogMatching,
    \* MonotonicCurrentTerm,
    \* MonotonicCommitIdx,
    \* MonotonicMatchIdx,
    \* CommittedLogDurable,
    \* CommittedLogReplicatedMajority,
    \* NextIdxGtMatchIdx,
    \* NextIdxGtZero,
    \* \* CheckLeader
    \* FollowerLogLELeaderLogAfterAE,
    \* CommitIdxLELogLen,
    \* LeaderCommitCurrentTermLogs,
    \* \* NewLeaderTermNotInLog,  \\ 因为分模块化测试会违反，先省略
    \* LeaderTermLogHasGreatestIdx  
>>

INV == Len(SelectSeqWithIdx(inv, LAMBDA x, y: ~x /\ y \notin netman.no_inv)) = 0



 (***************************************************************************
  Next actions
 ***************************************************************************)

DoElectionTimeout ==
    /\ PrePrune(netman.n_elec, "MaxElectionTimes")
    /\ \E n \in Servers: CheckStateIs(n, Follower) /\ BecomeCandidate(n)
    /\ inv' = InvSequence

DoBecomeLeader ==
    /\ PrePrune(netman.n_becomeLeader, "MaxBecomeLeaderTimes")
    /\ \A i \in Servers: 
        raftState[i] = Follower
    /\ \E n \in Servers:
        /\ BecomeLeader1(n)
    /\ inv' = InvSequence


DoHeartBeat ==
    /\ PrePrune(netman.n_hb, "MaxHeartBeatTimes")
    /\ \E n \in Servers:
        /\ raftState[n] = Leader
        /\ SendHeartBeatAll(n)
    /\ inv' = InvSequence


_DoRecvM(type, func(_)) ==
    /\ \E src, dst \in Servers:
        /\ src /= dst
        /\ LET m == NetGetMsg(src, dst)
           IN /\ m /= Nil
              /\ m.type = type
              /\ func(m)
    /\ inv' = InvSequence


DoHandleMsgRV == /\ _DoRecvM(M_RV, HandleMsgRV)

DoHandleMsgRVR == /\ _DoRecvM(M_RVR, HandleMsgRVR)
                  
DoHandleMsgAE == /\ _DoRecvM(M_AE, HandleMsgAE)

DoHandleMsgAER == /\ _DoRecvM(M_AER, HandleMsgAER)
                  
DoHandleMsgHB == /\ _DoRecvM(M_HB, HandleMsgHB)

DoHandleMsgHBR == /\ _DoRecvM(M_HBR, HandleMsgHBR)
                  
DoHandleMsgSnap == /\ _DoRecvM(M_SNAP, HandleMsgSnap)
                  
DoRecvEntry ==
    /\ PrePrune(netman.n_op, "MaxClientOperationsTimes")
    /\ \E n \in Servers, v \in Commands: RecvEntry(n, v)
    /\ inv' = InvSequence

\* DoNetworkDrop ==
\*     /\ PrePrune(NetGetDrop, "MaxDropTimes")
\*     /\ \E m \in msgs: 
\*         /\ NetUpdate2(NetDropMsg(m), <<"DoNetworkDrop", m.dst, m.src, m.seq>>)
\*         /\ UNCHANGED noNetVars
\*     /\ inv' = InvSequence

\* DoNetworkDup ==
\*     /\ PrePrune(NetGetDup, "MaxDupTimes")
\*     /\ \E m \in msgs: 
\*         /\ NetUpdate2(NetDupMsg(m), <<"DoNetworkDup", m.dst, m.src, m.seq>>)
\*         /\ UNCHANGED noNetVars
\*     /\ inv' = InvSequence

DoNetworkPartition ==
    /\ PrePrune(netman.n_part, "MaxPartitionTimes")
    /\ \E n \in Servers:
        /\ NetUpdate2(NetPartConn({n}), <<"DoNetworkPartition", n>>)
        /\ UNCHANGED noNetVars
    /\ inv' = InvSequence

DoNetworkCure ==
    /\ PrePrune(netman.n_cure, "MaxCureTimes")
    /\ NetIsParted
    /\ NetUpdate2(NetCureConn, <<"DoNetworkCure">>)
    /\ UNCHANGED noNetVars
    /\ inv' = InvSequence

DoSnapRequest == 
    /\ PrePrune(netman.n_rqSnap, "MaxSnapRequest")
    /\ \E n \in Servers: 
        /\ raftState[n] = Follower
        /\ LET index == commitIndex[n]
           IN /\ UNCHANGED <<snapVars>> 
              /\ FirstIdx(log[n], n) < index \* Ensure that operations are not repeated
              /\ SnapRequest(n)
    /\ inv' = InvSequence

DoRestart ==
    /\ PrePrune(netman.n_restart, "MaxRestart")
    /\ \E n \in Servers: 
        /\ Restart(n)
        /\ NetUpdate2(NetmanIncField("n_restart", NetNoAction2("msg_do_nothing")), <<"Dorestart", n>>)
    /\ inv' = InvSequence

Next == 
    \/ DoRestart
    \/ DoElectionTimeout
    \/ DoBecomeLeader
    \/ DoHeartBeat
    \/ DoHandleMsgRV
    \/ DoHandleMsgRVR
    \/ DoHandleMsgHB
    \/ DoHandleMsgHBR
    \/ DoHandleMsgAE
    \/ DoHandleMsgAER
    \/ DoHandleMsgSnap
    \/ DoRecvEntry
    \/ DoSnapRequest
    \/ DoNetworkPartition
    \/ DoNetworkCure



Spec == Init /\ [][Next]_vars
====