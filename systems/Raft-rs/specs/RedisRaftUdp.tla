---------------------------- MODULE RedisRaftUdp ----------------------------
(***************************************************************************)
(* Model assumptions:                                                      *)
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
CONSTANTS Servers  \* set of servers
CONSTANTS Follower, PreCandidate, Candidate, Leader  \* server states
CONSTANTS Commands, NoOp  \* commands of normal log entries 
CONSTANTS M_RV, M_RVR, M_AE, M_AER  \* basic raft msg types
CONSTANTS Nil  \* a placeholder

(***************************************************************************)
(* Variables definitions                                                   *)
(***************************************************************************)
VARIABLES current_term, voted_for, log  \* persistent vars
VARIABLES commit_idx, state  \* volatile vars
VARIABLES next_idx, match_idx  \* leader vars
VARIABLES voted_for_me  \* candidate vars
VARIABLES leader_id, match_msgid  \* node vars

(***************************************************************************)
(* Network variables and instance                                          *)
(***************************************************************************)
VARIABLES netman, netcmd, msgs
INSTANCE UdpNetwork WITH NULL_MSG <- Nil,
    _msgs <- msgs, _netman <- netman, _netcmd <- netcmd

(***************************************************************************)
(* Self manipulated invariants checking                                    *)
(***************************************************************************)
VARIABLES inv

(***************************************************************************)
(* Vars groups                                                             *)
(***************************************************************************)
serverVars    == <<current_term, voted_for, state>>
leaderVars    == <<next_idx, match_idx>>
candidateVars == <<voted_for_me>>
logVars       == <<log, commit_idx>>
nodeVars      == <<leader_id, match_msgid>>
netVars       == <<netman, netcmd, msgs>>
noNetVars     == <<serverVars, leaderVars, candidateVars, logVars, nodeVars>>
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
(* Type Ok                                                                 *)
(***************************************************************************)
TypeOkServerVars ==
    /\ current_term \in [ Servers -> Nat ]
    /\ voted_for    \in [ Servers -> Servers \cup {Nil} ]
    /\ state   \in [ Servers -> { Follower, PreCandidate, Candidate, Leader } ]
TypeOkLeaderVars ==
    /\ next_idx   \in [ Servers -> [ Servers -> Nat \ {0} ]]
    /\ match_idx  \in [ Servers -> [ Servers -> Nat ]]
TypeOkCandidateVars ==
    /\ voted_for_me \in [ Servers -> SUBSET Servers ]
TypeOkLogVars ==
    \* log data structure is complex, we skip checking it
    /\ commit_idx \in [ Servers -> Nat ]
TypeOkNodeVars ==
    /\ leader_id \in [ Servers -> Servers \cup {Nil} ]
    /\ match_msgid \in [ Servers -> [ Servers -> Nat ]]
TypeOk ==
    /\ TypeOkServerVars
    /\ TypeOkLeaderVars
    /\ TypeOkCandidateVars
    /\ TypeOkLogVars
    /\ TypeOkNodeVars

(***************************************************************************)
(* Init variables                                                          *)
(***************************************************************************)
InitServerVars ==  \* func: raft_new/raft_new_with_log
    /\ current_term = [ i \in Servers |-> 0 ]
    /\ voted_for    = [ i \in Servers |-> Nil ]
    /\ state   = [ i \in Servers |-> Follower ]
InitLeaderVars ==  \* func: raft_node_new/raft_become_leader
    /\ next_idx  = [ i \in Servers |-> [ j \in Servers |-> 1 ]]
    /\ match_idx = [ i \in Servers |-> [ j \in Servers |-> 0 ]]
InitCandidateVars ==  \* func: raft_node_new
    /\ voted_for_me = [ i \in Servers |-> {} ]
InitLogVars ==  \* func: raft_new_with_log
    /\ log = [ i \in Servers |-> <<>> ]
    /\ commit_idx = [ i \in Servers |-> 0 ]
InitNodeVars ==  \* raft_new_with_log
    /\ leader_id = [ i \in Servers |-> Nil ]
    /\ match_msgid = [ i \in Servers |-> [ j \in Servers |-> 0 ] ]
InitNetVars ==
    /\ InitUdpNetworkNetman(Servers, <<"Init", Cardinality(Servers)>>, 
            [ n_op |-> 0, n_ae |-> 0, n_elec |-> 0, no_inv |-> GetParameterSet("NoInv")])
InitInv ==
    /\ inv = <<>>

Init ==
    /\ InitServerVars
    /\ InitLeaderVars
    /\ InitCandidateVars
    /\ InitLogVars
    /\ InitNodeVars
    /\ InitNetVars
    /\ InitInv

(***************************************************************************)
(* Helper functions                                                        *)
(***************************************************************************)
NumServer == Cardinality(Servers)
Max(a, b) == IF a > b THEN a ELSE b
Min(a, b) == IF a < b THEN a ELSE b
IsQuorum(ss) == Cardinality(ss) * 2 > NumServer
IsQuorumNum(num) == num * 2 > NumServer
Update(var, n, value) == [ var EXCEPT ![n] = value ]
UpdateCurrentTerm(n, term) == current_term' = Update(current_term, n, term)
UpdateVotedFor(n, node) == voted_for' = Update(voted_for, n, node)
UpdateState(n, s) == state' = Update(state, n, s)
UpdateLeaderId(n, id) == leader_id' = Update(leader_id, n, id)
AddVotedForMe(me, node) == voted_for_me' = [ voted_for_me EXCEPT ![me] = @ \cup {node} ]
ClearVotedForMe(me) == voted_for_me' = [ voted_for_me EXCEPT ![me] = {} ]
UpdateMatchIdx(me, node, idx) == match_idx' = [ match_idx EXCEPT ![me][node] = idx ]
UpdateNextIdx(me, node, idx) == next_idx' = [ next_idx EXCEPT ![me][node] = IF idx < 1 THEN 1 ELSE idx ]
UpdateCommitIdx(n, idx) == commit_idx' = Update(commit_idx, n, idx)
UpdateMatchMsgid(me, node, id) == match_msgid' = [ match_msgid EXCEPT ![me][node] = id ]


(***************************************************************************)
(* Log helpers                                                             *)
(***************************************************************************)
\* Currently, the log won't be compacted
LogAppend(log_, entry) == Append(log_, entry)
LogCount(log_) == Len(log_)
LogGetEntry(log_, idx) ==
    IF idx > LogCount(log_) \/ idx <= 0 THEN Nil ELSE log_[idx]
LogGetEntriesFrom(log_, idx) ==
    IF idx > LogCount(log_) \/ idx <= 0 THEN <<>>
    ELSE SubSeq(log_, idx, LogCount(log_))
LogGetEntriesTo(log_, idx) ==
    IF Len(log_) < idx THEN log_
    ELSE SubSeq(log_, 1, idx)
LogDeleteEntriesFrom(log_, idx) == SubSeq(log_, 1, idx - 1)
LogCurrentIdx(log_) == LogCount(log_)
LogLastTerm(log_) ==
    LET idx == LogCount(log_)
        term == IF idx = 0 THEN 0 ELSE log_[idx].term
    IN term
LogGetTerm(log_, idx) ==
    IF LogCount(log_) < idx
    THEN Assert(FALSE, <<"no such log entry", log_, idx>>)
    ELSE IF idx = 0 THEN 0 ELSE log_[idx].term
LogGetMatchEntries(log_, entries, prevLogIdx) ==
    LET F[i \in 0..Len(entries)] ==
            IF i = 0 THEN Nil
            ELSE LET ety1 == LogGetEntry(log_, prevLogIdx + i)
                     ety2 == LogGetEntry(entries, i)
                     entries1 == LogGetEntriesTo(log_, prevLogIdx + i - 1)
                     entries2 == LogGetEntriesFrom(entries, i)
                 IN IF /\ F[i-1] = Nil
                       /\ \/ ety1 = Nil
                          \/ ety1.term /= ety2.term
                    THEN entries1 \o entries2
                    ELSE F[i-1]
        result == F[Len(entries)]
    IN IF result = Nil THEN log_ ELSE result

(***************************************************************************)
(* Msg constructors                                                        *)
(***************************************************************************)
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
    [ src |-> src, dst |-> dst, type |-> type, body |-> body ]

RequestVote(i, j) ==  \* func：raft_send_requestvote
    LET isPreCandidate == PreCandidate = state'[i]
        body == [ prevote |-> isPreCandidate,
                  term |-> IF isPreCandidate
                           THEN current_term'[i] + 1
                           ELSE current_term'[i],
                  candidate_id |-> i,
                  last_log_idx |-> LogCurrentIdx(log[i]),
                  last_log_term |-> LogLastTerm(log[i]) ]
    IN ConstructMsg(i, j, M_RV, body)

RequestVoteResponse(m, voted) ==  \* func: raft_recv_requestvote
    LET i == m.dst
        j == m.src
        req == m.body
        isPreVote == req.prevote
        rejectHasLeaderId == /\ isPreVote
                             /\ leader_id[i] /= Nil
                             /\ leader_id[i] /= req.candidate_id
        meTerm == current_term'[i]
        rejectMeTermIsBigger == meTerm > req.term
        rejectVotedOther == /\ meTerm = req.term
                            /\ voted /= Nil
                            /\ voted /= req.candidate_id
        meLastTerm == LogLastTerm(log[i])
        rejectMeLogNewer == \/ req.last_log_term < meLastTerm
                            \/ /\ req.last_log_term = meLastTerm
                               /\ req.last_log_idx < LogCurrentIdx(log[i])
        voteStatus == IF rejectHasLeaderId    THEN "not-vote: has leader"    ELSE
                      IF rejectMeTermIsBigger THEN "not-vote: term bigger"   ELSE
                      IF rejectVotedOther     THEN "not-vote: already voted" ELSE
                      IF rejectMeLogNewer     THEN "not-vote: log newer"     ELSE "voted"
        granted == voteStatus = "voted"
        body == [ prevote |-> req.prevote,
                  request_term |-> req.term,
                  term |-> IF isPreVote THEN meTerm ELSE Max(req.term, meTerm),
                  vote_granted |-> granted ]
    IN ConstructMsg(i, j, M_RVR, body) @@ [ status |-> voteStatus ]

AppendEntriesNext(i, j, next) ==  \* func: raft_send_appendentries
    LET prev_log_idx == next[i][j] - 1
        body == [ term |-> current_term[i],
                  leader_id |-> i,
                  leader_commit |-> commit_idx'[i],
                  prev_log_idx |-> prev_log_idx,
                  prev_log_term |-> LogGetTerm(log'[i], prev_log_idx),
                  entries |-> LogGetEntriesFrom(log'[i], next[i][j]) ]
    IN ConstructMsg(i, j, M_AE, body)

AppendEntries(i, j) == AppendEntriesNext(i, j, next_idx)

AppendEntriesResponseFail(m) ==  \* func: raft_recv_appendentries
    LET body == [ success |-> FALSE,
                  term |-> Max(current_term[m.dst], m.body.term),
                  current_idx |-> LogCurrentIdx(log[m.dst]),
                  msg_id |-> m.seq ]
    IN ConstructMsg(m.dst, m.src, M_AER, body)

AppendEntriesResponseSuccess(m) ==  \* func: raft_recv_appendentries
    LET req == m.body
        body == [ success |-> TRUE,
                  term |-> current_term[m.dst],
                  current_idx |-> req.prev_log_idx + Len(m.body.entries),
                  msg_id |-> m.seq ]
    IN ConstructMsg(m.dst, m.src, M_AER, body)


(***************************************************************************)
(* Raft actions                                                            *)
(***************************************************************************)

(***************************************************************************)
(* Become precandidate                                                     *)
(***************************************************************************)
BecomePrecandidate(i) ==  \* func: raft_become_precandidate
    /\ state[i] /= Leader
    /\ UpdateState(i, PreCandidate)
    /\ ClearVotedForMe(i)
    /\ UpdateLeaderId(i, Nil)  \* func: raft_election_start
    /\ UNCHANGED <<current_term, voted_for, leaderVars, logVars, match_msgid>>
    /\ LET ms == BatchReqMsgs(i, RequestVote)
       IN NetUpdate2(NetmanIncField("n_elec", NetBatchAddMsg(ms)), <<"BecomePrecandidate", i>>)

(***************************************************************************)
(* Recv requestvote                                                        *)
(***************************************************************************)
SetCurrentTerm(i, term) ==  \* func: raft_set_current_term
    /\ UpdateCurrentTerm(i, term)
    /\ UpdateVotedFor(i, Nil)

_BecomeFollower(i) ==  \* func: raft_become_follower
    /\ UpdateState(i, Follower)
    /\ UpdateLeaderId(i, Nil)

BecomeFollower(i, term) ==  
    /\ SetCurrentTerm(i, term)
    /\ _BecomeFollower(i)

RecvRequestVote(m) ==  \* func: raft_recv_requestvote
    LET req == m.body
        src == m.src
        dst == m.dst
        demote == ~req.prevote /\ current_term[dst] < req.term
        msg == RequestVoteResponse(m, IF demote THEN Nil ELSE voted_for[dst])
    IN /\ IF demote  \* Update the term only if this is not a prevote request
          THEN /\ UpdateCurrentTerm(dst, req.term)
               /\ UpdateState(dst, Follower)
          ELSE UNCHANGED <<current_term, state>>
       /\ IF msg.body.vote_granted /\ ~req.prevote
          THEN /\ Assert(~(state'[dst] \in {Leader, Candidate}),
                    <<"Leader/Candidate cannot vote", m, state'[dst], current_term'>>)
               /\ UpdateLeaderId(dst, Nil)
               /\ UpdateVotedFor(dst, src)
          ELSE IF demote
               THEN /\ UpdateLeaderId(dst, Nil)
                    /\ UpdateVotedFor(dst, Nil)
               ELSE UNCHANGED <<leader_id, voted_for>>
       /\ UNCHANGED <<leaderVars, candidateVars, logVars, match_msgid>>
       /\ NetUpdate2(NetReplyMsg(msg, m), 
            <<"RecvRequestVote", msg.status, dst, src, IF req.prevote THEN "prevote" ELSE "not-prevote">>)

(***************************************************************************)
(* Recv requestvote response                                               *)
(***************************************************************************)
BecomeCandidate(i, m) ==  \* func: raft_become_candidate
    /\ UpdateCurrentTerm(i, current_term[i] + 1)
    /\ ClearVotedForMe(i)
    /\ UpdateVotedFor(i, i)
    /\ UpdateLeaderId(i, Nil)
    /\ UpdateState(i, Candidate)
    /\ LET ms == BatchReqMsgs(i, RequestVote)
       IN NetUpdate2(NetReplyBatchAddMsg(ms, m), <<"RecvRequestVoteResponse", "BecomeCandidate", i>>) 

BecomeLeader(i, m) ==  \* func: raft_become_leader
    /\ LET noop == [ term |-> current_term[i], data |-> Nil ]
       IN log' = Update(log, i, LogAppend(log[i], noop))
    /\ UpdateState(i, Leader)
    /\ UpdateLeaderId(i, i)
    /\ match_idx' = [ match_idx EXCEPT ![i] = ( i :> LogCurrentIdx(log'[i]) ) @@ [ j \in Servers |-> 0 ] ]
    /\ LET next == [ next_idx EXCEPT ![i] = ( i :> 1 ) @@ [ j \in Servers |-> LogCurrentIdx(log'[i]) ] ]
           ms == BatchReqMsgsArg(i, AppendEntriesNext, next)
       IN /\ next_idx' = [ next EXCEPT ![i] = ( i :> 1 ) @@ [ j \in Servers |-> LogCurrentIdx(log'[i]) + 1 ] ]
          /\ NetUpdate2(NetReplyBatchAddMsg(ms, m), <<"RecvRequestVoteResponse", "BecomeLeader", i>>) 

RecvRequestVoteResponse(m) ==  \* func: raft_recv_requestvote_response
    LET resp == m.body
        src == m.src
        dst == m.dst
    IN /\ IF resp.term > current_term[dst]
          THEN /\ UNCHANGED <<leaderVars, candidateVars, logVars, match_msgid>>
               /\ BecomeFollower(dst, resp.term)
               /\ NetUpdate2(NetDelMsg(m), <<"RecvRequestVoteResponse", "term is smaller", dst, src>>)
          ELSE IF \/ /\ resp.prevote
                     /\ \/ ~(state[dst] = PreCandidate)
                        \/ resp.request_term /= current_term[dst] + 1
                  \/ /\ ~resp.prevote
                     /\ \/ ~(state[dst] = Candidate)
                        \/ resp.request_term /= current_term[dst]
               THEN /\ UNCHANGED noNetVars
                    /\ NetUpdate2(NetDelMsg(m), <<"RecvRequestVoteResponse", "vote is stale", dst, src>>)
               ELSE IF resp.vote_granted
                    THEN LET votes == Cardinality(voted_for_me[dst] \cup {src}) + 1  \* +1 is itself
                         IN IF IsQuorumNum(votes)
                            THEN IF state[dst] = PreCandidate
                                 THEN /\ UNCHANGED <<leaderVars, logVars, match_msgid>>
                                      /\ BecomeCandidate(dst, m)
                                 ELSE /\ UNCHANGED <<current_term, voted_for, commit_idx, match_msgid>>
                                      /\ AddVotedForMe(dst, src)
                                      /\ BecomeLeader(dst, m)
                            ELSE /\ UNCHANGED <<serverVars, leaderVars, logVars, nodeVars>>
                                 /\ AddVotedForMe(dst, src)
                                 /\ NetUpdate2(NetDelMsg(m), <<"RecvRequestVoteResponse", "granted", dst, src>>)
                    ELSE /\ UNCHANGED noNetVars
                         /\ NetUpdate2(NetDelMsg(m), <<"RecvRequestVoteResponse", "not granted", dst, src>>)

(***************************************************************************)
(* Send appendentries to all other nodes                                   *)
(***************************************************************************)
SendAppendentriesAll(n) ==  \* func: raft_send_appendentries_all
    /\ UNCHANGED <<logVars, serverVars, match_idx, candidateVars, nodeVars>>
    /\ LET ms == BatchReqMsgsArg(n, AppendEntriesNext, next_idx)
       IN /\ next_idx' = [ next_idx EXCEPT ![n] = ( n :> 1 ) @@ [ j \in Servers |-> LogCurrentIdx(log[n]) + 1 ] ]
          /\ NetUpdate2(NetmanIncField("n_ae", NetBatchAddMsg(ms)), <<"SendAppendentriesAll", n>>)

(***************************************************************************)
(* Recv appendentries                                                      *)
(***************************************************************************)
AcceptLeader(me, leader) ==  \* func: raft_accept_leader
    /\ UpdateState(me, Follower)
    /\ UpdateLeaderId(me, leader)

SetCommitIdx(n, idx) ==  \* func: raft_set_commit_idx
    /\ Assert(commit_idx[n] <= idx, "SetCommitIdx: commit_idx[n] <= idx")
    /\ Assert(idx <= LogCurrentIdx(log'[n]), <<"SetCommitIdx: idx <= LogCurrentIdx(log'[n])", n, idx, log'>>)
    /\ UpdateCommitIdx(n, idx)

RecvAppendentries(m) ==  \* func: raft_recv_appendentries
    LET req == m.body
        src == m.src
        dst == m.dst
        fail == AppendEntriesResponseFail(m)
        success == AppendEntriesResponseSuccess(m)
    IN IF req.term < current_term[dst]
       THEN /\ UNCHANGED noNetVars
            /\ NetUpdate2(NetReplyMsg(fail, m), <<"RecvAppendentries", "term is bigger", dst, src>>)
       ELSE /\ IF req.term > current_term[dst]
               THEN /\ UpdateCurrentTerm(dst, req.term)
                    /\ UpdateVotedFor(dst, Nil)
               ELSE UNCHANGED <<current_term, voted_for>>
            /\ AcceptLeader(dst, req.leader_id)
            /\ LET prevLogIsLastSnapshot == req.prev_log_idx = 0  \* snapshot is not implemented
                   ety == LogGetEntry(log[dst], req.prev_log_idx)
                   noPrevLog == ety = Nil
                   termMismatch == ety.term /= req.prev_log_term
               IN IF /\ ~prevLogIsLastSnapshot
                     /\ \/ noPrevLog
                        \/ termMismatch
                  THEN IF noPrevLog
                       THEN /\ UNCHANGED <<leaderVars, candidateVars, logVars, match_msgid>>
                            /\ NetUpdate2(NetReplyMsg(fail, m), <<"RecvAppendentries", "no prev log", dst, src>>)
                       ELSE \* term mismatch
                            /\ UNCHANGED <<leaderVars, candidateVars, commit_idx, match_msgid>>
                            /\ log' = Update(log, dst, LogDeleteEntriesFrom(log[dst], req.prev_log_idx))
                            /\ NetUpdate2(NetReplyMsg(fail, m), <<"RecvAppendentries", "term mismatch", dst, src>>)
                  ELSE \* success
                       /\ UNCHANGED <<leaderVars, candidateVars, match_msgid>>
                       /\ log' = Update(log, dst, LogGetMatchEntries(log[dst], req.entries, req.prev_log_idx))
                       /\ IF commit_idx[dst] < req.leader_commit
                          THEN LET lastLogIdx == Max(LogCurrentIdx(log'[dst]), 1)
                                   idxToCommit == Min(lastLogIdx, req.leader_commit)
                               IN SetCommitIdx(dst, idxToCommit)
                          ELSE UNCHANGED commit_idx
                       /\ NetUpdate2(NetReplyMsg(success, m), <<"RecvAppendentries", "success", dst, src>>)

(***************************************************************************)
(* Recv appendentries response                                             *)
(***************************************************************************)
AdvanceCommitIdx(me) ==  \* func: raft_update_commit_idx
    LET F[i \in 0..NumServer] ==
            IF i = 0 THEN <<<<>>, Servers>>
            ELSE LET n == CHOOSE n \in F[i-1][2]: TRUE
                 IN <<Append(F[i-1][1], match_idx'[me][n]), F[i-1][2] \ {n}>>
        sorted_match_idx == SortSeq(F[NumServer][1], LAMBDA x, y: x > y)
        commit == sorted_match_idx[NumServer \div 2 + 1]
    IN IF /\ commit > commit_idx[me]
          /\ current_term[me] = LogGetTerm(log[me], commit)
       THEN SetCommitIdx(me, commit)
       ELSE UNCHANGED commit_idx

\* syncIndex<0: not to set match_idx'
FlushAdvanceCommitIdx(me, syncIndex) ==  \* func: raft_flush
    IF state[me] /= Leader THEN TRUE
    ELSE /\ IF syncIndex >= 0
            THEN IF syncIndex > match_idx[me][me]
                 THEN UpdateMatchIdx(me, me, syncIndex)
                 ELSE UNCHANGED match_idx
            ELSE TRUE
         /\ AdvanceCommitIdx(me)

FlushSendAppendentries(me, m, info) ==  \* \* func: raft_flush
    LET F[i \in 0..NumServer] ==
        IF i = 0 THEN <<{}, Servers>>
        ELSE LET n == CHOOSE n \in F[i-1][2]: TRUE
                 idx == LogCurrentIdx(log'[me])
             IN IF \/ n = me
                   \/ next_idx[me][n] > idx
                THEN <<F[i-1][1] \cup {n}, F[i-1][2] \ {n}>>
                ELSE <<F[i-1][1], F[i-1][2] \ {n}>>
        excludes == F[NumServer][1]
        ms == _BatchExcludesReqMsgsArg(me, excludes, _Dummy2, AppendEntriesNext, next_idx)
        next_keep == [ s \in excludes |-> next_idx[me][s] ]
        next_update == [ s \in Servers \ excludes |-> LogCurrentIdx(log'[me]) + 1 ]
    IN /\ next_idx' = [ next_idx EXCEPT ![me] = next_keep @@ next_update ]
       /\ IF m = Nil  \* RecvEntry: client request
          THEN NetUpdate2(NetmanIncField("n_op", NetBatchAddMsg(ms)), info)
          ELSE NetUpdate2(NetReplyBatchAddMsg(ms, m), info)

RecvAppendentriesResponse(m) ==  \* func: raft_recv_appendentries_response
    LET resp == m.body
        src == m.src
        dst == m.dst
        failReason ==
            IF state[dst] /= Leader THEN "not leader" ELSE
            IF resp.msg_id < match_msgid[dst][src] THEN "msg_id is bigger" ELSE
            IF resp.term > current_term[dst] THEN "term is smaller" ELSE
            IF ~resp.success /\ resp.current_idx < match_idx[dst][src] THEN "stale response" ELSE
            IF ~resp.success THEN "retry" ELSE "success"
    IN IF failReason /= "success"
       THEN IF failReason = "retry"
            THEN LET next == Min(resp.current_idx + 1, LogCurrentIdx(log[dst]))
                     nextForAe == [next_idx EXCEPT ![dst][src] = next]
                     nextToUpdate == LogCurrentIdx(log'[dst]) + 1
                     retryAe == AppendEntriesNext(dst, src, nextForAe)
                 IN /\ UNCHANGED <<serverVars, match_idx, candidateVars, logVars, nodeVars>>
                    /\ UpdateNextIdx(dst, src, nextToUpdate)
                    /\ NetUpdate2(NetReplyMsg(retryAe, m), <<"RecvAppendentriesResponse", "retry", dst, src>>)
            ELSE /\ UNCHANGED <<leaderVars, candidateVars, logVars, match_msgid>>
                 /\ IF failReason = "term is smaller"
                    THEN BecomeFollower(dst, resp.term)
                    ELSE UNCHANGED <<serverVars, leader_id>>
                 /\ NetUpdate2(NetDelMsg(m), <<"RecvAppendentriesResponse", failReason, dst, src>>)
       ELSE \* success
            /\ UNCHANGED <<leader_id, log, serverVars, candidateVars>>
            /\ IF resp.current_idx > match_idx[dst][src]
               THEN UpdateMatchIdx(dst, src, resp.current_idx)
               ELSE UNCHANGED match_idx
            /\ IF resp.msg_id > match_msgid[dst][src]
               THEN UpdateMatchMsgid(dst, src, resp.msg_id)
               ELSE UNCHANGED match_msgid
            /\ FlushAdvanceCommitIdx(dst, -1)
            /\ FlushSendAppendentries(dst, m, <<"RecvAppendentriesResponse", "success", dst, src>>)

(***************************************************************************)
(* Recv client entry on Leader                                             *)
(***************************************************************************)
RecvEntry(n, data) ==  \* func: raft_recv_entry
    /\ state[n] = Leader
    /\ UNCHANGED <<serverVars, candidateVars, nodeVars>>
    /\ LET ety == [ term |-> current_term[n], data |-> data ]
       IN log' = Update(log, n, LogAppend(log[n], ety))
    /\ FlushAdvanceCommitIdx(n, LogCurrentIdx(log'[n]))
    /\ FlushSendAppendentries(n, Nil, <<"RecvEntry", n, data>>)

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
ElectionSafety ==
    LET TwoLeader ==
            \E i, j \in Servers:
                /\ i /= j
                /\ current_term'[i] = current_term'[j]
                /\ state'[i] = Leader
                /\ state'[j] = Leader
    IN ~TwoLeader

LeaderAppendOnly ==
    \A i \in Servers:
        IF state[i] = Leader /\ state'[i] = Leader
        THEN LET curLog == log[i]
                 nextLog == log'[i]
             IN IF Len(nextLog) >= Len(curLog)
                THEN SubSeq(nextLog, 1, Len(curLog)) = curLog
                ELSE FALSE
        ELSE TRUE

LogMatching ==
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
                ELSE Assert(FALSE, <<i, j, F>>)
        ELSE TRUE

MonotonicCurrentTerm == \A i \in Servers: current_term' [i] >= current_term[i]

MonotonicCommitIdx == \A i \in Servers: commit_idx'[i] >= commit_idx[i]

MonotonicMatchIdx ==
    \A i \in Servers:
        IF state[i] = Leader
        THEN \A j \in Servers:  match_idx'[i][j] >= match_idx[i][j]
        ELSE TRUE

CommittedLogDurable ==
    \A i \in Servers:
        LET len     == Min(commit_idx'[i], commit_idx[i])
            logNext == SubSeq(log'[i], 1, len)
            logCur  == SubSeq(log[i], 1, len)
        IN IF len = 1 THEN TRUE
           ELSE /\ Len(logNext) >= len
                /\ Len(logCur) >= len
                /\ logNext = logCur

CommittedLogReplicatedMajority ==
     \A i \in Servers:
        IF state'[i] /= Leader \/ commit_idx'[i] <= 1
        THEN TRUE
        ELSE LET entries == SubSeq(log'[i], 1, commit_idx'[i])
                 len     == Len(entries)
                 nServer == Cardinality(Servers)
                 F[j \in 0..nServer] ==
                    IF j = 0
                    THEN <<{}, {}>>
                    ELSE LET k == CHOOSE k \in Servers: k \notin F[j-1][1]
                             logLenOk == LogCount(log'[k]) >= commit_idx'[i]
                             kEntries == SubSeq(log'[k], 1, commit_idx'[i])
                         IN IF /\ logLenOk
                               /\ entries = kEntries
                             THEN <<F[j-1][1] \union {k}, F[j-1][2] \union {k}>>
                             ELSE <<F[j-1][1] \union {k}, F[j-1][2]>>
             IN IsQuorum(F[nServer][2])

NextIdxGtMatchIdx ==
    \A i \in Servers:
        IF state'[i] = Leader
        THEN \A j \in Servers \ {i}: next_idx'[i][j] > match_idx'[i][j]
        ELSE TRUE

NextIdxGtZero ==
    \A i \in Servers:
        IF state'[i] = Leader
        THEN \A j \in Servers: next_idx'[i][j] > 0
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
    IN IF cmd1 = "RecvAppendentries" /\ cmd2 \in { "success", "no prev log" }
       THEN IF log[follower] /= log'[follower]
            THEN LogCount(log'[follower]) <= LogCount(log'[leader])
            ELSE TRUE
       ELSE TRUE

CommitIdxLELogLen ==
    \A i \in Servers: commit_idx'[i] <= LogCount(log'[i])

LeaderCommitCurrentTermLogs ==
    \A i \in Servers:
        IF state'[i] = Leader
        THEN IF commit_idx[i] /= commit_idx'[i]
             THEN log'[i][commit_idx'[i]].term = current_term'[i]
             ELSE TRUE
        ELSE TRUE

NewLeaderTermNotInLog ==
    \A i \in Servers:
        IF state'[i] = Leader /\ state[i] /= Leader
        THEN \A j \in Servers \ {i}:
                \A n \in DOMAIN log'[j]:
                    log'[j][n].term /= current_term'[i]
        ELSE TRUE

LeaderTermLogHasGreatestIdx ==
    \A i \in Servers:
        IF state'[i] = Leader
        THEN \A j \in Servers \ {i}:
                LET IncTermLogCount(a, b) == IF a.term = current_term'[i] THEN b + 1 ELSE b
                IN FoldSeq(IncTermLogCount, 0, log'[i]) >= FoldSeq(IncTermLogCount, 0, log'[j])
        ELSE TRUE

InvSequence == <<
    ElectionSafety,
    LeaderAppendOnly,
    LogMatching,
    MonotonicCurrentTerm,
    MonotonicCommitIdx,
    MonotonicMatchIdx,
    CommittedLogDurable,
    CommittedLogReplicatedMajority,
    NextIdxGtMatchIdx,
    NextIdxGtZero,
    FollowerLogLELeaderLogAfterAE,
    CommitIdxLELogLen,
    LeaderCommitCurrentTermLogs,
    NewLeaderTermNotInLog,
    LeaderTermLogHasGreatestIdx
>>

INV == Len(SelectSeqWithIdx(inv, LAMBDA x, y: ~x /\ y \notin netman.no_inv)) = 0

(***************************************************************************)
(* State contraints                                                        *)
(***************************************************************************)

\*CONSTANTS MaxSentMsgs,
\*          MaxRecvMsgs,
\*          MaxWireMsgs,
\*          MaxClientOperationsTimes,
\*          MaxAppendEntriesTimes,
\*          MaxElectionTimes,
\*          MaxLogLength,
\*          MaxTerm,
\*          MaxDropTimes,
\*          MaxDupTimes,
\*          MaxUnorderTimes

GetRealLogLen(curLog) == SelectSeq(curLog, LAMBDA i: i.data /= NoOp)
GetMaxLogLen == Len(log[CHOOSE i \in Servers: \A j \in Servers \ {i}:
                            GetRealLogLen(log[i]) >= GetRealLogLen(log[j])])
GetMaxTerm == current_term[CHOOSE i \in Servers: \A j \in Servers \ {i}:
                            current_term[i] >= current_term[j]]

ScSent == CheckParameterMax(netman.n_sent, "MaxSentMsgs")
ScRecv == CheckParameterMax(netman.n_recv, "MaxRecvMsgs")
ScWire == CheckParameterMax(netman.n_wire, "MaxWireMsgs")
ScLog  == CheckParameterMax(GetMaxLogLen,  "MaxLogLength")
ScTerm == CheckParameterMax(GetMaxTerm,    "MaxTerm")
ScOp   == CheckParameterMax(netman.n_op,   "MaxClientOperationsTimes")
ScAe   == CheckParameterMax(netman.n_ae,   "MaxAppendEntriesTimes")
ScElec == CheckParameterMax(netman.n_elec, "MaxElectionTimes")
ScDrop == CheckParameterMax(netman.n_drop, "MaxDropTimes")
ScDup  == CheckParameterMax(netman.n_dup,  "MaxDupTimes")
ScUnorder == CheckParameterMax(netman.n_unorder, "MaxUnorderTimes")

SC == /\ ScSent /\ ScRecv /\ ScWire /\ ScLog
      /\ ScTerm /\ ScOp   /\ ScAe   /\ ScElec
      /\ ScDrop /\ ScDup  /\ ScUnorder

(***************************************************************************)
(* Next actions                                                            *)
(***************************************************************************)

_DoRecvM(type, func(_)) ==
    /\ \E m \in msgs:
        /\ m /= Nil
        /\ m.type = type
        /\ LET unorder == IF IsFirstMsg(m) THEN 0 ELSE 1
           IN CheckParameterMax(NetGetUnorder + unorder, "MaxUnorderTimes")
        /\ func(m)
    /\ inv' = InvSequence

DoRecvRequestVote == /\ _DoRecvM(M_RV, RecvRequestVote)

DoRecvRequestVoteResponse == /\ _DoRecvM(M_RVR, RecvRequestVoteResponse)

DoRecvAppendentries == /\ _DoRecvM(M_AE, RecvAppendentries)

DoRecvAppendentriesResponse == /\ _DoRecvM(M_AER, RecvAppendentriesResponse)

DoBecomePrecandidate ==
    /\ PrePrune(netman.n_elec, "MaxElectionTimes")
    /\ \E n \in Servers: BecomePrecandidate(n)
    /\ inv' = InvSequence

DoRecvEntry ==
    /\ PrePrune(netman.n_op, "MaxClientOperationsTimes")
    /\ \E n \in Servers, v \in Commands: RecvEntry(n, v)
    /\ inv' = InvSequence

DoSendAppendentriesAll ==
    /\ PrePrune(netman.n_ae, "MaxAppendEntriesTimes")
    /\ \E n \in Servers:
        /\ state[n] = Leader
        /\ SendAppendentriesAll(n)
    /\ inv' = InvSequence

DoNetworkDrop ==
    /\ PrePrune(NetGetDrop, "MaxDropTimes")
    /\ \E m \in msgs: 
        /\ NetUpdate2(NetDropMsg(m), <<"DoNetworkDrop", m.dst, m.src, m.seq, m.dup>>)
        /\ UNCHANGED noNetVars
    /\ inv' = InvSequence

DoNetworkDup ==
    /\ PrePrune(NetGetDup, "MaxDupTimes")
    /\ \E m \in msgs: 
        /\ NetUpdate2(NetDupMsg(m), <<"DoNetworkDup", m.dst, m.src, m.seq, m.dup>>)
        /\ UNCHANGED noNetVars
    /\ inv' = InvSequence

Next ==
    \/ DoRecvRequestVote
    \/ DoRecvRequestVoteResponse
    \/ DoRecvAppendentries
    \/ DoRecvAppendentriesResponse
    \/ DoBecomePrecandidate
    \/ DoRecvEntry
    \/ DoSendAppendentriesAll
    \/ DoNetworkDrop
    \/ DoNetworkDup

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Thu Mar 16 10:12:48 CST 2023 by tangruize
\* Created Tue Jan 03 16:38:47 CST 2023 by tangruize
