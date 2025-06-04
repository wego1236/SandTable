
#ifndef WORLD_H
#define WORLD_H

extern "C"{
    void* raftInit();
    void raftRecvMsg(void* Node, const char* id, int length);
    void raftPeriodic(void* Node);
    void raftClientOperation(void* Node, const char* data);
    char* raftGet(void* Node, const char* data);
    void raftBecomePreCandidate(void* Node);
    void raftBecomeCandidate(void* Node);
    void raftBecomeLeader(void* Node);
    void raftCampaign(void* Node, const char* data);
    void raftCompact(void* Node);
    void raftAskSnap(void* Node);
    void raftBcastHeartbeat(void* Node);
    void raftBcastAppend(void* Node);
}


#endif