//
// Created by tangruize on 2/14/23.
//
// WARN: we do not consider endian problem while serialization.
// WARN: we do not consider 32-bit or 64-bit memory.

#include <cassert>
#include <sys/time.h>
#include "Raft.h"
#include "Network.h"

extern "C" {
    void* raftInit();
    void raftRecvMsg(void* Node, const char* data, int length);
    void raftPeriodic(void* Node);
    void raftClientOperation(void* Node, const char* data);
    char* raftGet(void* Node, const char* data);
    void raftBecomePreCandidate(void* Node);
    void raftBecomeCandidate(void* Node);
    void raftBecomeLeader(void* Node);
    void raftCampaign(void* Node, const char* data);
    void raftBcastHeartbeat(void* Node);
    void raftBcastAppend(void* Node);
    void raftAskSnap(void* Node);
}



#define DATA_LEN 8

string state_machine = "init";

enum {
    MSG_AE,
    MSG_AER,
    MSG_RV,
    MSG_RVR
};



bool RaftInit() {  // 所以是一次性将所有节点都初始化好？
    void *me = raftInit();
    if (!me)
        return false;
    cerr_verbose << "Raft init, self id: " << config.get_self_node().getid() << endl;
    config.set_raft_server(me);
    return true;
}



bool RaftRecvMsg(Node node) {
    if (!config.get_node(node)) {
        cerr_warning << "RaftRecvMsg cannot find node" << endl;
        return false;
    }
    string data;
    int length = net->recv_from(node, data);
    if (length < 0)
        return false;



    char * dst = new char[length + 1];
    std::memcpy(dst, data.data(), length);
    // const char* cstr = data.c_str();
    // printf("in Raft.cpp raftrecvmsg : %s", cstr);

    raftRecvMsg(config.get_raft_server(), dst, length);
    return true;
}

// 这个操作是什么
bool RaftPeriodic() {
    // const char* cstr = time.c_str();
    auto * me =  config.get_raft_server();
    raftPeriodic(me);
    return true;
}

bool RaftBecomePreCandidate(){
    auto * me =  config.get_raft_server();
    raftBecomePreCandidate(me);
    return true;
}

bool RaftBecomeCandidate(){
    auto * me =  config.get_raft_server();
    raftBecomeCandidate(me);
    return true;
}

bool RaftBecomeLeader(){
    auto * me =  config.get_raft_server();
    raftBecomeLeader(me);
    return true;
}

bool RaftBcastHeartBeat(){
    auto * me =  config.get_raft_server();
    raftBcastHeartbeat(me);
    return true;
}

bool RaftBcastAppend(){
    auto * me =  config.get_raft_server();
    raftBcastAppend(me);
    return true;
}

bool RaftAskSnap(){
    auto * me =  config.get_raft_server();
    raftAskSnap(me);
    return true;
}

bool RaftCampaign(string data){
    auto * me =  config.get_raft_server();
    const char* cstr = data.c_str();
    raftCampaign(me, cstr);
    return true;
}


bool RaftClientOperation(string data) {
    auto *me = config.get_raft_server();
    const char* cstr = data.c_str();
    raftClientOperation(me, cstr);
    return true;
}




bool RaftRepl(const string &cmd) {
    auto tokens = tokenize(cmd);
    if (tokens.empty()) {
        return false;
    }
    if (tokens[0] == "init") {
        return RaftInit();
    } else if (tokens[0] == "recvfrom") {
        if (tokens.size() <= 1)
            return false;
        else 
            return RaftRecvMsg(tokens[1]);
    } else if (tokens[0] == "BecomePrecandidate") {
         RaftBecomePreCandidate();
         return true;
    } else if (tokens[0] == "BecomeCandidate") {
         RaftBecomeCandidate();
         return true;
    } else if (tokens[0] == "campaign") {
        if (tokens.size() <= 1)
            return false;
        else 
            return RaftCampaign(tokens[1]);
    } else if (tokens[0] == "BecomeLeader") {
         RaftBecomeLeader();
         return true;
    }  else if (tokens[0] == "heartBeat") {
         RaftBcastHeartBeat();
         return true;
    }  else if (tokens[0] == "askSnap") {
         RaftAskSnap();
         return true;
    } else if (tokens[0] == "bcast_append") {
         RaftBcastAppend();
         return true;
    } else if (tokens[0] == "periodic") {
         RaftPeriodic();
         return true;
    } else if (tokens[0] == "cli") {
        if (tokens.size() <= 1)
            return false;
        return RaftClientOperation(tokens[1]);
    } else if (tokens[0] == "statemachine" ) {
        cerr << state_machine << endl;
        return true;
    }
    else {
        return false;
    }
    return false;
}

string RaftGet(const string &variable) {
    auto *me = config.get_raft_server();
    const char* cstr = variable.c_str();
    string result = raftGet(me, cstr);
    return result;
}

// not implemented!
//void RaftAutoRun() {
//    if (!RaftInit()) {
//        cerr_warning << "cannot init" << endl;
//        abort();
//    }
//
//}