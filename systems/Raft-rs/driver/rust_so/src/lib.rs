// 导入 raft-rs 库
#![allow(clippy::field_reassign_with_default)]
extern crate slog_term;
extern crate slog;

#[allow(unused_imports)]
use std::slice;
// use slog::*;

#[allow(unused_imports)]
extern crate raft;
use raft::eraftpb::Snapshot;
use protobuf::Message as PbMessage;
use raft::{Config, storage::MemStorage, raw_node::RawNode, StateRole, ProgressState};
use raft::eraftpb::{ Entry, Message, MessageType};
use raft::{CAMPAIGN_PRE_ELECTION, CAMPAIGN_ELECTION, CAMPAIGN_TRANSFER};
// use raft::{prelude::*};

// use protobuf::Message;
use std::ffi::CString;
use libc::{c_int, ssize_t, c_char};

use slog::Drain;
// use std::collections::{HashMap};
use std::time::{Duration, Instant};
use std::{str};
use std::ffi::CStr;
// use slog::*;

// use regex::Regex;

use slog::{error, info, o};

// #[link(name = "config")]
#[link(name = "myLibrary")]
extern "C" {
    fn getIdSelf() -> u64;
    fn send_to(node_id: c_int, data: *const libc::c_char, length: ssize_t) -> ssize_t;
    #[allow(dead_code)]
    fn recv_from(node_id: c_int, data: *const libc::c_char) -> ssize_t;
}



#[no_mangle]
pub extern "C" fn raftInit() -> *mut Node {

    let _node = create_node().unwrap();
    let node = Box::new(_node);

    Box::into_raw(node)
}


#[no_mangle]
pub extern "C" fn raftRecvMsg(ptr: *mut Node, data: *const libc::c_char, length: usize) {

    // 将 C 字符串指针转换为 Rust 字符串切片
    // let c_str = unsafe {
    //     assert!(!data.is_null());
    //     CStr::from_ptr(data)
    // };

    let data_slice: &[u8] = unsafe { 
        assert!(!data.is_null());
        std::slice::from_raw_parts(data as *const u8, length) 
    };
    // 将 CStr 转换为 Rust 的 str 类型
    // let data = c_str.to_str().expect("Invalid UTF-8");

    // 尝试将字节切片转换为 &str
    match std::str::from_utf8(data_slice) {
        
        Ok(data_str) => {
            unsafe{
                // println!("data {} node {}", data, (*ptr).get_id());
        
                (*ptr).recv_msg(data_str);
            };
        },
        Err(e) => {
            // 处理转换失败的情况，例如不合法的UTF-8数据
            println!("Failed to convert data to str: {}", e);
        }
    }
    // unsafe{
    //     // println!("data {} node {}", data, (*ptr).get_id());

    //     (*ptr).recv_msg(data);
    // };
    

}

#[no_mangle]
pub extern "C" fn raftClientOperation(ptr: *mut Node, data: *const libc::c_char) {
    let c_str = unsafe {
        assert!(!data.is_null());
        CStr::from_ptr(data)
    };
    

    // 将 CStr 转换为 Rust 的 str 类型
    let data = c_str.to_str().expect("Invalid UTF-8");
    println!("propose {}", data);
    unsafe{
        // println!("data {} node {}", data, (*ptr).get_id());
        (*ptr).propose(data);
    };
    

    
}
#[allow(unused_imports)]
use std::{ptr::addr_of};
use libc::{c_uint, printf};

#[allow(dead_code)]
fn print_buffer(addr: *const u8, size: isize) {
    let c_fmt = CString::new("%02X ").unwrap();
    let c_fmt_endl = CString::new("%02X\n").unwrap();
    unsafe {
        for i in 0..size {
            if (i + 1) % 8 == 0 {
                printf(c_fmt_endl.as_ptr(), *addr.offset(i) as c_uint);
            } else {
                printf(c_fmt.as_ptr(), *addr.offset(i) as c_uint);
            }
        }
    }
}


#[no_mangle]
pub extern "C" fn raftPeriodic(ptr: *mut Node) {
    unsafe{
        // println!("node {}",  (*ptr).get_id());
        (*ptr).tick();
    };
}

#[no_mangle]
pub extern "C" fn raftCampaign(ptr: *mut Node, data: *const libc::c_char) {
    let c_str = unsafe {
        assert!(!data.is_null());
        CStr::from_ptr(data)
    };
    // 将 CStr 转换为 Rust 的 str 类型
    let data = c_str.to_str().expect("Invalid UTF-8");
    unsafe{
        (*ptr).campaign(data);
    };
}

#[no_mangle]
pub extern "C" fn raftBcastHeartbeat(ptr: *mut Node) {
    unsafe{
        (*ptr).bcast_heartbeat();
    };
}
#[no_mangle]
pub extern "C" fn raftBcastAppend(ptr: *mut Node) {
    unsafe{
        (*ptr).bcast_append();
    };
}

#[no_mangle]
pub extern "C" fn raftBecomePreCandidate(ptr: *mut Node) {
    unsafe{
        // println!("node {}",  (*ptr).get_id());
        (*ptr).become_pre_candidate();
    };
}

#[no_mangle]
pub extern "C" fn raftBecomeCandidate(ptr: *mut Node) {
    unsafe{
        // println!("node {}",  (*ptr).get_id());
        (*ptr).become_candidate();
    };
}



#[no_mangle]
pub extern "C" fn raftBecomeLeader(ptr: *mut Node) {
    unsafe{
        // println!("node {}",  (*ptr).get_id());
        (*ptr).become_leader();
    };
}

#[no_mangle]
pub extern "C" fn raftCompact(ptr: *mut Node) {
    unsafe{
        // println!("node {}",  (*ptr).get_id());
        (*ptr).compact();
    };
}

#[no_mangle]
pub extern "C" fn raftAskSnap(ptr: *mut Node) {
    unsafe{
        // println!("node {}",  (*ptr).get_id());
        (*ptr).askSanp();
    };
}

#[no_mangle]
pub extern "C" fn raftGet(ptr: *mut Node, data: *const libc::c_char) -> *mut c_char{
    // print_buffer(ptr as *const u8, 32);

    // 将输入的 C 字符串转换为 Rust 的字符串切片
    let input = unsafe { 
        assert!(!data.is_null());
        CStr::from_ptr(data).to_str().unwrap() 
    };

    let c_result: *mut c_char;
    unsafe{

        let result = (*ptr).get_var(input);
        // 将结果字符串转换为 C 字符串（CString）
        let c_string = CString::new(result).unwrap();
        c_result = c_string.into_raw();
    // 返回结果的原始指针
        
    };
    c_result
    
}


fn create_node() ->  Option<Node>{
    let id = unsafe{getIdSelf()};
    let decorator = slog_term::TermDecorator::new().build();
    let drain = slog_term::FullFormat::new(decorator).build().fuse();
    let drain = slog_async::Async::new(drain)
        .chan_size(4096)
        .overflow_strategy(slog_async::OverflowStrategy::Block)
        .build()
        .fuse();
    let logger = slog::Logger::root(drain, o!());

    let node = Node::create_node(id, &logger);
    return  Some(node);
}

#[allow(dead_code)]
fn is_initial_msg(msg: &Message) -> bool {
    let msg_type = msg.get_msg_type();
    msg_type == MessageType::MsgRequestVote
        || msg_type == MessageType::MsgRequestPreVote
        || (msg_type == MessageType::MsgHeartbeat && msg.commit == 0)
}


#[repr(C)]
pub struct Node {
    // None if the raft is not initialized.
    id : u64,
    raft_group: Option<RawNode<MemStorage>>,
    timer : Instant,
    timeout : Duration,
    logger : slog::Logger,
}

impl Node {

    fn create_node(
        id: u64,
        logger : &slog::Logger,
    ) -> Self {
        let mut cfg = example_config();
        cfg.id = id;
        
        let logger = logger.new(o!("tag" => format!("peer_{}", id)));
        let mut s = Snapshot::default();
        // Because we don't use the same configuration to initialize every node, so we use
        // a non-zero index to force new followers catch up logs by snapshot first, which will
        // bring all nodes to the same initial state.
        s.mut_metadata().index = 1;
        s.mut_metadata().term = 1;

        // 在这个地方设置voters
        s.mut_metadata().mut_conf_state().voters = vec![1, 2, 3];
        let storage = MemStorage::new();
        storage.wl().apply_snapshot(s).unwrap();
        let raft_group = Some(RawNode::new(&cfg, storage, &logger).unwrap());

        // let id = id as i32;
        let timer = Instant::now();
        let timeout = Duration::from_millis(100);
        Node {
            id ,
            raft_group,
            timer,
            timeout,
            logger,
        }
    }

    // Initialize raft for followers.
    #[allow(dead_code)]
    fn initialize_raft_from_message(&mut self, msg: &Message, logger: &slog::Logger) {
        if !is_initial_msg(msg) {
            return;
        }
        let mut cfg = example_config();
        cfg.id = msg.to;
        self.id = msg.to;
        let logger = logger.new(o!("tag" => format!("peer_{}", self.id)));
        let storage = MemStorage::new();
        self.raft_group = Some(RawNode::new(&cfg, storage, &logger).unwrap());
    }

    #[allow(dead_code)]
    fn step(&mut self, msg: Message, logger: &slog::Logger) {
        if self.raft_group.is_none() {
            if is_initial_msg(&msg) {
                self.initialize_raft_from_message(&msg, logger);
            } else {
                return;
            }
        }
        let raft_group = self.raft_group.as_mut().unwrap();
        let _ = raft_group.step(msg);
    }

    #[allow(dead_code)]
    fn get_id(& self) -> u64{
        return self.id;
    }

    fn recv_msg(&mut self, input : &str){
        if self.raft_group.is_none() {
            return;
        }

        let raft_group =  self.raft_group.as_mut().unwrap();
        let logger = &self.logger; 
        
        let _size = 4025;

        let bytes = input.as_bytes();
        match Message::parse_from_bytes(&bytes) {
            Ok(deserialized_message) => {
                // 成功将字节数组反序列化为消息对象
                // 在这里处理反序列化后的消息对象
                println!("step message: {:?}", deserialized_message);
                let _ = raft_group.step(deserialized_message);
                
            }
            Err(err) => {
                // 发生错误
                error!(logger, "Error deserializing message: {:?}", err);
                return;
            }
        }
        on_ready(raft_group, logger);
    }

    fn campaign(&mut self, input : &str){

        if self.raft_group.is_none() {
            return;
        }

        let raft_group =  self.raft_group.as_mut().unwrap();
        let logger = &self.logger;   
        if input == "normal"{
            raft_group.campaign();
        } else if input == "pre"{
            raft_group.raft.campaign(CAMPAIGN_PRE_ELECTION);
        } else if input == "transfer"{
            raft_group.raft.campaign(CAMPAIGN_TRANSFER);
        }
        on_ready(raft_group, logger);
    }

// 实际上 在 raft-rs中不需要时钟驱动 我们通过tick就可以驱动
// 实际上后续 heartBeat campaign 都不需要专门时钟一次次推进，我这里想做的就是在处理完事件之后有一个更新到raft节点的过程
    fn tick(&mut self){

        if self.raft_group.is_none() {
            return;
        }

        let raft_group =  self.raft_group.as_mut().unwrap();
        let logger = &self.logger;   

        // raft_group.tick();

        on_ready(raft_group, logger);
    }

    fn bcast_heartbeat(&mut self){

        if self.raft_group.is_none() {
            return;
        }

        let raft_group =  self.raft_group.as_mut().unwrap();
        let logger = &self.logger;   

        println!("raft ping");
        raft_group.raft.ping();

        on_ready(raft_group, logger);
    }

    fn bcast_append(&mut self){

        if self.raft_group.is_none() {
            return;
        }

        let raft_group =  self.raft_group.as_mut().unwrap();
        let logger = &self.logger;   

        println!("raft bcast append");
        raft_group.raft.bcast_append();

        on_ready(raft_group, logger);
    }

    fn become_candidate(&mut self){
        if self.raft_group.is_none() {
            return;
        }

        let raft_group =  self.raft_group.as_mut().unwrap();
        let logger = &self.logger;   
        raft_group.raft.become_candidate();

        on_ready(raft_group, logger);
    }

    fn become_leader(&mut self){
        if self.raft_group.is_none() {
            return;
        }
        let raft_group =  self.raft_group.as_mut().unwrap();
        let logger = &self.logger;   

        raft_group.raft.become_candidate();
        raft_group.raft.become_leader();
        raft_group.raft.bcast_append();

        on_ready(raft_group, logger);
    }


    fn compact(&mut self){
        if self.raft_group.is_none() {
            return;
        }
        let raft_group =  self.raft_group.as_mut().unwrap();
        let logger = &self.logger;   

        let store = raft_group.raft.raft_log.store.clone();

        store.wl().compact(raft_group.raft.r.raft_log.committed).unwrap();

        on_ready(raft_group, logger);
    }

    fn askSanp(&mut self){
        if self.raft_group.is_none() {
            return;
        }
        let raft_group =  self.raft_group.as_mut().unwrap();
        let logger = &self.logger;   

        raft_group.request_snapshot();

        on_ready(raft_group, logger);
    }



    fn become_pre_candidate(&mut self){
        if self.raft_group.is_none() {
            return;
        }

        let raft_group =  self.raft_group.as_mut().unwrap();
        let logger = &self.logger;   

        raft_group.raft.become_pre_candidate();

        on_ready(raft_group, logger);
    }
        // let mut timeout = Duration::from_millis(100); 
        // let d = self.timer.elapsed();
        // self.timer = Instant::now();
        // let res = d >= self.timeout;
        // if d >= self.timeout {
        //     self.timeout = Duration::from_millis(100);
        //     // We drive Raft every 100ms.
        //     info!(logger, "raft_group {} tick", self.id);
            
        // } else {
        //     timeout -= d;
        // }

    fn propose(&mut self, data :&str){
        if self.raft_group.is_none() {
            return;
        }

        let raft_group =  self.raft_group.as_mut().unwrap();
        let logger = &self.logger; 

        // 如果我不设置回调函数呢？其实应该也没什么，毕竟就是单纯
        let data_bytes = data.as_bytes().to_vec();
        raft_group.propose(vec![], data_bytes).unwrap();
        on_ready(raft_group, logger);
    }

    #[warn(unused_must_use)]
    fn get_var(&mut self, data :&str)-> String {
        let logger = &self.logger; 
        info!(logger, "node {} get {}", self.id, data);
        if let Some(raw_node) = &self.raft_group{
            match data {
                "state" => {
                    match raw_node.raft.soft_state().raft_state{
                        StateRole::Follower =>{
                            return "1".to_string();
                        }StateRole::Candidate =>{
                            return "3".to_string();
                        }StateRole::Leader =>{
                            return "4".to_string();
                        }StateRole::PreCandidate =>{
                            return "2".to_string();
                        }
                    }
                }"current_term" => {
                    return raw_node.raft.hard_state().term.to_string();
                }
                "log" => {
                    let mut res = "[(1, 'Nil', 1)".to_string();
                    let all_ents = raw_node.raft.raft_log.all_entries();
                    for (index, ent) in all_ents.iter().enumerate() {
                        // if res == "".to_string(){
                        //     res = format!{"[({}, \'{}\')",  ent.get_term(),  String::from_utf8_lossy(ent.get_data())};
                        // } else {
                        //     res = format!{"{}, ({}, \'{}\')", res, ent.get_term(),  String::from_utf8_lossy(ent.get_data())};
                        // }  
                        let mut ent_data = String::from_utf8_lossy(ent.get_data()).into_owned();
                        ent_data = if ent_data.is_empty() {
                            "Nil".to_string()
                        } else{
                            ent_data
                        };
                        res = format!{"{}, ({}, \'{}\', {})", res, ent.get_term(), ent_data, index + 2};                    
                    }
                    // if res != "".to_string(){
                    //     res = format!{"{}]", res};
                    // }
                    res = format!{"{}]", res};

                        
                    println!("raft log {:?}", all_ents);
                    println!("raft_log first_index {:?}", raw_node.raft.raft_log.first_index());
                    println!("raft_log last_index {:?}", raw_node.raft.raft_log.last_index());
                    println!("raft_log committed {:?}", raw_node.raft.raft_log.committed);
                    println!("raft_log persisted {:?}", raw_node.raft.raft_log.persisted);
                    return res.to_string();
                }
                "commit_idx" => {
                    return raw_node.raft.raft_log.committed.to_string();                    
                }"match_idx" => {
                    let mut res = "".to_string();
                    raw_node.raft.prs()
                        .iter()
                        .filter(|&(id, _)| *id != self.get_id())
                        .for_each(|(id, pr)| {
                            if res == "".to_string(){
                                res = format!{"{{\'n{}\': {}",  id, pr.matched}
                            } else {
                                res = format!{"{}, \'n{}\': {}", res, id, pr.matched}
                            }                        });
                        res = format!{"{}}}", res};
                    return res.to_string();
                }"next_idx" => {
                    let mut res = "".to_string();
                    raw_node.raft.prs()
                        .iter()
                        .filter(|&(id, _)| *id != self.get_id())
                        .for_each(|(id, pr)| {
                            if res == "".to_string(){
                                res = format!{"{{\'n{}\': {}",  id, pr.next_idx}
                            } else {
                                res = format!{"{}, \'n{}\': {}", res, id, pr.next_idx}
                            }
                        });
                        res = format!{"{}}}", res};
                    return res.to_string();
                }"pr_pending" => {
                    let mut res = "".to_string();
                    raw_node.raft.prs()
                        .iter()
                        .filter(|&(id, _)| *id != self.get_id())
                        .for_each(|(id, pr)| {
                            if res == "".to_string(){
                                res = format!{"{{\'n{}\': {}",  id, pr.pending_request_snapshot}
                            } else {
                                res = format!{"{}, \'n{}\': {}", res, id, pr.pending_request_snapshot}
                            }
                        });
                        res = format!{"{}}}", res};
                    return res.to_string();
                }
                "pending_snapshot" => {
                    return raw_node.raft.pending_request_snapshot.to_string();
                }"progress" => {
                    let mut res = "".to_string();
                    raw_node.raft.prs()
                        .iter()
                        .filter(|&(id, _)| *id != self.get_id())
                        .for_each(|(id, pr)| {
                            let state_str = match pr.state{
                                ProgressState::Probe => "Probe".to_string(),
                                ProgressState::Replicate =>"Replicate".to_string(),
                                ProgressState::Snapshot => "Snapshot".to_string(),
                                
                            }; 
                            let pause_flag = if pr.is_paused(){
                                "pause"
                            } else {
                                "running"
                            };

                            if res == "".to_string(){
                                res = format!{"{{\'n{}\': {}, {}",  id, state_str, pause_flag}
                            } else {
                                res = format!{"{}, \'n{}\': {}, {}", res, id, state_str, pause_flag}
                            }
                        });
                    res = format!{"{}}}", res};
                    return res.to_string();
                }
                &_ => todo!()
            }  
        } else {
            error!(self.logger, "raft group empty");
            return "".to_string();
        }
    }
}


fn on_ready(raft_group: &mut RawNode<MemStorage>,
    logger: &slog::Logger,) {
    if !raft_group.has_ready() {
        return;
    }
    println!( "on_ready start");
    let store = raft_group.raft.raft_log.store.clone();

    // Get the `Ready` with `RawNode::ready` interface.
    let mut ready = raft_group.ready();

    println!( "ready  {:?}", ready);


    let handle_messages = |msgs: Vec<Message>| {
        
        for msg in msgs {
            let to = msg.to as i32;
            match msg.write_to_bytes() {
                Ok(mut serialized_message) => {
                    println!("to {}", to);
                    println!("serialized_message {:?}", serialized_message);

                    let length = serialized_message.len();
                    unsafe{send_to(to, serialized_message.as_mut_ptr() as *const libc::c_char, length.try_into().unwrap())};                  
                }
                Err(err) => {
                    error!(logger, "Error serializing message: {:?}", err);
                }
            }  
        }
    };

    

    if !ready.messages().is_empty() {
        // Send out the messages come from the node.
        handle_messages(ready.take_messages());
    }

    // Apply the snapshot. It's necessary because in `RawNode::advance` we stabilize the snapshot.
    if *ready.snapshot() != Snapshot::default() {
        let s = ready.snapshot().clone();
        if let Err(e) = store.wl().apply_snapshot(s) {
            error!(
                logger,
                "apply snapshot fail: {:?}, need to retry or panic", e
            );
            return;
        }
    }

    let mut _last_apply_index = 0;
    let mut handle_committed_entries = |committed_entries: Vec<Entry>| {
        
        
        for entry in committed_entries {
            // Mostly, you need to save the last apply index to resume applying
            // after restart. Here we just ignore this because we use a Memory storage.
            _last_apply_index = entry.index;

            // 感觉这里对于commited data 应该是对  commited 是不是不需要操作
            // if entry.data.is_empty() {
            //     // Emtpy entry, when the peer becomes Leader it will send an empty entry.
            //     continue;
            // }

            // if entry.get_entry_type() == EntryType::EntryNormal {
            //     if let Some(cb) = cbs.remove(entry.data.first().unwrap()) {
            //         cb();
            //     }
            // }
        

            // TODO: handle EntryConfChange
        }
    };
    handle_committed_entries(ready.take_committed_entries());
    // Persistent raft logs. It's necessary because in `RawNode::advance` we stabilize
    // raft logs to the latest position.
    if let Err(e) = store.wl().append(ready.entries()) {
        error!(
            logger,
            "persist raft log fail: {:?}, need to retry or panic", e
        );
        return;
    }

    if let Some(hs) = ready.hs() {
        // Raft HardState changed, and we need to persist it.
        store.wl().set_hardstate(hs.clone());
    }

    if !ready.persisted_messages().is_empty() {
        // Send out the persisted messages come from the node.
        handle_messages(ready.take_persisted_messages());
    }

    // Call `RawNode::advance` interface to update   flags in the raft.
    let mut light_rd = raft_group.advance(ready);
    // Update commit index.
    if let Some(commit) = light_rd.commit_index() {
        store.wl().mut_hard_state().set_commit(commit);
    }
    // Send out the messages.
    handle_messages(light_rd.take_messages());
    // Apply all committed entries.
    handle_committed_entries(light_rd.take_committed_entries());
    // Advance the apply index.
    raft_group.advance_apply();
}


fn example_config() -> Config {
    Config {
        election_tick: 10,
        heartbeat_tick: 3,
        max_inflight_msgs : 1,  //  只允许一个
        // skip_bcast_commit: true, 
        ..Default::default()
    }
}

