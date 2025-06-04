//
// Created by tangruize on 2/23/23.
//

#include "UdpNetwork.h"
#include <thread>
#include <sys/epoll.h>

extern "C" {
#include "tlpi/inet_sockets.h"
}

UdpNetwork::UdpNetwork(bool run_background): Network() {
    if (self.name.empty())
        return;
    addrlen = 0;
    // 这里为什么只传 port?
    sockfd = inetBind(self.getport().c_str(), SOCK_DGRAM, &addrlen);
    if (sockfd == -1) {
        throw_syserror("inetBind");
    }
    cerr_verbose << "bind port " << self.getport() << endl;
    if (set_nonblocking(sockfd) == -1) {
        throw_syserror("set_nonblocking");
    }
//     if (run_background) {
//         udp_in_background();
// //        cerr_verbose << "running accept in background" << endl;
//     }
}

bool UdpNetwork::is_connected(int fd) {
    if (fd == -1)
        return false;
    char data;
    ssize_t size = recv(fd, &data, 1, MSG_PEEK | MSG_DONTWAIT);
    if (size == 0 || (size == -1 && errno != EAGAIN))
        return false;
    return true;
}


ssize_t UdpNetwork::send_to(const Node &peer, const string &data) {
//    auto it = peers.find(peer);
    auto it = find_node(peer);
    if (it == peers.end() || it->second < 0) {
        cerr_warning << "cannot send to " << peer.to_string() << endl;
        return -1;
    }
    string to_send;
    uint32_t size = htonl(data.size());
    to_send.resize(sizeof(size));
    *(uint32_t *)&to_send.front() = size;
    to_send += data;
    ssize_t ret = write(it->second, to_send.c_str(), to_send.size());
    if (ret != ssize_t(data.size()) + 4) {
        if (ret == -1)
            warn_syserror("send_to");
        else {
            cerr_warning << "partial send: " + to_string(ret) + "/" + to_string(to_send.size());
        }
    }
    return ret;
}

ssize_t UdpNetwork::recv_from(const Node &peer, string &data) {
//    auto it = peers.find(peer);
    auto it = find_node(peer);
    if (it == peers.end() || it->second < 0) {
        cerr_warning << "cannot find node " << peer.to_string() << endl;
        return -1;
    }
    uint32_t size;
    struct sockaddr_in cli_addr;
    socklen_t addrlen = sizeof(struct sockaddr_in);
    ssize_t ret = recvfrom(it->second, &size, sizeof(size), MSG_DONTWAIT | MSG_PEEK, (struct sockaddr* )&cli_addr, &addrlen);
    if (ret != 4) {
        if (ret == -1) {
            warn_syserror("UdpNetwork::recv_from");
            close(it->second);
            it->second = -1;
        } else {
            cerr_warning << "recv_from cannot get size" << endl;
        }
        return -1;
    }
    if (recvfrom(it->second, &size, sizeof(size), MSG_DONTWAIT, (struct sockaddr* )&cli_addr, &addrlen) != 4) {  // discard 4 bytes
        cerr_warning << "recv_from failed to discard 4 bytes" << endl;
        return -1;
    }
    size = ntohl(size);
    if (size > 65535) {
        cerr_warning << "recv_from: size is too big!" << endl;
        abort();
    }
    data.resize(size);
    ret = recvfrom(it->second, &data.front(), size, MSG_WAITALL, (struct sockaddr* )&cli_addr, &addrlen);
    if (ret == -1) {
        warn_syserror("recv_from");
    }
    return ret;
}

bool all_of(const int* begin, const int* end, bool (*predicate)(int)) {
    for (const int* p = begin; p != end; ++p) {
        if (!predicate(*p)) {
            return false;
        }
    }
    return true;
}

