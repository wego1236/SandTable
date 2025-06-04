//
// Created by tangruize on 2/23/23.
//

#ifndef REDISTMET_UDPNETWORK_H
#define REDISTMET_UDPNETWORK_H

#include "common.h"
#include "Network.h"

class UdpNetwork: public Network {
private:
    socklen_t addrlen;
public:
    explicit UdpNetwork(bool run_accept=true);
    int accept();
    void udp_loop();
    void udp_in_background();
    static bool is_connected(int fd);
    bool connect(const Node &n) override;
    void connect_all() override;
    bool is_all_connected() override;
    ssize_t send_to(const Node &peer, const string &data) override;
    ssize_t recv_from(const Node &peer, string &data) override;
};

ssize_t send_to(const Node &peer, const string &data);

ssize_t recv_from(const Node &peer, string &data);


#endif //REDISTMET_TCPNETWORK_H
