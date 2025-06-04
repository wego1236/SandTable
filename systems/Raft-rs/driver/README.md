# RedisTMet

目的：封装redis raft为可执行的程序。

## 网络

TCP网络：

- 读取配置文件并建立连接
- 使用字符串节点名作为发送方和接收方的标识（一个程序运行一个节点，仅需接收方）
- 消息开头为4字节网络字节序的包大小，后面为包内容
- API: connect, recv, send, accept

## Raft驱动

- 需要考虑超时设置
- API封装：RV, RVR, AE, AER, timeout, recv entry, send ae

## 用户界面

- 需要REPL来读取命令
- 配置文件，节点名和地址

## 配置文件

格式：

- node n1 1.1.1.1:9000
- node n1 1.1.1.1  (默认9000)
