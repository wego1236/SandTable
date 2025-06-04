cmake_minimum_required(VERSION 3.16)
project(rsDriver)

set(CMAKE_CXX_STANDARD 20)
add_compile_options(-Wall -Wextra -Werror -Wno-unused-parameter -Wno-unused-function)

# add_subdirectory(deps/raft EXCLUDE_FROM_ALL)
add_subdirectory(tlpi EXCLUDE_FROM_ALL)

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_CURRENT_SOURCE_DIR}/cmake/")

find_package(gflags REQUIRED)
find_package(Readline REQUIRED)


# 单独生成的库所需的源文件
set(LIBRARY_SOURCES
        Network.cpp
        TcpNetwork.cpp 
        Config.cpp
        Node.cpp
        common.cpp
)
# set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl,-rpath,/path/to/myLibrary")

add_library(myLibrary SHARED ${LIBRARY_SOURCES})

target_link_libraries(myLibrary tlpi)

add_custom_target(world_so
    COMMAND make 
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/rust_so
)

# message("Current binary directory: ${CMAKE_CURRENT_BINARY_DIR}")
# message("Source binary directory: ${CMAKE_CURRENT_SOURCE_DIR}")
set(MyLib ${CMAKE_CURRENT_BINARY_DIR}/libmyLibrary.so )

set(WORLD_SO ${CMAKE_CURRENT_SOURCE_DIR}/rust_so/target/debug/libworld.so)

include_directories( ${CMAKE_CURRENT_SOURCE_DIR}/rust_so/include)

add_executable(RedisTMet main.cpp Network.h Config.h Repl.cpp Repl.h Raft.cpp Raft.h common.h Node.h  TcpNetwork.h UdpNetwork.h)

# Add dependencies for the custom target if needed
add_dependencies(RedisTMet  world_so)

target_link_libraries(RedisTMet PUBLIC
        readline
        gflags
        tlpi
        ${MyLib}
        # myLibrary
        ${WORLD_SO})