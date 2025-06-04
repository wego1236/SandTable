MC_DIR ?= $(shell realpath $(shell pwd)/../model-simulation/model)
TARGET_MC_DIR ?= $(shell ls -td ${MC_DIR}/*/ | head -1)
TARGET_DIR ?= $(shell ls -td ${TARGET_MC_DIR}/*/ | head -1)
TARGET ?=

run: build
	if test ${TARGET}; then ./start.sh ${TARGET}; else for i in $$(ls ${TARGET_DIR} | grep '^trace.*\.dir$$'); do ./start.sh ${TARGET_DIR}/$$i; tmux a; done; fi

build:
	cd ../.. && cmake -B cmake-build-debug && cmake --build cmake-build-debug -j $(shell nproc)