#!/bin/bash

PROJECT_DIR=$(realpath $(dirname "$(realpath "$0")")/../..)
SCRIPTS_DIR=$PROJECT_DIR/scripts

gen_config_script=$SCRIPTS_DIR/configuration/gen_3_config.sh
generator_script=$SCRIPTS_DIR/model-simulation/testcase_generator.py
check_script=$SCRIPTS_DIR/run-testcase/start.sh

TRACE=$1
TRACE_DIR=$(realpath $(dirname $TRACE))
TEST_DIR=$TRACE_DIR/test
TEST_TRACE=$TEST_DIR/trace
CONFIG_FILE=$TEST_DIR/config/config.txt
DEBUG=${2:+-d}

set -e
mkdir -p $TEST_DIR/config
cp $TRACE $TEST_TRACE
bash $gen_config_script 3 10.1.0.0/24 $CONFIG_FILE
cd $TEST_DIR
python3 $generator_script -i -c $CONFIG_FILE $TEST_TRACE

env -u TMUX bash $check_script $DEBUG $TEST_DIR
