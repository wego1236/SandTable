#!/bin/bash

PROJECT_DIR=$(realpath $(dirname "$(realpath "$0")")/../..)
CONTROLLER=$PROJECT_DIR/cmake-build-debug/controller/controller
INTERCEPTRO_SH=$PROJECT_DIR/cmake-build-debug/interceptor/run.sh
SPSSH_SH=$PROJECT_DIR/deps/spssh/spssh.sh
CLIENT=$PROJECT_DIR/cmake-build-debug/client/RedisTMet

function usage() {
    echo "Usage: start.sh trace_xxx.dir"
    exit 1
}

TESTCASE_DIR=$1
if ! test -d "$TESTCASE_DIR"; then
    usage
fi
TESTCASE_DIR=$(realpath $TESTCASE_DIR)

export TMPDIR=$(mktemp -u -d -p $TESTCASE_DIR)
mkdir -p $TMPDIR

cd $TESTCASE_DIR
CONFIG_FILE=$(realpath config/config.txt)

HOST_CMD="$CONTROLLER -detail -config $CONFIG_FILE -tmpdir $TMPDIR; exit"

cat <<EOF | "$SPSSH_SH" -H -S -q -t -e -s -r "$HOST_CMD" -w "$TMPDIR" root@n{1,2,3}
cd $TESTCASE_DIR
$INTERCEPTRO_SH -config $CONFIG_FILE $CLIENT -config $CONFIG_FILE -detail -name "n\${SSH_NO}"; exit
EOF
test -t 0 && tmux attach -t SPSSH$(echo -n $TMPDIR | tail -c 2)>/dev/null
tmux wait-for "$TMPDIR"