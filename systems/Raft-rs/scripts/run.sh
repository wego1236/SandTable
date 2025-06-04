#!/bin/bash

PROJECT_DIR=$(realpath $(dirname "$(realpath "$0")")/../..)
MC_DIR=$PROJECT_DIR/scripts/model-simulation/model
TARGET_MC_DIR=$(ls -td ${MC_DIR}/*/ | head -1)
TARGET_DIR=$(ls -td ${TARGET_MC_DIR}/*/ | head -1)
START_SCRIPT=$(dirname "$(realpath "$0")")/start-lxd.sh

inotifywait -e close_write -m -r -q  --format '%w %f' $TARGET_DIR | while read line; do
    a=($line)
    if [[ ${a[0]} =~ .*MC.out.dir/$ ]]; then
        is_exit=true
    elif test ${a[1]} != 'traces.txt'; then
        continue
    fi
    echo "${a[0]}"
    $START_SCRIPT "${a[0]}"
    if test "$is_exit" = true; then
        kill -10 $$
    fi
done