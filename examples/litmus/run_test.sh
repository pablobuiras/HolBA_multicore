#!/bin/bash

RED='\033[0;31m'
GREEN='\033[0;32m'
NC='\033[0m'

LITMUS=${1}.litmus
JSON=${1}.json

if [ ! -f $JSON ]; then
        ./lift_test $LITMUS $JSON 2>/dev/null >/dev/null
fi

if [ ! -f $JSON ]; then
        echo $1 Error
        exit 0
fi

ACTUAL=$(./run_test $JSON | grep -oE "(Ok|No|ExecError)")

if [ "$ACTUAL" = "ExecError" ]; then
        echo $1 ExecError
        exit 0
fi 

EXPECTED=$(herd7 $LITMUS | grep -oE "(Ok|No)")

if [ "$EXPECTED" = "$ACTUAL" ]; then
        echo -e "$1 ${GREEN}Ok${NC} (expected $EXPECTED, found $ACTUAL)"
else
        echo -e "$1 ${RED}No${NC} (expected $EXPECTED, found $ACTUAL)"
fi
