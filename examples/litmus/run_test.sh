#!/bin/bash

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
        echo $1 Ok
else
        echo $1 No
fi
