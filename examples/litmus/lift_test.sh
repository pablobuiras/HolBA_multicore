#!/bin/bash

LITMUS=${1}.litmus
JSON=${1}.json

if [ -f $JSON ]; then
        echo "${1}: Skipping."
        exit 1
fi
if [ ! -f $LITMUS ]; then
        echo "${1}: Missing litmus file."
        exit 2
fi
./lift_test $LITMUS $JSON >/dev/null 2>&1

if [ -f $JSON ]; then
        echo "${1}: Lifted."
else
        echo "${1}: Lift failed."
        exit 3
fi
