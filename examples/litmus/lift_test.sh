#!/bin/bash

LITMUS=${1}.litmus
JSON=${1}.json

if [ ! -f $JSON ]; then
        ./lift_test $LITMUS $JSON 2>/dev/null >/dev/null
fi
