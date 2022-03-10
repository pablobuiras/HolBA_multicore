#!/bin/bash

LITMUS=${1}.litmus
JSON=${1}.json

if [ ! -f $JSON ]; then
        ./lift_test $LITMUS $JSON
fi
