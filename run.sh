#!/bin/sh

if [ $# -eq 0 ]; then
    gradle run
else
    gradle run --args="../$*"
fi
