#!/bin/bash

for iso in `cat isolates.txt`; do ivy_check isolate=$iso SCP.ivy; done
