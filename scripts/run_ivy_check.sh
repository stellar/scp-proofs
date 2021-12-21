#!/bin/bash

cd ~/ivy
git fetch -q
git checkout -q f0a63852a8bb960a8bb52aace1902263ed84fd33 # known to work with this version of Ivy
cd ~/scp-proofs/
ivy_check complete=fo $1
