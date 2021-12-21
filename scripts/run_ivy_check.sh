#!/bin/bash

cd ~/ivy
git fetch -q
git checkout -q c740b2742508beb6d8e22fbab2f13babf117db8f # does not work with most recent master
cd ~/scp-proofs/
ivy_check complete=fo $1
