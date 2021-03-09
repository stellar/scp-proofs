# This does not work due to https://github.com/kenmcmil/ivy/issues/16
all: network.ivy node.ivy sort.ivy assertion.ivy executable.ivy
	ivy_to_cpp target=repl isolate=executable_runner executable.ivy
	g++ -O2 executable.cpp -pthread -lpthread -o executable

# This does not work due to https://github.com/kenmcmil/ivy/issues/16
fuzz: network.ivy node.ivy sort.ivy assertion.ivy fuzz.ivy
	ivyc target=test isolate=fuzz_runner classname=fuzz fuzz.ivy

# the proof goes much faster with complete=qf
proof: network.ivy node.ivy sort.ivy assertion.ivy proof.ivy
	ivy_check complete=qf trace=true proof.ivy

format: member.py
	autopep8 -i member.py
