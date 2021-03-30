# TODO: Fix the executable and fuzz models.
# Tldr: The fuzzing and executable do not work due to some
#       strange technical details that occur ONLY IF
#       * We hardcode nodes, AND
#       * The number of nodes is not a power of 2.
#         (In this case, we have 3 nodes.)
#
# Longer explanation:
#
# These compile and run, but fail for the same reason.
# Since 3 is not a power of 2, we can't use bit-vector interpretations.
# When Ivy converts fuzzing into C++, init_gen::generate in fuzz.cpp
# assigns a random value to v1, v2, and v3.
# But in order for federated voting to work correctly,
# those values must be distinct.
#
# They are guaranteed to be distinct in the proof
# since proof.ivy contains axioms such as `axiom v0 ~= v2`.
# which doesn't seem to work with fuzzing unfortunately.
#
# fuzz: network.ivy node.ivy sort.ivy assertion.ivy fuzz.ivy
# 	ivyc target=test isolate=fuzz_runner classname=fuzz fuzz.ivy
#
# all: network.ivy node.ivy sort.ivy assertion.ivy executable.ivy
# 	ivy_to_cpp target=repl isolate=executable_runner executable.ivy
# 	g++ -O2 executable.cpp -pthread -lpthread -o executable

# the proof goes much faster with complete=qf
proof: network.ivy node.ivy sort.ivy assertion.ivy proof.ivy
	ivy_check complete=qf trace=true proof.ivy

format: relation.py
	autopep8 -i relation.py
