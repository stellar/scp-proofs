executable: network.ivy node.ivy sort.ivy assertion.ivy executable.ivy
	ivy_to_cpp target=repl isolate=executable_runner executable.ivy
	g++ -O2 executable.cpp -pthread -lpthread -o executable

fuzz: network.ivy node.ivy sort.ivy assertion.ivy fuzz.ivy
	ivyc target=test isolate=fuzz_runner classname=fuzz fuzz.ivy

proof: network.ivy node.ivy sort.ivy assertion.ivy proof.ivy
	ivy_check trace=true proof.ivy

clean:
	rm -f fuzz fuzz.h fuzz.cpp executable executable.h executable.cpp
