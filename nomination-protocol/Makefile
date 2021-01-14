all: nomination.ivy node.ivy set.ivy network.ivy
	ivy_to_cpp target=repl isolate=runner nomination.ivy
	g++ -O2 nomination.cpp -pthread -lpthread -o nomination
