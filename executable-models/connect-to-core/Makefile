# This has to be a path to a checked-out, configured and _built_ stellar-core
# source tree.
CORE=$(HOME)/src/stellar-core

CORE_OBJS=$(CORE)/src/crypto/BLAKE2.o \
          $(CORE)/src/crypto/Hex.o \
          $(CORE)/src/crypto/KeyUtils.o \
          $(CORE)/src/crypto/Random.o \
          $(CORE)/src/crypto/SecretKey.o \
          $(CORE)/src/crypto/ShortHash.o \
          $(CORE)/src/crypto/SHA.o \
          $(CORE)/src/crypto/StrKey.o \
          $(CORE)/src/scp/BallotProtocol.o \
          $(CORE)/src/scp/LocalNode.o \
          $(CORE)/src/scp/NominationProtocol.o \
          $(CORE)/src/scp/QuorumSetUtils.o \
          $(CORE)/src/scp/SCP.o \
          $(CORE)/src/scp/SCPDriver.o \
          $(CORE)/src/scp/Slot.o \
          $(CORE)/src/util/Backtrace.o \
          $(CORE)/src/util/GlobalChecks.o \
          $(CORE)/src/util/HashOfHash.o \
          $(CORE)/src/util/Logging.o \
          $(CORE)/src/util/Math.o \
          $(CORE)/src/util/Scheduler.o \
          $(CORE)/src/util/Timer.o \
          $(CORE)/src/util/numeric.o \
          $(CORE)/src/util/types.o \

CORE_LIBDIRS=-L $(CORE)/lib \
             -L $(CORE)/lib/xdrpp/xdrpp/ \
             -L $(CORE)/lib/libsodium/src/libsodium/.libs

CORE_INCLUDES=-I $(CORE) \
              -I $(CORE)/src \
              -I $(CORE)/lib/xdrpp \
              -I $(CORE)/lib/fmt/include

executable: $(CORE_OBJS) executable.o
	clang++ -g -o $@ $^ $(CORE_LIBDIRS) -lpthread -lsodium -l3rdparty -lxdrpp -lz3 -o executable

executable.o: executable.cpp executable.h Makefile
	clang++ -c -g -std=c++17 -pthread $(CORE_INCLUDES) -o $@ $<

executable.cpp executable.h: executable.ivy Makefile
	ivy_to_cpp target=test isolate=executable_runner build=false $<