# This has to be a path to a checked-out, configured and _built_ stellar-core
# source tree.
CORE=$(HOME)/src/stellar-core
IVY=$(HOME)/src/ivy

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
          $(CORE)/src/util/RandHasher.o \
          $(CORE)/src/util/Scheduler.o \
          $(CORE)/src/util/Timer.o \
          $(CORE)/src/util/numeric.o \
          $(CORE)/src/util/types.o

CORE_LIBDIRS=-L $(CORE)/lib \
             -L $(CORE)/lib/xdrpp/xdrpp/ \
             -L $(CORE)/lib/libsodium/src/libsodium/.libs

CORE_INCLUDES=-I $(CORE) \
              -I $(CORE)/src \
              -I $(CORE)/lib/xdrpp \
              -I $(CORE)/lib/fmt/include \
              -I $(CORE)/lib/spdlog/include

# use Ivy's version of z3
IVY_INCDIR=$(IVY)/ivy/include
IVY_LIBDIR=$(IVY)/ivy/lib

executable: $(CORE_OBJS) executable.o
	@echo "\n\ndon't forget to build stellar core with --disable-tests\n\n"
	clang++ -g -o $@ $^ $(CORE_LIBDIRS) -L $(IVY_LIBDIR) -lpthread -lsodium -l3rdparty -lxdrpp -lz3 -Wl,-rpath,$(IVY_LIBDIR) -o executable
	@echo "\n\ndon't forget to export LD_LIBRARY_PATH=$(IVY_LIBDIR)\n\n"

executable.o: executable.cpp executable.h Makefile
	clang++ -c -O2 -g -std=c++17 -pthread $(CORE_INCLUDES) -I $(IVY_INCDIR) -o $@ $<

executable.cpp executable.h: executable.ivy Makefile
	ivy_to_cpp target=test isolate=executable_runner build=false $<

clean:
	rm -f executable.o executable.cpp executable.h

.PHONY: clean
