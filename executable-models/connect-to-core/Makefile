# This has to be a path to a checked-out, configured and _built_ stellar-core
# source tree.

# Use $(HOME)/src/stellar-core, $(HOME)/src/ivy
# as the default locations of stellar-core and ivy.
# If you use different locations, use `env` to overwrite it.
# e.g., `env CORE_DIR=~/stellar-core IVY_DIR=~/ivy make executable`.
CORE_DIR?=$(HOME)/src/stellar-core
IVY_DIR?=$(HOME)/src/ivy

CORE_OBJS=$(CORE_DIR)/src/crypto/BLAKE2.o \
          $(CORE_DIR)/src/crypto/Hex.o \
          $(CORE_DIR)/src/crypto/KeyUtils.o \
          $(CORE_DIR)/src/crypto/Random.o \
          $(CORE_DIR)/src/crypto/SecretKey.o \
          $(CORE_DIR)/src/crypto/ShortHash.o \
          $(CORE_DIR)/src/crypto/SHA.o \
          $(CORE_DIR)/src/crypto/StrKey.o \
          $(CORE_DIR)/src/scp/BallotProtocol.o \
          $(CORE_DIR)/src/scp/LocalNode.o \
          $(CORE_DIR)/src/scp/NominationProtocol.o \
          $(CORE_DIR)/src/scp/QuorumSetUtils.o \
          $(CORE_DIR)/src/scp/SCP.o \
          $(CORE_DIR)/src/scp/SCPDriver.o \
          $(CORE_DIR)/src/scp/Slot.o \
          $(CORE_DIR)/src/util/Backtrace.o \
          $(CORE_DIR)/src/util/GlobalChecks.o \
          $(CORE_DIR)/src/util/HashOfHash.o \
          $(CORE_DIR)/src/util/Logging.o \
          $(CORE_DIR)/src/util/Math.o \
          $(CORE_DIR)/src/util/RandHasher.o \
          $(CORE_DIR)/src/util/ProtocolVersion.o \
          $(CORE_DIR)/src/util/Scheduler.o \
          $(CORE_DIR)/src/util/Timer.o \
          $(CORE_DIR)/src/util/numeric.o \
          $(CORE_DIR)/src/util/types.o

CORE_LIBDIRS=-L $(CORE_DIR)/lib \
             -L $(CORE_DIR)/lib/xdrpp/xdrpp/ \
             -L $(CORE_DIR)/lib/libsodium/src/libsodium/.libs

CORE_INCLUDES=-I $(CORE_DIR) \
              -I $(CORE_DIR)/src \
              -I $(CORE_DIR)/lib/xdrpp \
              -I $(CORE_DIR)/lib/fmt/include \
              -I $(CORE_DIR)/lib/libsodium/src/libsodium/include \
              -I $(CORE_DIR)/lib/spdlog/include

# use Ivy's version of z3
IVY_INCDIR=$(IVY_DIR)/ivy/include
IVY_LIBDIR=$(IVY_DIR)/ivy/lib

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
