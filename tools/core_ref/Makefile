CPP = ../../reference/ghidra/Ghidra/Features/Decompiler/src/decompile/cpp
OBJ = $(CPP)/com_dbg
CXXFLAGS = -g -I$(CPP)
DECOMP_FLAGS = -DCPUI_DEBUG -D__TERMINAL__
CORE_OBJS = $(OBJ)/xml.o $(OBJ)/marshal.o $(OBJ)/space.o $(OBJ)/float.o $(OBJ)/address.o $(OBJ)/pcoderaw.o \
	$(OBJ)/translate.o $(OBJ)/opcodes.o $(OBJ)/globalcontext.o $(OBJ)/crc32.o $(OBJ)/multiprecision.o

SLEIGH_OBJS = $(OBJ)/sleigh.o $(OBJ)/pcodeparse.o $(OBJ)/pcodecompile.o $(OBJ)/sleighbase.o $(OBJ)/slghsymbol.o \
	$(OBJ)/slghpatexpress.o $(OBJ)/slghpattern.o $(OBJ)/semantics.o $(OBJ)/context.o $(OBJ)/slaformat.o \
	$(OBJ)/compression.o $(OBJ)/loadimage.o $(OBJ)/filemanage.o

DECOMP_OBJS = $(filter-out $(OBJ)/consolemain.o $(OBJ)/bfd_arch.o $(OBJ)/loadimage_bfd.o,$(wildcard $(OBJ)/*.o))

all: xml_probe core_probe opbehavior_probe pcodeparse_probe prettyprint_probe printlang_probe grammarlex_probe grammarparse_probe printtypes_probe

xml_probe: xml_probe.cc
	g++ $(CXXFLAGS) $< $(OBJ)/xml.o -o $@

core_probe: core_probe.cc
	g++ $(CXXFLAGS) $< $(CORE_OBJS) -o $@

opbehavior_probe: opbehavior_probe.cc
	g++ $(CXXFLAGS) $< $(CORE_OBJS) $(OBJ)/opbehavior.o -o $@

pcodeparse_probe: pcodeparse_probe.cc
	g++ $(CXXFLAGS) $< $(CORE_OBJS) $(SLEIGH_OBJS) -lz -o $@

prettyprint_probe: prettyprint_probe.cc
	g++ $(CXXFLAGS) $(DECOMP_FLAGS) $< $(DECOMP_OBJS) -lz -o $@

printlang_probe: printlang_probe.cc
	g++ $(CXXFLAGS) $(DECOMP_FLAGS) $< $(DECOMP_OBJS) -lz -o $@

grammarlex_probe: grammarlex_probe.cc
	g++ $(CXXFLAGS) $(DECOMP_FLAGS) $< $(DECOMP_OBJS) -lz -o $@

grammarparse_probe: grammarparse_probe.cc
	g++ $(CXXFLAGS) $(DECOMP_FLAGS) $< $(DECOMP_OBJS) -lz -o $@

printtypes_probe: printtypes_probe.cc
	g++ $(CXXFLAGS) $(DECOMP_FLAGS) $< $(DECOMP_OBJS) -lz -o $@

clean:
	rm -f xml_probe core_probe opbehavior_probe pcodeparse_probe prettyprint_probe printlang_probe grammarlex_probe grammarparse_probe printtypes_probe
