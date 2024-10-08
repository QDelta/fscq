MODULES    := Lock Nomega Word WordAuto WordZ Bytes Rounding \
				Mem AsyncDisk Pred Prog ProgMonad PredCrash Hoare \
				OperationalSemantics \
				Hashmap HashmapProg \
	      SepAuto Idempotent Errno \
	      BasicProg ListUtils MapUtils Array Rec RecArrayUtils \
	      MemPred Cache SyncedMem \
	      FSLayout AsyncRecArray DiskLogHash \
	      LogReplay MemLog ListPred GenSepN FMapMem \
	      NEList DiskSet GroupLog Log LogRecArray \
	      Balloc BlockPtr GenSepAuto Inode BFile BFileCrash \
	      MemMatch FileRecArray \
	      Dir DirName DirCache StringUtils TreeUtils \
	      DirTreePath DirTreeDef DirTreePred DirTreeRep DirTreeSafe \
	      DirTreeNames DirTreeInodes DirTree \
	      TreeCrash \
	      SuperBlock AsyncFS AsyncFSRecover VBConv AByteFile \
	      ADestructPair DestructVarname ExtrHaskellPrelude ExtrHaskellMap \
	      DirSep DirSepCrash ProgMetatheory TreeSeq \
	      AtomicCp BACHelper BytefileSpecs AtomicCpRecover

VS         := $(MODULES:%=%.v)
VS_BUILD   := $(patsubst %.v,coqbuild/%.v,$(VS))
VS_HS      := codegen/AsyncFS.hs
VS_ML      := codegen/AsyncFS.ml
VS_JSON    := codegen/AsyncFS.json
GHC 	   := ghc
HSC2HS	   := hsc2hs
ifeq (,$(shell $(GHC) --version 2>/dev/null | grep 'version 8\.' 2>/dev/null))
	GHC := /opt/ghc/8.0.1/bin/ghc
	HSC2HS := /opt/ghc/8.0.1/bin/hsc2hs
endif

J	   ?= 1
GHC_PACKAGES := bytestring unix integer-gmp ghc-prim containers directory filepath process
GHCARGS    := -j$(J) -O2 -threaded -rtsopts -optl-no-pie $(foreach p,$(GHC_PACKAGES),-package $(p))
		# -ticky -ticky-dyn-thunk -ticky-allocd
		# -prof -fprof-auto
		# -eventlog
HSLIB_FUSE := hscgen/Fuse.hs hslib/libopfuse.a
HSLIB_PRE  := hslib/Word.hs hslib/Evict.hs hslib/Profile.hs
HSLIB_POST := hslib/Disk.hs hslib/Interpreter.hs

COQ_WARNING := -w -omega-is-deprecated,-implicit-core-hint-db,-deprecated-hint-without-locality,-deprecated-grab-existentials,-undeclared-scope
COQEXEC     := coqtop -R . Fscq $(COQ_WARNING) -batch -load-vernac-source

.PHONY: vos vok proof clean

all: fscq mkfs

mlbin/mkfs.exe: mlbin/mkfs.ml $(VS_ML) $(wildcard mllib/*.ml)
	dune build $@

mlbin/fscqfuse.exe: mlbin/fscqfuse.ml $(VS_ML) $(wildcard mllib/*.ml)
	dune build $@

hscgen/%.hs: hslib/%.hsc
	@mkdir -p $(@D)
	$(HSC2HS) $< -o $@ --cflag=-D_FILE_OFFSET_BITS=64 -Ihslib

%: %.hs $(VS_HS) $(HSLIB_PRE) $(HSLIB_POST) $(HSLIB_FUSE) fiximports.py
	test ! -f codegen/Word.hs || mv codegen/Word.hs codegen/.Word.hs
	$(GHC) $(GHCARGS) $(HSLIB_FUSE)
	$(GHC) $(GHCARGS) -Wall $(HSLIB_PRE)
	$(GHC) $(GHCARGS) -F -pgmF ./fiximports.py codegen/*.hs -ihslib
	$(GHC) $(GHCARGS) -F -pgmF ./fiximports.py -Wall $(HSLIB_POST) -ihslib -icodegen
	$(GHC) $(GHCARGS) -F -pgmF ./fiximports.py -Wall $< -ihslib -icodegen -ihscgen -optl -lfuse -lopfuse -Lhslib -o $@

$(VS_HS): vos coqbuild/ExtractHaskell.v
	( cd coqbuild && $(COQEXEC) ExtractHaskell.v )

$(VS_ML): vos coqbuild/ExtractOcaml.v
	( cd coqbuild && $(COQEXEC) ExtractOcaml.v )
	mv codegen/Word.ml codegen/.WordCoq.ml
	mv codegen/Word.mli codegen/.WordCoq.mli

$(VS_JSON): vos coqbuild/ExtractJSON.v
	( cd coqbuild && $(COQEXEC) ExtractJSON.v )

vos: coqbuild/Makefile.coq
	( cd coqbuild && $(MAKE) -j $(J) -f Makefile.coq vos )

vok: coqbuild/Makefile.coq
	( cd coqbuild && $(MAKE) -j $(J) -f Makefile.coq vok )

proof: coqbuild/Makefile.coq
	( cd coqbuild && $(MAKE) -j $(J) -f Makefile.coq )

coqbuild/%.v: %.v
	@mkdir -p coqbuild
	ln -s ../$< $@

coqbuild/Makefile.coq: Makefile $(VS_BUILD)
	@mkdir -p codegen
	@mkdir -p coqbuild
	@ln -sf ../coqbuild codegen
	( cd coqbuild && coq_makefile -R . Fscq -arg "$(COQ_WARNING)" $(VS) -o Makefile.coq )

%/main.go: %.json coq2go.py
	@mkdir -p $(@D)
	./coq2go.py $< > $(patsubst %/main.go,%/temp.go,$@)
	go fmt $(patsubst %/main.go,%/temp.go,$@)
	mv $(patsubst %/main.go,%/temp.go,$@) $@

gotest: $(patsubst %.json,%/main.go,$(wildcard codegen/*.json))
	GOPATH=$(shell cd .. && pwd):${GOPATH} go build gotest.go

hslib/%.o: hslib/%.c
	$(CC) $^ -c -o $@ -O2 -Wall -Werror -D_FILE_OFFSET_BITS=64

hslib/libopfuse.a: hslib/opqueue.o hslib/opfuse.o
	ar rcs $@ $^

clean:
	rm -rf codegen coqbuild _build fstest hstest gotest disk.img \
	       fscq mkfs *.o *.hi \
	       hslib/*.o hscgen \
	       mlbin/*.exe

.PRECIOUS: hscgen/%.hs %_stubs.c
