# omi: slim binaries for polpo

A slim binary holds no machine code. It holds the symbol table of a module and its syntax tree,
compressed by a dictionary of the nodes seen before, and the machine code is made from it on the
machine that uses the module. The technique is Michael Franz's (ETH Zurich, 1994: *Code-Generation
On-the-Fly: A Key to Portable Software*); with Thomas Kistler (UC Irvine) it became the Oberon
Module Interchange (OMI) of MacOberon, where one object file ran on 68k and PowerPC Macintoshes
and the module loader generated the code when it loaded the module.

This package brings it back for polpo, as one more kind of object next to the native ones of its
ports (x86, ARM, ARMv7, RISC-V, MIPS), which stay.

## What is here

    mac/            the OMI sources of MacOberon R2.32 (Src.Arc, 2000), unchanged but for plain text
    src/OPOPV.Mod   the encoder, polpo's version of mac/PPC.OPOPV.Mod
    src/OPOPD.Mod   the decoder: a slim binary back into the objects and the tree of polpo's compiler
    src/SlimLoad.Mod a slim binary compiled to native code: into memory for the module loader, or to obj/x86
    src/slim.Mod    the commands
    test/           SlimTest (the language) and SlimSysTest (SYSTEM)

The history of `src/OPOPV.Mod` starts with the mac's encoder unchanged; each change for polpo is
a commit of its own.

## Using it

    slim.Compile [/s /2 ...] X.Mod   X.Mod to the slim binary obj/slim/X.Obj (and obj/slim/X.Sym)
    X.Run                            loads X: compiled into memory from obj/slim/X.Obj
    slim.Build X                     obj/slim/X.Obj to a native obj/x86/X.Obj, if wanted
    SlimLoad.Verbose                 report each module compiled into memory
    slim.Help

A module with a slim binary and no native object is compiled when it is loaded, as on the mac:
polpo's module loader (Modules0) meets obj/slim/X.Obj, loads the module SlimLoad the first time,
and SlimLoad decodes the slim binary into what polpo's parser makes of the source and compiles that
with the x86 back end into an object that stays in memory; the loader loads it from there and
nothing is written. The nearest comes first: the native object of the current directory, its slim
binary, then the same in the root. `slim.Build` writes the native object instead, a cache that
the loader then takes. The interfaces of imports come from obj/slim, else from obj/x86.

## The format

A slim binary is an object file with the tag of a portable object (BB 88). Then, as on the mac:

  * a symbol part, as in a .Sym file: the imports and the interface of the module;
  * three numbers: the start of the use section and the sizes of the dictionary;
  * the other imports, and a second stream: the rest of the module's scope, the use section (each
    object used from an import, with its fingerprint; a constant's value and a record's layout are
    in their fingerprints) and the code;
  * the code is the tree in prefix order. Each node is a tag (a new node) or the number of a node
    of the dictionary, complete (an equal subtree written before) or partial (the same operator
    and some operands: the rest follows). Global nodes count up from after the last tag, those of
    a procedure count down from -1 and are dropped when the procedure ends. The local scope of a
    procedure is written where its body starts.

polpo's changes to the format of the mac:

  * SYSTEM: the tags 36H to 40H (ADR, BIT, LSH, ROT, GET8..GET32, GET, PUT, NEW, MOVE) and a
    partial node per type for SYSTEM.VAL (the basic types, BYTE, PTR and every type of the module
    and of the imports used). The x86-only operations (GETREG, PUTREG, CC, PORTIN, PORTOUT, STI,
    CLI), inline assembler and code procedures are refused (error 505).
  * Tags are written with WriteNum like the other numbers (from 40H a single byte would be read as
    negative), and the global node numbers start after 40H.
  * The forms of polpo's compiler (four kinds of arrays), its WITH (the variable of a branch) and
    its hidden records.

Numbers are written with WriteNum and do not depend on the byte order. REAL and LONGREAL
constants are written as polpo's Files writes them, little endian on all of polpo's ports; a
decoder on a big endian machine has to turn them round. Code that reads memory byte for byte
with SYSTEM stays bound to the byte order it was written for.

Slim binaries are 32 bit: the front end folds SIZE of basic types and MAX(LONGINT) as on polpo's
ports, and the fingerprints of records use the x86 layout.

## Native modules below, slim modules above

As MacOberon kept its toolbox interface (TB) native for each processor, the modules below
the portable line stay native on each port: Kernel, Linux0 (the system calls), the loader. A slim
module may import them, and the use section binds it to the objects it uses: on a port whose
Linux0 differs in an object used (a constant, the layout of a record), slim.Build refuses it.

## Tests

    slim.Compile /2 SlimTest.Mod; slim.Build SlimTest; SlimTest.Run       22 checks
    slim.Compile SlimSysTest.Mod; slim.Build SlimSysTest; SlimSysTest.Run  19 checks

Both give the output of the native compile, with the same size of code. polpo's TLS library (35
modules: RSA, ECDSA, X25519, AES-GCM, SHA-2, X.509, TLS 1.3 client and server) built through slim
passes its 34 test modules with the output of the native one.

Loaded into memory: SlimTest runs from its slim binary alone, and with the whole TLS library
only as slim binaries the 34 test modules pass; compiling the 14 modules TLSTestServer loads costs
about 36 ms (0.154 s against 0.118 s native).

SlimMethTest (type-bound procedures, a super call; 5 checks, /2) passes as well.

Not yet: operators, object bodies of Active Oberon; code generation for the other ports, and an
interpreter for processors polpo has no compiler for.

The license is GPL-3 (`LICENSE`); the code comes from ETH Oberon, whose license (`LICENSE.ETH`)
asks to keep its copyright notice and conditions, which `LICENSE.ETH` does.
