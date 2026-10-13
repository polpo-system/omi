MODULE SlimLoad;  (** a slim binary compiled to native code: into memory for the module loader, or to obj/x86 *)

(* As MacOberon's loader did with Interchange, polpo's module loader (Modules0) compiles the slim binary
   of a module that has no native object when it loads it: Modules0.slim, installed by this module's
   body, decodes obj/slim/name.Obj (OPOPD) and compiles it with the x86 back end into an object that
   stays in memory (OPM.toMemory); the loader loads that one, nothing is written. Modules0 loads this
   module itself the first time it meets a slim binary. slim.Build uses the same code to write the
   native object to obj/x86, the cache of a slim module. *)

IMPORT Files, OPB, OPT, OPS, OPM, OPV, OPC, OPL, OPO, OPOPD, Modules0, Root, Texts := texts, Oberon := Oberon0, Out := out;

VAR verbose*: BOOLEAN;  (** report each module compiled into memory *)

PROCEDURE Append(VAR s: ARRAY OF CHAR; t: ARRAY OF CHAR);
VAR i, j: INTEGER;
BEGIN i := 0; WHILE s[i] # 0X DO INC(i) END; j := 0;
  WHILE (t[j] # 0X) & (i < LEN(s)-1) DO s[i] := t[j]; INC(i); INC(j) END; s[i] := 0X
END Append;

PROCEDURE ShowErrors;  (* the error messages are in Oberon.Log, as with compiler.Compile *)
VAR R: Texts.Reader; ch: CHAR;
BEGIN
  Texts.OpenReader(R, Oberon.Log, 0); Texts.Read(R, ch);
  WHILE ~R.eot DO Out.Char(ch); Texts.Read(R, ch) END
END ShowErrors;

PROCEDURE Reset*;  (** the x86 compiler shares OPM: leave it as found *)
BEGIN OPM.slim := FALSE; OPM.toMemory := FALSE; OPM.symPath := ""; OPM.outputPath := "!"; OPM.outputPrefix := "!"
END Reset;

(** Compile obj/slim/name.Obj to native code: into memory (the result) if memory, else to obj/x86/name.Obj;
   size: the size of the code, -1 after an error (the messages are written out) *)
PROCEDURE Compile*(name: ARRAY OF CHAR; memory: BOOLEAN; VAR size: LONGINT): Files.File;
VAR F, obj: Files.File; fname: ARRAY 256 OF CHAR; t: Texts.Text; r: Texts.Reader; p: OPT.Node; modName: OPS.Name;
  newSF, extSF: BOOLEAN;
BEGIN
  size := -1; obj := NIL;
  Root.Obj("slim", fname); Append(fname, name); Append(fname, ".Obj");
  F := Files.Old(fname);
  IF F = NIL THEN RETURN NIL END;
  Root.Obj("x86", OPM.outputPath); OPM.outputPrefix := ""; COPY(".Obj", OPM.extension);
  Root.Obj("slim", OPM.symPath); OPM.toMemory := memory;
  NEW(t); Texts.Open(t, ""); Texts.OpenReader(r, t, 0);
  OPM.Init(OPM.DefaultCodeOpt, OPM.DefaultParserOpt + {OPM.newsf}, r, Oberon.Log);
  OPB.typSize := OPV.TypSize; OPV.Init(-1);
  COPY(name, modName); OPOPD.Module(F, modName, p);
  IF OPM.noerr THEN
    OPL.Init; OPM.errpos := 0; OPM.Begin(modName);
    IF OPM.noerr THEN
      newSF := TRUE; extSF := FALSE;
      OPT.Export(modName, newSF, extSF); OPV.AdrAndSize(OPT.topScope);
      IF OPM.noerr THEN
        OPM.errpos := 0; OPC.Init; OPV.Module(p);
        IF OPM.noerr THEN OPL.OutCode(modName) END
      END;
      OPL.Close
    END
  END;
  OPT.CloseScope; OPT.Close;
  IF OPM.noerr THEN size := OPO.pc; IF memory THEN obj := OPM.memFile END
  ELSE Out.String(fname); Out.String(": "); ShowErrors; Out.Ln
  END;
  OPM.memFile := NIL; Reset;
  RETURN obj
END Compile;

PROCEDURE *Load(name: ARRAY OF CHAR): Files.File;  (* Modules0.slim *)
VAR f: Files.File; size: LONGINT;
BEGIN
  f := Compile(name, TRUE, size);
  IF verbose & (f # NIL) THEN Out.String("SlimLoad: "); Out.String(name); Out.String(" compiled into memory, ");
    Out.Int(size, 0); Out.String(" bytes of code"); Out.Ln
  END;
  RETURN f
END Load;

PROCEDURE Verbose*;  (** SlimLoad.Verbose: report the modules compiled into memory *)
BEGIN verbose := TRUE
END Verbose;

BEGIN
  verbose := FALSE; Modules0.slim := Load; Oberon.OnStop(Reset)
END SlimLoad.
