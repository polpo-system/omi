MODULE slim;  (** slim.Compile file.Mod: compile a module to a slim binary in obj/slim/ *)

(* A slim binary (Oberon Module Interchange, M. Franz and T. Kistler) holds no machine code: its
   symbol table and its syntax tree, compressed by the dictionary of the encoder (OPOPV). The front
   end is polpo's x86 compiler (OPP, OPB, OPT, OPM); the interfaces of imports come from obj/slim/,
   else from obj/x86/ (the same front end writes them, with the same fingerprints). *)

IMPORT OPP, OPB, OPT, OPS, OPM, OPOPV, Root, Texts := texts, Oberon := Oberon0, Out := out;

CONST
  module = OPS.module; ident = OPS.ident;

PROCEDURE Reset;  (* the x86 compiler shares OPM: leave it as it found it *)
BEGIN OPM.slim := FALSE; OPM.symPath := ""; OPM.outputPath := "!"; OPM.outputPrefix := "!"
END Reset;

PROCEDURE Options(VAR options: ARRAY OF CHAR; VAR codeOpt, parserOpt: SET);
VAR i: LONGINT; ch: CHAR;
BEGIN
  codeOpt := OPM.DefaultCodeOpt; parserOpt := OPM.DefaultParserOpt; i := 0;
  LOOP
    ch := options[i]; INC(i);
    IF ch = 0X THEN EXIT
    ELSIF ch = "x" THEN codeOpt := codeOpt / {OPM.inxchk}
    ELSIF ch = "v" THEN codeOpt := codeOpt / {OPM.ovflchk}
    ELSIF ch = "t" THEN codeOpt := codeOpt / {OPM.typchk}
    ELSIF ch = "a" THEN codeOpt := codeOpt / {OPM.assert}
    ELSIF ch = "s" THEN parserOpt := parserOpt / {OPM.newsf}
    ELSIF ch = "e" THEN parserOpt := parserOpt / {OPM.extsf}
    ELSIF ch = "w" THEN parserOpt := parserOpt / {OPM.warning}
    ELSIF ch = "2" THEN parserOpt := parserOpt / {OPM.oberon2}
    END
  END
END Options;

PROCEDURE Name(source: Texts.Reader);  (* the module name, for the message *)
VAR sym: SHORTINT;
BEGIN
  OPM.Init({}, {}, source, Oberon.Log); OPS.Get(sym);
  IF sym = module THEN OPS.Get(sym);
    IF sym = ident THEN OPS.Get(sym); Out.String(" compiling "); Out.String(OPM.outputPath); Out.String(OPS.name) END
  END
END Name;

PROCEDURE Module(source: Texts.Reader; options: ARRAY OF CHAR; VAR error: BOOLEAN);
VAR codeOpt, parserOpt: SET; newSF, extSF: BOOLEAN; p: OPT.Node; modName: OPS.Name; R: Texts.Reader;
BEGIN
  Options(options, codeOpt, parserOpt);
  Root.Obj("slim", OPM.outputPath); OPM.outputPrefix := ""; COPY(".Obj", OPM.extension);
  Root.Obj("x86", OPM.symPath);
  R := source; Name(R);
  OPM.Init(codeOpt, parserOpt, source, Oberon.Log); OPS.ch := " ";
  OPB.typSize := OPOPV.NoTypSize;  (* sizes are decided when the module is loaded: no SIZE(T) of a composite T *)
  newSF := OPM.newsf IN parserOpt; extSF := OPM.extsf IN parserOpt;
  OPP.Module(p, modName);
  IF OPM.noerr THEN
    OPM.errpos := 0; OPM.slim := TRUE; OPM.Begin(modName);
    IF OPM.noerr THEN
      OPT.Export(modName, newSF, extSF);
      IF newSF THEN Out.String(" new symbol file") ELSIF extSF THEN Out.String(" extended symbol file") END;
      IF OPM.noerr THEN OPM.errpos := 0; OPOPV.Module(p) END
    END
  END;
  OPT.CloseScope; OPT.Close;
  Out.Ln; error := ~OPM.noerr;
  Reset
END Module;

PROCEDURE CompileFile(name, options: ARRAY OF CHAR; VAR error: BOOLEAN);
VAR t: Texts.Text; r: Texts.Reader;
BEGIN
  NEW(t); Texts.Open(t, name);
  IF t.len # 0 THEN
    Texts.OpenReader(r, t, 0); Out.String(name); OPS.Init; Module(r, options, error)
  ELSE Out.String(name); Out.String(" not found"); Out.Ln; error := TRUE
  END
END CompileFile;

PROCEDURE Help*;
BEGIN
  Out.String("slim: slim binaries (Oberon Module Interchange) of polpo modules"); Out.Ln; Out.Ln;
  Out.String("  slim.Compile [options] file.Mod ...   a slim binary obj/slim/Name.Obj and its obj/slim/Name.Sym"); Out.Ln;
  Out.String("    /s new symbol file   /e extended symbol file   /2 Oberon-2"); Out.Ln;
  Out.String("    /x /v /t /a          index, overflow, type checks and ASSERT off"); Out.Ln; Out.Ln;
  Out.String("  A slim binary holds the syntax tree of the module, not machine code. SYSTEM operations,"); Out.Ln;
  Out.String("  inline assembler and code procedures cannot be written in one yet (error 505), nor"); Out.Ln;
  Out.String("  SIZE of a record or array (error 501): sizes are known only on the machine that loads it."); Out.Ln
END Help;

PROCEDURE Compile*;
VAR S: Texts.Scanner; name, opt: ARRAY 64 OF CHAR; error: BOOLEAN; i, j: INTEGER;
BEGIN
  error := FALSE; opt[0] := 0X;
  Texts.OpenScanner(S, Oberon.Par.text, Oberon.Par.pos); Texts.Scan(S);
  IF S.class = Texts.Inval THEN Out.String("usage: slim.Compile [options] file.Mod ... (slim.Help)"); Out.Ln; RETURN END;
  WHILE (S.class # Texts.Inval) & ~error DO
    IF S.class = Texts.Name THEN
      COPY(S.s, name);
      IF (name[0] = "/") OR (name[0] = "\") THEN
        j := 0; WHILE opt[j] # 0X DO INC(j) END;
        i := 1; WHILE name[i] # 0X DO opt[j] := name[i]; INC(i); INC(j) END; opt[j] := 0X
      ELSE CompileFile(name, opt, error)
      END
    END;
    Texts.Scan(S)
  END
END Compile;

BEGIN
  Oberon.OnStop(Reset)
END slim.
