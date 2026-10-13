(* ETH Oberon, Copyright 2000 ETH Zürich Institut für Computersysteme, ETH Zentrum, CH-8092 Zürich.
Refer to the general ETH Oberon System license contract available at: http://www.oberon.ethz.ch/ *)

MODULE Compiler;  (* RC 6.3.89 / 16.10.92, mmb 19.2.93 / 31.5.94 / tk object model  12.12.95 *)
(* 94-05-24 OptionChar changed *) (* MAH 20.7.94 Debugger interface*)

  IMPORT
    Kernel,FileDir, Files, Modules, Oberon, Texts,
    OPP := OOPP, OPB := OOPB, OPV := OOPV, OPT := OOPT,
    OPS := OOPS, OPC := OOPC, OPL := OOPL,
    OPM := OOPM, POPV:=OPOPV;

  CONST
    (* compiler options: *)
    inxchk = 0; (* x - index check on *)
    ovflchk = 1;  (* v - overflow check on *)
    nilchk = 2; (* n - nil pointer checks on read accesses *)
    ranchk = 3; (* r- range check on *)
    typchk = 4; (* t - type check on *)
    ptrinit = 5;  (* p - pointer initialization *)
    assert = 6; (* a - assert evaluation *)

    dbginfo = 8;
    findpc = 9; (* f - find text position of breakpc *)
    newsf = 10; (* s- generation of new symbol file allowed *)
    extsf =11;  (* e - generation of extended symbol file allowed *)
    warning = 12; (* w - display warnings *)
    update = 13;  (* u - compile only if necessary *)
    portable = 17;
    powerpc = 25; (* c - use PowerPC instruction set *)
    DefOpt = {inxchk, ovflchk, ranchk, typchk, nilchk, ptrinit, assert, powerpc, portable}; (* default options *)
    MakeName = "OOPU";

    module = 63; ident = 38;  (* symbols *)

  VAR
    W: Texts.Writer;

    (* global because of the GC call *)
      SourceCoder: BOOLEAN;
    source: Texts.Text;
    sourceR: Texts.Reader;
    S: Texts.Scanner;
    dpath: FileDir.FileName;
    make*: RECORD (** non-portable *)
      Init*: PROCEDURE;
      Actualize*: PROCEDURE (name: ARRAY OF CHAR; log: Texts.Text): BOOLEAN;
    END;

  PROCEDURE Init;
    VAR m: Modules.Module;
  BEGIN
    m := Modules.ThisMod(MakeName);
    Texts.WriteString(W, "Oberon Portable Compiler / nw & rc & gs -1"); Texts.WriteLn(W);
    Texts.WriteString(W, "PowerPC Code Generator  / mb & tk 9.7.96"); Texts.WriteLn(W);
    Texts.Append(Oberon.Log, W.buf)
  END Init;

  PROCEDURE WriteMsg(source: Texts.Reader; log: Texts.Text);
    VAR sym: SHORTINT;
  BEGIN
    Texts.WriteString(W, " compiling ");
    OPM.Init({}, source, log); OPS.Get(sym);
    IF sym = module THEN
      OPS.Get(sym);
      IF sym = ident THEN
        IF OPM.outputPath # "" THEN
          Texts.WriteString(W, OPM.outputPath); Texts.Write(W, FileDir.PathChar)
        END;
        OPS.Get(sym); Texts.WriteString(W, OPS.name);Texts.WriteString(W, '.Obj');
      (*! IF Modules.FindMod(OPS.name) # NIL THEN Texts.WriteString(W, " (in use) ") END*)
      END
    END;
    Texts.Append(log, W.buf)
  END WriteMsg;

  PROCEDURE Module* (source: Texts.Reader; opt: ARRAY OF CHAR; breakpc: LONGINT; log: Texts.Text; VAR error: BOOLEAN);
    VAR
      extSF, newSF: BOOLEAN; options: SET;
      p: OPT.Node; modName: OPS.Name; i: INTEGER; ch: CHAR;
      m: Modules.Module;
  BEGIN
    OPS.Init(); WriteMsg(source, log);
    options:=DefOpt; i:=0;
    REPEAT  ch:=opt[i]; INC(i);
      IF ch = "x" THEN options := options / {inxchk}
      ELSIF ch = "v" THEN options := options / {ovflchk}
      ELSIF ch = "c" THEN options := options / {ranchk}
      ELSIF ch = "t" THEN options := options / {typchk}
      ELSIF ch = "s" THEN options := options / {newsf}
      ELSIF ch = "p" THEN options := options / {ptrinit}
      ELSIF ch = "n" THEN options := options / {nilchk}
      ELSIF ch = "a" THEN options := options / {assert}
      ELSIF ch = "f" THEN options := options / {findpc}; options := options - {portable}
      (* ELSIF ch = "c" THEN options := options / {powerpc} *)
      ELSIF ch = "e" THEN options := options / {extsf}
      ELSIF ch = "w" THEN options := options / {warning}
      ELSIF ch = "u" THEN options := options / {update}
      ELSIF ch = "d" THEN options := options / {dbginfo}
      ELSIF ch = "P" THEN options := options + {portable}
      ELSIF ch = "N" THEN options := options - {portable}
      END
    UNTIL ch=0X;
    OPM.Init(options, source, log);
    IF portable IN options THEN OPB.typSize:=POPV.NoTypSize ELSE OPB.typSize := OPV.TypSize END;
    newSF := newsf IN options; extSF := extsf IN options;
    OPP.Module(p, modName, options);
    IF  OPM.noerr THEN  OPM.Begin(modName);
      IF ~(portable IN options) THEN OPL.Init(options); OPV.Init(options, breakpc) END;
      OPM.errpos:=0;
      OPT.Export(modName, newSF, extSF);
      IF newSF THEN OPM.LogWStr(" new symbol file")
      ELSIF extSF THEN OPM.LogWStr(" extended symbol file")
      END;
      IF portable IN options THEN
        OPM.errpos := 0;
        IF OPM.noerr THEN POPV.Module(p) END
      ELSE
        OPV.AdrAndSize(OPT.topScope);
        IF OPM.noerr THEN
          OPM.errpos := 0;
          OPC.Init(options);
          OPV.Module(p);
          IF OPM.noerr THEN
            OPL.OutCode(modName);
             END
        END;
        OPL.Close
      END;
      IF OPM.noerr THEN
  m := Modules.modList;
  WHILE (m # NIL) & (m.name # modName) DO m := m.link END;
  IF m # NIL THEN
    OPM.LogWStr(" (in use) ")
  END
END

    END ;
    OPT.CloseScope; OPT.Close;
    OPM.LogWLn; error := ~OPM.noerr;
        Kernel.GC (* << jm *)
  END Module;

  PROCEDURE Compile*;
    VAR beg, end, time: LONGINT; error: BOOLEAN; ch: CHAR;  defopt: ARRAY 32 OF CHAR;

    PROCEDURE GetOptions(VAR options: ARRAY OF CHAR);
      VAR i: SHORTINT;
    BEGIN i:=0;
      ch := S.nextCh; i:=0;
      WHILE ((ch >= "0") & (ch <= "9") OR (ch >= "a") & (ch <= "z") OR (ch >= "A") & (ch <= "Z")) DO
        i:=0; WHILE (options[i]#ch) & (options[i]#0X) DO INC(i) END;
        IF options[i]=0X THEN options[i]:=ch; options[i+1]:=0X END;
        Texts.Read(S, ch)
      END;
      S.nextCh := ch; Texts.Scan(S)
    END GetOptions;

    PROCEDURE InOptions(VAR options: ARRAY OF CHAR; opt: CHAR): BOOLEAN;
      VAR i: INTEGER;
    BEGIN i:=0; WHILE (options[i]#opt) & (options[i]#0X) DO INC(i) END;
      RETURN options[i]#0X;
    END InOptions;
(*
    PROCEDURE Do(filename: ARRAY OF CHAR; beg: LONGINT; options: ARRAY OF CHAR);
      VAR S1: Texts.Scanner; line: INTEGER; name: ARRAY 32 OF CHAR;
        fbeg, fend, ftime, breakpc: LONGINT; ftext: Texts.Text; f, u: BOOLEAN;
    BEGIN
      (*Texts.WriteString(W, filename); Texts.WriteString(W, "  compiling  ");*)
      IF ~SourceCoder THEN
        Texts.OpenScanner(S1, source, beg); Texts.Scan(S1);
        WHILE ~S1.eot & ((S1.class # Texts.Name) OR (S1.s # "MODULE")) DO Texts.Scan(S1) END;
        IF (S1.class = Texts.Name) & (S1.s = "MODULE") THEN Texts.Scan(S1);
          IF S1.class = Texts.Name THEN COPY(S1.s, name); Texts.WriteString(W, S1.s) END
        END ;
      END;
      Texts.Append(Oberon.Log, W.buf);
      line := S.line;
      f := FALSE;
      Texts.Scan(S);
      IF (S.line = line) & (S.class = Texts.Char) & (S.c = Oberon.OptionChar) THEN GetOptions(options) END;
      IF InOptions(options, "f") THEN
        LOOP
          Oberon.GetSelection(ftext, fbeg, fend, ftime);
          IF ftime >= 0 THEN
            Texts.OpenScanner(S1, ftext, fbeg); Texts.Scan(S1);
            IF S1.class = Texts.Int THEN breakpc := S1.i; EXIT END
          END ;
          Texts.WriteString(W, "  pc not selected"); Texts.WriteLn(W);
          Texts.Append(Oberon.Log, W.buf); error := TRUE; RETURN
        END
      END ;
      u := InOptions(options, "u");
      IF u & (make.Actualize#NIL) THEN u:=make.Actualize(name, Oberon.Log) ELSE u:=TRUE END;
      IF u THEN
        Texts.OpenReader(sourceR, source, beg);
        Module(sourceR, options, breakpc, Oberon.Log, error)
      END
    END Do;*)   PROCEDURE Do(beg: LONGINT; options: ARRAY OF CHAR);
      VAR line: INTEGER; S1: Texts.Scanner;
        fbeg, fend, ftime, breakpc: LONGINT; ftext: Texts.Text; u: BOOLEAN;
    BEGIN
      line := S.line;
      Texts.Scan(S);
      IF (S.line = line) & (S.class = Texts.Char) & ((S.c = Oberon.OptionChar) OR (S.c = "%")) THEN GetOptions(options) END;
      IF InOptions(options, "f") THEN
        LOOP
          Oberon.GetSelection(ftext, fbeg, fend, ftime);
          IF ftime # -1 THEN
            Texts.OpenScanner(S1, ftext, fbeg); Texts.Scan(S1);
            IF S1.class = Texts.Int THEN breakpc := S1.i; EXIT END
          END;
          Texts.WriteString(W, "  pc not selected"); Texts.WriteLn(W);
          Texts.Append(Oberon.Log, W.buf); error := TRUE; RETURN
        END
      END;
      u := InOptions(options, "u");
      IF u & (make.Actualize # NIL) THEN u := make.Actualize("", Oberon.Log) ELSE u := TRUE END;
      IF u THEN
        Texts.OpenReader(sourceR, source, beg);
        Module(sourceR, options, breakpc, Oberon.Log, error)
      END
    END Do;


    PROCEDURE OpenSource(VAR name: ARRAY OF CHAR; VAR text: Texts.Text; options: ARRAY OF CHAR);  (* ejz, 19.4.95 *)
    CONST SCTag = 011FFH;
    VAR F: Files.File; R: Files.Rider; tag: INTEGER; cmd: ARRAY 64 OF CHAR; par: Texts.Text; pos: LONGINT;
    BEGIN
      OPS.Get := NIL;
      F := Files.Old(name); par := NIL;
      IF F # NIL THEN
        Files.Set(R, F, 0);
        Files.ReadInt(R, tag);
        IF tag = SCTag THEN
          Files.ReadString(R, cmd);
          par := Oberon.Par.text; pos := Oberon.Par.pos;
          NEW(Oberon.Par.text); Texts.Open(Oberon.Par.text, ""); Oberon.Par.pos := 0; Texts.WriteString(W, name);
          Texts.Append(Oberon.Par.text, W.buf);
          Oberon.Call(cmd, Oberon.Par, FALSE, tag);
          Oberon.Par.text := par; Oberon.Par.pos := pos;
          IF OPS.Get # NIL THEN Texts.Open(text, "")
          ELSE text := NIL
          END
        ELSE Texts.Open(text, name)
        END
      ELSE text := NIL
      END;
      IF (par = NIL) & ((text = NIL) OR (text.len = 0)) THEN error := TRUE;
        Texts.WriteString(W, name); Texts.WriteString(W, " not found");
        Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf)
      ELSE Do(0, options)
      END
    END OpenSource;

  BEGIN
    error := FALSE; defopt[0]:=0X; COPY(dpath, OPM.outputPath);
    OPS.Get := NIL; SourceCoder := FALSE;
    Texts.OpenScanner(S, Oberon.Par.text, Oberon.Par.pos); Texts.Scan(S);
    IF make.Init#NIL THEN make.Init END;
    IF (S.class = Texts.Char) & (S.c # Oberon.OptionChar) THEN
      IF S.c = "*" THEN source:=Oberon.MarkedText();
        IF  source#NIL  THEN  Do(0, defopt) END
      ELSIF S.c = "^" THEN
        Oberon.GetSelection(source, beg, end, time);
        IF time #-1 THEN
          Texts.OpenScanner(S, source, beg); Texts.Scan(S); NEW(source);
          IF (S.class = Texts.Char) & (S.c = Oberon.OptionChar) & (Texts.Pos(S) - S.len <= end) THEN
            defopt[0] := 0X; GetOptions(defopt)
          END;
          WHILE (S.class IN {Texts.Name, Texts.String}) & (Texts.Pos(S) - S.len <= end) & ~error DO
              OpenSource(S.s, source, defopt) (* ejz, 19.4.95 *)
          END
        END
      ELSIF S.c = "@" THEN
        Oberon.GetSelection(source, beg, end, time);
        IF time #-1 THEN Do( beg, defopt) END
      END
    ELSE NEW(source);
      IF (S.class = Texts.Char) & (S.c = Oberon.OptionChar) & ~error THEN
        defopt[0] := 0X; GetOptions(defopt)
      END;
      WHILE (S.class IN {Texts.Name, Texts.String}) & ~error DO
                OpenSource(S.s, source, defopt) (* ejz, 19.4.95 *)
      END
    END;
    Oberon.Collect; COPY(dpath, OPM.outputPath)
  END Compile;

  PROCEDURE SetDestPath*;
      VAR beg, end, time: LONGINT; T: Texts.Text; S: Texts.Scanner;
    BEGIN Texts.OpenScanner(S, Oberon.Par.text, Oberon.Par.pos); Texts.Scan(S);
      IF  (S.class=Texts.Char)&(S.c="^")  THEN  Oberon.GetSelection(T, beg, end, time);
        IF  time #-1  THEN  Texts.OpenScanner(S, T, beg); Texts.Scan(S) END
      END;
      IF  (S.class IN {Texts.Name, Texts.String}) THEN
        Texts.WriteString(W, "Compiler.SetDestPath "); Texts.WriteString(W, S.s);
        Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf);
        COPY(S.s, dpath); COPY(dpath, OPM.outputPath)
      END
    END SetDestPath;


BEGIN Texts.OpenWriter(W); Init
END Compiler.
