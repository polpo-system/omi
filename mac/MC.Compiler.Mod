(* OBERON System 3, Release 2.2.

Copyright 1996, 1997

Team of the Institute of Computer Systems of ETH Zürich, ETH Center, CH-8092 Zürich
Team of the Information and Computer Science at the University of California at Irvine, Irvine, CA 92697-3425

e-mail: oberon@inf.ethz.ch.

This module may be used under the conditions of the general Oberon System 3 license contract.
The full text can be downloaded from

  "ftp://ftp.inf.ethz.ch/pub/software/Oberon/System3/license.txt;A"

or requested from the above mentioned address.

Under the license terms stated it is in particular (a) prohibited to modify the interface of this module
in any way that disagrees with style or content of the system and (b) requested to provide all conversions
of the source code to another platform with the name OBERON. *)

MODULE Compiler;  (*mf/tk 12.12.95*)

  IMPORT
    Kernel, Texts, Viewers, Oberon, Display, Objects, Modules, Files,
    OPP:=OOPP, OPB:=OOPB, OPV:=OOPV, OPL:=OOPL, OPC:=OOPC, OPT:=OOPT,
    OPS:=OOPS, OPM:=OOPM, POPV:=OPOPV;

  CONST
    (*OP2 Options*) oinxchk=0; oovflchk=1; onilchk=2; oranchk=3; otypchk=4; optrinit=5; oassert=6; orefinfo=7; odbginfo=8;
    (*OP2 Options*) ofindpc=9; onewsf=10; oextsf=11; owarning=12; oupdate=13; ominim=14; ogc=15; ooberon2=16; oportbl=17;
    DefOpt={oinxchk, otypchk, onilchk, ogc, optrinit, orefinfo, oassert, ooberon2, oportbl};
    MakeName = "OOPU";

  VAR
    dpath: ARRAY 512 OF CHAR;
    signedOn, SourceCoder: BOOLEAN;
    (* global because of the GC call *)
    source: Texts.Text; sourceR: Texts.Reader;
    S: Texts.Scanner; W: Texts.Writer;
    m: Modules.Module;
    make*: RECORD
      Init*: PROCEDURE ();
      Actualize*: PROCEDURE (name: ARRAY OF CHAR; log: Texts.Text): BOOLEAN;
    END;

  PROCEDURE SignOn;
  BEGIN
    IF  ~signedOn THEN  signedOn:=TRUE;
      Texts.WriteString(W, "Oberon Portable Compiler / nw & rc"); Texts.WriteLn(W);
      Texts.WriteString(W, "MC68020 Code Generator  / mf & tk 9.7.96"); Texts.WriteLn(W);
      Texts.Append(Oberon.Log, W.buf)
    END
  END SignOn;

  PROCEDURE ThisFrame(X, Y: INTEGER; VAR F: Display.Frame);
    VAR M: Display.LocateMsg;
  BEGIN M.X := X; M.Y := Y; M.F := NIL; M.loc := NIL; Display.Broadcast(M); F := M.loc
  END ThisFrame;

  PROCEDURE GetText(VAR par: Display.Frame): Texts.Text;
    VAR M: Objects.LinkMsg; t: Texts.Text;
  BEGIN
    t := NIL; ThisFrame(Oberon.Pointer.X, Oberon.Pointer.Y, par);
    IF par # NIL THEN
      M.id := Objects.get; M.name := "Model"; M.obj := NIL; M.res := -1; par.handle(par, M);
      IF (M.obj # NIL) & (M.obj IS Texts.Text) THEN t := M.obj(Texts.Text) END
    END;
    RETURN t
  END GetText;

  PROCEDURE Module*(source: Texts.Reader; opt: ARRAY OF CHAR; breakpc: LONGINT; log: Texts.Text; VAR error: BOOLEAN);
    VAR newSF, extSF: BOOLEAN; options: SET; modName: OPS.Name; mod: OPT.Node; cmd: ARRAY 32 OF CHAR; i, res: INTEGER; ch: CHAR;
  BEGIN
    options:=DefOpt; i:=0;
    REPEAT  ch:=opt[i]; INC(i);
      IF ch = "x" THEN options := options / {oinxchk}
      ELSIF ch = "t" THEN options := options / {otypchk}
      ELSIF ch = "s" THEN options := options / {onewsf}
      ELSIF ch = "p" THEN options := options / {optrinit}
      ELSIF ch = "n" THEN options := options / {onilchk}
      ELSIF ch = "a" THEN options := options / {oassert}
      ELSIF ch = "f" THEN options := options / {ofindpc}; options := options - {oportbl}
      ELSIF ch = "e" THEN options := options / {oextsf}
      ELSIF ch = "r" THEN options := options / {orefinfo}
      ELSIF ch = "d" THEN options := options / {odbginfo}
      ELSIF ch = "m" THEN options := options / {ominim}
      ELSIF ch = "g" THEN options := options / {ogc}
      ELSIF ch = "u" THEN options := options / {oupdate}
      ELSIF ch = "w" THEN options := options / {owarning}
      ELSIF ch = "N" THEN options := options - {oportbl}
      ELSIF ch = "P" THEN options := options + {oportbl}
      END;
    UNTIL ch=0X;
    OPM.Init(options, source, log);
    IF  oportbl IN options  THEN  OPB.typSize:=POPV.NoTypSize ELSE  OPB.typSize:=OPV.TypSize  END;
    newSF:=onewsf IN options; extSF:=oextsf IN options;
    OPP.Module(mod, modName, options);
    IF  OPM.noerr THEN
      IF  (ominim IN options) & ~(oportbl IN options) THEN  cmd:="OOPX.Minimize"; Oberon.Call(cmd, Oberon.Par, FALSE, res)  END;
      OPM.Begin(modName);
      IF  ~(oportbl IN options) THEN  OPL.Init(options, modName)  END;
      OPT.Export(modName, newSF, extSF);
      IF  newSF THEN  OPM.LogWStr(" new symbol file")
      ELSIF extSF THEN  OPM.LogWStr(" extended symbol file")
      END;
      IF  oportbl IN options  THEN
        OPM.errpos:=0;
        IF  OPM.noerr THEN  POPV.Module(mod)  END
      ELSE
        OPV.AdrAndSize;
        IF  OPM.noerr THEN  OPM.errpos:=0; OPC.Init(options); OPV.Module(options, mod, breakpc);
          IF  OPM.noerr THEN  OPL.OutCode END
        END
      END
    END;
    OPT.CloseScope; OPT.Close; OPM.LogWLn; error:=~OPM.noerr;
    IF  ogc IN options  THEN  Kernel.GC END
  END Module;


  PROCEDURE Compile*;
    VAR beg, end, time: LONGINT; error: BOOLEAN; ch: CHAR; F: Display.Frame; par: Texts.Text;
      defopt: ARRAY 32 OF CHAR; f: Files.File; r: Files.Rider; tag: INTEGER; cmd: ARRAY 64 OF CHAR;

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

    PROCEDURE Do(filename: ARRAY OF CHAR; beg: LONGINT; options: ARRAY OF CHAR);
      VAR S1: Texts.Scanner; line: INTEGER; pos: LONGINT; name: ARRAY 32 OF CHAR; u: BOOLEAN;
        fbeg, fend, ftime, breakpc: LONGINT; ftext: Texts.Text;
    BEGIN Texts.WriteString(W, filename); Texts.Write(W, 9X); Texts.WriteString(W, "compiling ");
      IF ~SourceCoder THEN
        Texts.OpenScanner(S1, source, beg); Texts.Scan(S1);
        WHILE ~S1.eot & ((S1.class#Texts.Name) OR (S1.s#"MODULE"))  DO  Texts.Scan(S1)  END;
        IF  (S1.class=Texts.Name)&(S1.s="MODULE") THEN  Texts.Scan(S1);
          IF  S1.class=Texts.Name THEN  COPY(S1.s, name); Texts.Write(W, 22X); Texts.WriteString(W, S1.s); Texts.Write(W, 22X)  END
        END
      END;
      Texts.Append(Oberon.Log, W.buf); line:=S.line; pos:=Texts.Pos(S); Texts.Scan(S);
      IF  (S.line=line)&(S.class=Texts.Char)&(Texts.Pos(S)=pos+1)&(S.c=Oberon.OptionChar) THEN  GetOptions(options) END;
      IF InOptions(options, "f") THEN
        LOOP  Oberon.GetSelection(ftext, fbeg, fend, ftime);
          IF  ftime >= 0  THEN  Texts.OpenScanner(S1, ftext, fbeg); Texts.Scan(S1);
            IF  S1.class=Texts.Int  THEN  breakpc:=S1.i; EXIT END
          END;
          Texts.Write(W, 9X); Texts.WriteString(W, "no pc selected"); Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf);
          error:=TRUE; RETURN
        END
      END;
      u:=InOptions(options, "u");
      IF u & (make.Actualize#NIL) THEN u:=make.Actualize(name, Oberon.Log) ELSE u:=TRUE END;
      IF u THEN Texts.OpenReader(sourceR, source, beg); Module(sourceR, options, breakpc, Oberon.Log, error) END;
    END Do;

  BEGIN
    IF make.Init#NIL THEN make.Init() END;
    error:=FALSE; defopt[0]:=0X; COPY(dpath, OPM.outputPath); OPS.Get := NIL; SourceCoder := FALSE;
    Texts.OpenScanner(S, Oberon.Par.text, Oberon.Par.pos); Texts.Scan(S); SignOn;
    IF  (S.class=Texts.Char) & (S.c # Oberon.OptionChar)  THEN
      IF  S.c="*" THEN  source:=GetText(F);
        IF  source#NIL  THEN  Do("", 0, defopt) END
      ELSIF S.c="^" THEN  Oberon.GetSelection(source, beg, end, time);
        IF  time >= 0 THEN  Texts.OpenScanner(S, source, beg); Texts.Scan(S); NEW(source);
          IF (S.class = Texts.Char) & (S.c = Oberon.OptionChar) & (Texts.Pos(S)-S.len <= end) THEN
            defopt[0] := 0X; GetOptions(defopt)
          END;
          WHILE (S.class IN {Texts.Name, Texts.String}) & (Texts.Pos(S)-S.len <= end) & ~error  DO
            Texts.Open(source, S.s);
            IF  source.len#0  THEN  Do(S.s, 0, defopt)
            ELSE  Texts.WriteString(W, S.s); Texts.WriteString(W, " not found");
              Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf); error:=TRUE
            END
          END
        END
      ELSIF S.c="@" THEN  Oberon.GetSelection(source, beg, end, time);
        IF  time >= 0 THEN  Do("", beg, defopt) END
      END
    ELSE  NEW(source);
      IF (S.class = Texts.Char) & (S.c = Oberon.OptionChar) THEN
        defopt[0] := 0X; GetOptions(defopt)
      END;
      WHILE (S.class IN {Texts.Name, Texts.String}) & ~error  DO
        OPS.Get := NIL; SourceCoder := FALSE;
        f := Files.Old(S.s);
        IF f # NIL THEN
          Files.Set(r, f, 0); Files.ReadInt(r, tag);
          IF tag = 011FFH (* SourceCoder *) THEN
            Files.ReadString(r, cmd);
            par := Oberon.Par.text; beg := Oberon.Par.pos;
            NEW(Oberon.Par.text); Texts.Open(Oberon.Par.text, ""); Oberon.Par.pos := 0; Texts.WriteString(W, S.s);
            Texts.Append(Oberon.Par.text, W.buf);
            Oberon.Call(cmd, Oberon.Par, FALSE, tag);
            Oberon.Par.text := par; Oberon.Par.pos := beg;
            IF OPS.Get # NIL THEN SourceCoder := TRUE; NEW(source); Texts.Open(source, "")
            ELSE
              Texts.WriteString(W, cmd); Texts.WriteString(W, " not found");
              Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf)
            END
          ELSE Texts.Open(source, S.s)
          END;
          Do(S.s, 0, defopt)
        ELSE
          Texts.WriteString(W, S.s); Texts.WriteString(W, " not found");
          Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf); error := TRUE
        END
      END
    END;
    COPY(dpath, OPM.outputPath)
  END Compile;

  PROCEDURE SetDestPath*;
    VAR beg, end, time: LONGINT; T: Texts.Text; S: Texts.Scanner;
  BEGIN Texts.OpenScanner(S, Oberon.Par.text, Oberon.Par.pos); Texts.Scan(S);
    IF  (S.class=Texts.Char)&(S.c="^")  THEN  Oberon.GetSelection(T, beg, end, time);
      IF  time >= 0 THEN  Texts.OpenScanner(S, T, beg); Texts.Scan(S) END
    END;
    IF  S.class IN {Texts.Name, Texts.String} THEN  Texts.WriteString(W, "Compiler.SetDestPath "); Texts.WriteString(W, S.s);
      Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf); COPY(S.s, dpath); COPY(dpath, OPM.outputPath)
    END
  END SetDestPath;

BEGIN Texts.OpenWriter(W); m:=Modules.ThisMod(MakeName);
END Compiler.