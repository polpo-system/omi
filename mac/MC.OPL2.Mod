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

MODULE Interchange; (*mf 11.11.94 / tk object model  *)

  IMPORT
    SYS:=SYSTEM, PLT:=OPLT, PLL:=OPLL, PLC:=OPLC, PLV:=OPLV, Kernel, Modules;

  CONST
    Var=1; Par=2; VarPar=3; Con=4; LProc=6; XProc=7; TypDynArr=8; TypArray=9; TypPointer=10; TypRecord=11;
    TypProcTyp=12;
    Bool=2; Char=3; SInt=4; Int=5; LInt=6; Real=7; LReal=8; Set=9; String=10; Pointer=13; Comp=15; Array=2;
    Local=FALSE; Global=TRUE;

  VAR
    verbose: BOOLEAN;
    verboseHook*: PROCEDURE (M: Modules.Module);


  PROCEDURE- CacheFlush 0A0H, 0BDH;
  PROCEDURE^ Import(VAR B: Kernel.Buffer; M: Modules.Module);


  PROCEDURE BuildSym(VAR B: Kernel.Buffer; M: Modules.Module);  (*construct object list from buffer*)
    TYPE Table= POINTER TO ARRAY 256 OF LONGINT;
    VAR entryTab, varTab: Table; nofEntries, nofVars: INTEGER; obj: PLT.Object; mod: Modules.Module;
  BEGIN Import(B, M);
    IF  Modules.res=0 THEN  M.nofstrc:=1; obj:=NIL;
      mod:=Modules.modList; WHILE mod#NIL DO mod.nofreimp:=0; mod:=mod.link END;
      PLT.ReadScope(B, M, 0, obj, Global); M.publics:=SYS.VAL(LONGINT, obj);
      entryTab:=SYS.VAL(Table, M.entryTab); varTab:=SYS.VAL(Table, M.varTab); nofEntries:=2; nofVars:=0;
      WHILE obj#NIL DO
        CASE  obj.mode  OF
        | Var:  obj.adr:=varTab[nofVars]; INC(nofVars)
        | XProc:  obj.adr:=entryTab[nofEntries]; INC(nofEntries)
        | TypRecord:  PLL.TypSize(obj.typ); obj.typ.tdadr:=entryTab[nofEntries]; INC(nofEntries);
        | TypDynArr, TypArray, TypPointer, TypProcTyp:  PLL.TypSize(obj.typ)
        ELSE
        END;
        obj:=obj.nxtobj
      END
    END
  END BuildSym;


  PROCEDURE Str(s: ARRAY OF CHAR);
    VAR i: INTEGER;
  BEGIN i:=0; REPEAT Modules.resMsg[Modules.resMsgLen]:=s[i]; INC(i); INC(Modules.resMsgLen) UNTIL s[i-1]=0X; DEC(Modules.resMsgLen);
  END Str;

  PROCEDURE Ln;
  BEGIN Modules.resMsg[Modules.resMsgLen]:=0DX; INC(Modules.resMsgLen); Modules.resMsg[Modules.resMsgLen]:=0X
  END Ln;

  PROCEDURE err(n: INTEGER; VAR name: ARRAY OF CHAR);
  BEGIN Modules.res:=n;
    IF  n>0 THEN
      IF  n<20  THEN  Str(name) END;
      IF  n=1 THEN  Str(" not found");
      ELSIF n=2 THEN  Str(" not a valid object file")
      ELSIF n=8 THEN  Str(" no symbols")
      END
    END
  END err;

  PROCEDURE Decorate*(M: Modules.Module); (*append object list to module descriptor*)
    VAR B: Kernel.Buffer; ch0, ch1: CHAR; i: INTEGER; fname: Modules.ModuleName; done: BOOLEAN; symSize: LONGINT;
  BEGIN
    IF  M.publics=0 THEN
      IF  M.syms#0  THEN  Kernel.SetBuf(B, M.syms); BuildSym(B, M)
      ELSE  i:=0; ch0:=M.name[0];
        WHILE ch0#0X  DO  fname[i]:=ch0; INC(i); ch0:=M.name[i] END;
        fname[i]:="."; fname[i+1]:="O"; fname[i+2]:="b"; fname[i+3]:="j"; fname[i+4]:=0X; Kernel.OpenBuf(B, fname, 511, done);
        IF  done  THEN  Kernel.BufRCh(B, ch0);
          IF  ch0=0BBX  THEN  Kernel.BufRCh(B, ch1);
            Kernel.BufRNum(B, symSize);
            IF  2+15+symSize>511  THEN  Kernel.CloseBuf(B); Kernel.OpenBuf(B, fname, 2+15+symSize, done);
              Kernel.BufSkip(B, 2); Kernel.BufRNum(B, symSize)
            END;
            BuildSym(B, M)
          ELSE  err(2, M.name)  END;
          Kernel.CloseBuf(B)
        ELSE  err(8, M.name)  END
      END
    END
  END Decorate;

  PROCEDURE Import(VAR B: Kernel.Buffer; M: Modules.Module);
    VAR name: Modules.ModuleName; iM: Modules.Module;
  BEGIN Kernel.BufRString(B, name); M.nofreimp:=0;
    WHILE (name#"")&(Modules.res=0) DO  iM:=Modules.ThisMod(name);
      IF  Modules.res=0 THEN  (* Kernel.BufRBytes(B, key, 4); *)
        Decorate(iM);
        IF  Modules.res=0 THEN
          M.import[M.nofimp]:=SYS.VAL(LONGINT, iM); INC(M.nofimp);
          IF M.nofimp>=LEN(M.import^) THEN PLT.DoubleArr(M.import) END;
          INC(iM.refCnt); Kernel.BufRString(B, name)
        END
      END
    END
  END Import;

  PROCEDURE Unlink(mod: Modules.Module; all: BOOLEAN);
    VAR i: INTEGER; imp: Modules.Module;
  BEGIN i:=mod.nofimp;  (*portable module*)
    WHILE i > 0 DO  DEC(i); imp:=SYS.VAL(Modules.Module, mod.import[i]); DEC(imp.refCnt);
      IF  all & (imp.refCnt=0)  THEN  Modules.Unload(imp, TRUE) END
    END
  END Unlink;

  PROCEDURE* Load(VAR B: Kernel.Buffer; M: Modules.Module);
    VAR globals, obj: PLT.Object; m: SHORTINT; nofEntries, nofVars: INTEGER; symSize, below, above, linkBlk, entSlot, varSlot, eNum, TS: LONGINT;
      mod: Modules.Module; B1: Kernel.Buffer;
  BEGIN (* load all imports first, because of reimport-tables *)
    Kernel.BufRNum(B, symSize); B1:=B; Kernel.BufSkip(B1, symSize); Import(B, M);
    IF  Modules.res=0 THEN  M.nofstrc:=1; globals:=NIL;
      Kernel.BufRNum(B1, symSize); Kernel.BufRNum(B1, below); Kernel.BufRNum(B1, above); Import(B1, M);
      mod:=Modules.modList; WHILE mod#NIL DO mod.nofreimp:=0; mod:=mod.link END;
      PLT.ReadScope(B, M, 0, globals, Global); B:=B1;
      IF  Modules.res=0 THEN  PLL.Open(M.code);
        M.publics:=SYS.VAL(LONGINT, globals);
        PLT.ReadScope(B, M, 0, globals, Local); M.privates:=SYS.VAL(LONGINT, globals);  (*append*)
        PLL.Traverse(globals); PLL.AllocGlobalVar(globals, M.data);
        PLV.Load(B, M, globals, below, above);
        IF Modules.res=0 THEN M.codeLim:=M.code+2*LONG(PLL.pc); PLL.Close(M.code);

          nofEntries:=0; nofVars:=0; obj:=SYS.VAL(PLT.Object, M.publics);
          WHILE obj#NIL DO  m:=obj.mode;
            IF  m=Var THEN  INC(nofVars)  ELSIF (m=XProc) OR (m=TypRecord)  THEN  INC(nofEntries) END;
            obj:=obj.nxtobj
          END;
          Kernel.AllocBlock(linkBlk, 4*(nofEntries+nofVars));
          entSlot:=linkBlk; M.entryTab:=entSlot-8;  (*account for ModuleBody and GlobalDesc*)
          varSlot:=entSlot+4*nofEntries; M.varTab:=varSlot;
          eNum:=2;
          obj:=SYS.VAL(PLT.Object, M.publics);
          WHILE obj#NIL DO  m:=obj.mode;
            IF  m=Var THEN  SYS.PUT(varSlot, obj.adr); INC(varSlot, 4)
            ELSIF m=XProc THEN  SYS.PUT(entSlot, obj.adr); INC(entSlot, 4); INC(eNum)
            ELSIF m=TypRecord THEN  SYS.PUT(entSlot, obj.typ.tdadr); INC(entSlot, 4); INC(eNum) END;
            obj:=obj.nxtobj
          END;
          Kernel.CloseBuf(B); M.refCnt := 0; CacheFlush; (* SYS.GET(16AH, TS); M.struct[127]:=TS*5 *)
          IF  verbose&(verboseHook#NIL) THEN  verboseHook(M)  END;
          PLV.body(); Modules.res:=0;
        ELSE Unlink(M, FALSE); Kernel.CloseBuf(B);
        END;
      ELSE  Unlink(M, FALSE); Kernel.CloseBuf(B)  END
    ELSE  Unlink(M, FALSE); Kernel.CloseBuf(B)  END
  END Load;


  PROCEDURE ThisCmd(mod: Modules.Module; VAR name: ARRAY OF CHAR): Modules.Command;
    VAR obj: PLT.Object;
  BEGIN obj:=SYS.VAL(PLT.Object, mod.publics);
    WHILE obj#NIL DO
      IF  (obj.name=name)&(obj.mode=XProc)&(obj.par=NIL)&(obj.typ=PLT.notyp)  THEN
        Modules.res:=0; RETURN SYS.VAL(Modules.Command, obj.adr)
      END;
      obj:=obj.nxtobj
    END;
    err(1, name); RETURN NIL
  END ThisCmd;

  PROCEDURE EnumCmds(mod: Modules.Module; showProc: Modules.Command);
    VAR obj: PLT.Object;
  BEGIN obj:=SYS.VAL(PLT.Object, mod.publics);
    WHILE obj#NIL DO
      IF  (obj.mode=XProc)&(obj.par=NIL)&(obj.typ=PLT.notyp)  THEN
        Modules.theProc.adr:=obj.adr; COPY(obj.name, Modules.theProc.name); showProc()
      END;
      obj:=obj.nxtobj
    END
  END EnumCmds;

  PROCEDURE EnumScope(obj: PLT.Object; base: LONGINT; global: BOOLEAN; showVar: Modules.Command);
    VAR s: SHORTINT; i: INTEGER; ch: CHAR; sadr: LONGINT;
  BEGIN
    WHILE obj#NIL DO
      IF  (obj.mode=Var) OR (obj.mode=VarPar) OR (obj.mode=Par) THEN  Modules.theObj.adr:=base+obj.adr;
        IF  obj.mode=VarPar THEN  SYS.GET(Modules.theObj.adr, Modules.theObj.adr) END;
        CASE  obj.typ.form  OF
        | Bool: SYS.GET(Modules.theObj.adr, Modules.theObj.boolval)
        | Char: SYS.GET(Modules.theObj.adr, Modules.theObj.chval)
        | SInt: SYS.GET(Modules.theObj.adr, s); Modules.theObj.intval:=s
        | Int:  SYS.GET(Modules.theObj.adr, i); Modules.theObj.intval:=i
        | LInt, Pointer:  SYS.GET(Modules.theObj.adr, Modules.theObj.intval)
        | Real: SYS.GET(Modules.theObj.adr, Modules.theObj.rval)
        | LReal:  SYS.GET(Modules.theObj.adr, Modules.theObj.lrlval)
        | Set:  SYS.GET(Modules.theObj.adr, Modules.theObj.setval)
        | Comp:
          IF  (obj.typ.comp=Array)&(obj.typ.BaseTyp.form=Char)&(obj.typ.size<=32) THEN  i:=0; sadr:=Modules.theObj.adr;
            LOOP  SYS.GET(sadr, ch);
              IF  (ch < " ") OR (ch >= 90X) OR (i=31) THEN  EXIT  END;
              Modules.theObj.strval[i]:=ch; INC(i); INC(sadr)
            END;
            Modules.theObj.strval[i]:=0X; Modules.theObj.class:=String;
          END
        ELSE  Modules.theObj.intval:=SYS.VAL(LONGINT, obj.typ)  END;
        Modules.theObj.class:=obj.typ.form; Modules.theObj.global:=global; COPY(obj.name, Modules.theObj.name); showVar()
      END;
      obj:=obj.nxtobj
    END
  END EnumScope;

  PROCEDURE EnumGlobs(mod: Modules.Module; showVar: Modules.Command);
  BEGIN Modules.theObj.rdonly:=FALSE; EnumScope(SYS.VAL(PLT.Object, mod.privates), 0, TRUE, showVar)
  END EnumGlobs;

  PROCEDURE EnumLocls(mod: Modules.Module; fp, pc: LONGINT; showProc, showVar: Modules.Command);
    VAR obj: PLT.Object;
  BEGIN obj:=SYS.VAL(PLT.Object, mod.privates);
    LOOP
      IF  obj=NIL THEN  COPY("$$", Modules.theProc.name); showProc(); EnumGlobs(mod, showVar); EXIT
      ELSIF (obj.mode IN {LProc, XProc})&(obj.adr < pc)&(obj.lim > pc)  THEN
        COPY(obj.name, Modules.theProc.name); showProc();
        EnumScope(obj.locals, fp, FALSE, showVar);
        EXIT
      END;
      obj:=obj.nxtobj
    END
  END EnumLocls;


  PROCEDURE Start*;
  BEGIN Modules.extended.Load:=Load
  END Start;

  PROCEDURE Stop*;
  BEGIN Modules.extended.Load:=NIL
  END Stop;

  PROCEDURE Verbose*;
  BEGIN verbose:=TRUE
  END Verbose;

  PROCEDURE ChecksOn*;
  BEGIN PLC.inxchk:=TRUE; PLC.typchk:=TRUE; PLC.nilchk:=TRUE; PLC.ptrinit:=TRUE
  END ChecksOn;

  PROCEDURE ChecksOff*;
  BEGIN PLC.inxchk:=FALSE; PLC.typchk:=FALSE; PLC.nilchk:=FALSE; PLC.ptrinit:=FALSE
  END ChecksOff;


  PROCEDURE Setup;
    VAR M: Modules.Module;
  BEGIN M:=Modules.modList;
    WHILE M#NIL DO
      IF  M.syms#0  THEN  Modules.res:=0; Decorate(M) END;
      M:=M.link
    END
  END Setup;


BEGIN Setup; PLC.inxchk:=TRUE; PLC.typchk:=TRUE; PLC.nilchk:=TRUE; PLC.ptrinit:=TRUE;
  Modules.extended.Load:=Load; Modules.extended.Unlink:=Unlink; Modules.extended.ThisCmd:=ThisCmd;
  Modules.extended.EnumCmds:=EnumCmds; Modules.extended.EnumGlobs:=EnumGlobs; Modules.extended.EnumLocls:=EnumLocls
END Interchange.