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

MODULE Modules; (*mf/tk 7.12.95*)

  IMPORT
    SYS:=SYSTEM, Kernel;  (*IMPORT A5World; modList: -24(A5); mark1: -20(A5); scan: -16(A5)*)

  CONST
    ModNameLen*= 32;
    DefMaxImport=64; DefMaxStruct=32; DefMaxReimp=32;

  TYPE
    Command*= PROCEDURE;
    ModuleName*= ARRAY ModNameLen OF CHAR;

    ExportPtr* = POINTER TO ExportDesc;
    ExportDesc* = RECORD
      fp*: LONGINT; adr*: LONGINT;
      nofExp*: INTEGER; dsc*: LONGINT; (* ExportPtr *)
    END;
    ExportList = POINTER- TO ARRAY MAX(INTEGER) OF ExportDesc;

    ArrayPtr* = POINTER TO ARRAY OF LONGINT;

    TerminationHandler*=Kernel.Handler;

    Module*= POINTER TO ModDesc;
    ModDesc*= RECORD
      link*: Module; name*: ModuleName; refCnt*: INTEGER;
      code*, codeLim*, data*, imodTab*, entryTab*, varTab*, refs*, comms*, syms*: LONGINT;
      publics*, privates*: LONGINT;
      nofimp*: INTEGER; import*: ArrayPtr;  (*for native modules, nofimp counts only re_exported imports*)
      nofstrc*: INTEGER; struct*: ArrayPtr; (*for portable modules, nofimp counts all imports, imodTab set to zero*)
      nofreimp*: INTEGER; reimp*: ArrayPtr;
      export*: ExportDesc;
      (*Input.Time of loading stored in struct[126]..struct[127]*)
      term: TerminationHandler;
    END;

  CONST
    EUEnd = 0;  EURecord = 1; EUobjScope = 0; EUrecScope = 1;   EUerrScope = -1;

  VAR
    res*: INTEGER; resMsg*: ARRAY 256 OF CHAR;
    resMsgLen*: INTEGER; modList*: Module;
    extended*: RECORD
      Load*: PROCEDURE(VAR buf: Kernel.Buffer; mod: Module);
      Unlink*: PROCEDURE(mod: Module; all: BOOLEAN);
      ThisCmd*: PROCEDURE(mod: Module; VAR name: ARRAY OF CHAR): Command;
      EnumCmds*: PROCEDURE(mod: Module; showProc: Command);
      EnumGlobs*: PROCEDURE(mod: Module; showVar: Command);
      EnumLocls*: PROCEDURE(mod: Module; fp, pc: LONGINT; showProc, showVar: Command)
    END;
    theMod*: Module;
    theProc*: RECORD name*: ModuleName; adr*, pc*, relpc*, fp*: LONGINT END;
    theObj*: RECORD name*: ModuleName; adr*: LONGINT; class*: INTEGER; global*, rdonly*, boolval*: BOOLEAN; chval*: CHAR; intval*: LONGINT; setval*: SET; rval*: REAL; lrlval*: LONGREAL; strval*: ARRAY 128 OF CHAR END;
    a5: LONGINT; mark1, scan: PROCEDURE; B: Kernel.Buffer;

  PROCEDURE- CacheFlush 0A0H, 0BDH;

  PROCEDURE Fixup(adr: LONGINT; with: Module);
    TYPE Table=POINTER TO ARRAY 512 OF LONGINT; VAR link, code: INTEGER; entry, var: Table;
  BEGIN entry:=SYS.VAL(Table, with.entryTab); var:=SYS.VAL(Table, with.varTab);
    REPEAT  SYS.GET(adr, link); SYS.GET(adr+2, code);
      IF  code<0  THEN  SYS.PUT(adr, var[(code DIV 100H) MOD 80H]+(code MOD 100H))  ELSE  SYS.PUT(adr, entry[code]) END;
      INC(adr, LONG(link)*2)
    UNTIL link=0
  END Fixup;

  PROCEDURE FixupObj(adr, patch: LONGINT; with: Module);
    VAR link, code: INTEGER; i, x, adr0, adr1: LONGINT;
  BEGIN
    REPEAT  SYS.GET(adr, link);  SYS.GET(adr+2, code);
      IF code<0 THEN SYS.PUT(adr, patch+with.data+(code MOD 100H)) (* Var *)
      ELSE
        IF code>=1 THEN   (* copy base types of typedesc *)
          adr0:=adr-code*4; adr1:=patch*2+with.code+4;
          i:=0; WHILE i<=code DO
            SYS.GET(adr1, x); SYS.PUT(adr0, x);
            INC(adr0, 4); INC(adr1, 4); INC(i)
          END;
        ELSE  SYS.PUT(adr, patch*2+with.code)
        END;
      END;
      INC(adr, LONG(link)*2);
    UNTIL link=0;
  END FixupObj;

  (* error message *)

  PROCEDURE Str(s: ARRAY OF CHAR);
    VAR i: INTEGER;
  BEGIN i:=0; REPEAT resMsg[resMsgLen]:=s[i]; INC(i); INC(resMsgLen) UNTIL s[i-1]=0X; DEC(resMsgLen);
  END Str;

  PROCEDURE Ch(ch: CHAR);
  BEGIN resMsg[resMsgLen]:=ch; INC(resMsgLen); resMsg[resMsgLen]:=0X
  END Ch;

  PROCEDURE Ln;
  BEGIN resMsg[resMsgLen]:=0DX; INC(resMsgLen); resMsg[resMsgLen]:=0X
  END Ln;

  PROCEDURE Clear;
  BEGIN resMsg[0]:=0X; resMsgLen:=0
  END Clear;

  PROCEDURE err(n: INTEGER; VAR name: ARRAY OF CHAR);
  BEGIN res:=n;
    IF  res>0 THEN
      IF  res<20  THEN  Str(name) END;
      IF  res=1 THEN  Str(" not found");
      ELSIF res=2 THEN  Str(" not a valid object file")
      ELSIF res=7 THEN  Str(" cyclic imported")
      ELSIF res=8 THEN  Str(" no symbols")
      END
    END
  END err;

  (** Returns a handle to an already loaded module, or loads a module and all its imported modules. *)
  PROCEDURE ThisMod*(name: ARRAY OF CHAR): Module;
    TYPE BlkPtr=POINTER TO ARRAY 64*1024 OF CHAR;
    VAR mod, import: Module; B: Kernel.Buffer; found: BOOLEAN; ch, ch0, ch1: CHAR; i: INTEGER; TS: LONGINT; blk: BlkPtr;
      sfSize, codeSize, constSize, dataSize, nofEntries, nofImp, nofVar, cmdSize, refSize: LONGINT;
      blkBase, dataBlk, linkBlk, slot, tabLim, offset, fixoff, globPtrDesc: LONGINT; iname: ModuleName; body: PROCEDURE;

    PROCEDURE LoadExpBlock(M: Module);
      VAR struct: ARRAY 1024 OF ExportPtr; nofStr: INTEGER;

      PROCEDURE LoadScope(VAR scope: ExportDesc; level: INTEGER; adr: LONGINT);
        VAR no, no2: INTEGER; fp, off: LONGINT; dsc: ExportList;
      BEGIN
        Kernel.BufRBytes(B, scope.nofExp, 2); no:=0; no2:=0;
        Kernel.AllocBlock(SYS.VAL(LONGINT, scope.dsc), -SIZE(ExportDesc)*scope.nofExp);
        dsc:=SYS.VAL(ExportList, scope.dsc); IF adr#0 THEN dsc[0].adr:=adr END;
        IF level=EUrecScope THEN INC(nofStr); struct[nofStr]:=SYS.VAL(ExportPtr, SYS.ADR(scope)) END;
        Kernel.BufRNum(B, fp);
        WHILE fp#EUEnd DO
          IF fp=EURecord THEN Kernel.BufRNum(B, off);
            IF off<0 THEN dsc[no2].nofExp:=struct[-off].nofExp;
              dsc[no2].dsc:=struct[-off].dsc;   (* old type *)
            ELSE LoadScope(dsc[no2], EUrecScope, off) END;
          ELSE IF level=EUobjScope THEN Kernel.BufRNum(B, dsc[no].adr) END;
            dsc[no].fp:=fp; no2:=no; INC(no)
          END;
          Kernel.BufRNum(B, fp);
        END;
      END LoadScope;

    BEGIN nofStr:=0; LoadScope(M.export, EUobjScope, 0)
    END LoadExpBlock;

    PROCEDURE CheckUseBlock(M: Module);
      VAR mod: Module; name: ModuleName;

      PROCEDURE Err;
      BEGIN
        IF res=0 THEN
          Str(M.name); Str(" imports incompatible version of ");
          Str(mod.name); Str(": "); res:=16;
        ELSE Ch(9X) END;
      END Err;

      PROCEDURE CheckScope(scope: ExportDesc; level: INTEGER);
        VAR fp, link, i: LONGINT; dsc, tadr: ExportList; tmpErr: BOOLEAN;
      BEGIN tmpErr:=(level=EUerrScope);
        dsc:=SYS.VAL(ExportList, scope.dsc); i:=0;
        Kernel.BufRNum(B, fp);
        WHILE fp#EUEnd DO
          IF fp=EURecord THEN Kernel.BufRNum(B, link);
            IF tmpErr THEN CheckScope(dsc[i], EUerrScope)
            ELSE
              IF link#0 THEN tadr:=SYS.VAL(ExportList, dsc[i].dsc); FixupObj(M.code+link*2, tadr[0].adr, mod)
              END;
              CheckScope(dsc[i], EUrecScope);
            END;
          ELSE Kernel.BufRString(B, name);
            IF level>=EUobjScope THEN tmpErr:=FALSE;
              IF level=EUobjScope THEN Kernel.BufRNum(B, link) END;
              i:=0; WHILE (i<scope.nofExp) & (dsc[i].fp#fp) DO INC(i) END;
              IF i>=scope.nofExp THEN Err; tmpErr:=TRUE; Ln; Ch(9X);
                IF name="@" THEN Str("RECORD ")
                ELSE Str(name) END; Str(" incompatible");
              ELSIF (level=EUobjScope) & (link#0) THEN FixupObj(M.code+link*2, dsc[i].adr, mod)
              END
            END
          END;
          Kernel.BufRNum(B, fp);
        END;
      END CheckScope;

    BEGIN Kernel.BufRString(B, name);
      WHILE (name#"") & (res=0) DO
        mod:=ThisMod(name);
        IF res=0 THEN INC(mod.refCnt); SYS.PUT(M.imodTab+4*M.nofimp, mod);
          INC(M.nofimp); CheckScope(mod.export, EUobjScope)
        END;
        Kernel.BufRString(B, name);
      END;
    END CheckUseBlock;

  BEGIN
    SYS.GET(16AH, TS); res:=0; Clear; mod:=modList;
    WHILE (mod#NIL) & (name#mod.name) DO  mod:=mod.link;    END;
    IF  mod=NIL THEN  found:=FALSE; i:=0; ch0:=name[0];
      WHILE (ch0#0X) & (i < 28) DO  iname[i]:=ch0; INC(i); ch0:=name[i] END;
      IF  i < 28  THEN  iname[i]:="."; iname[i+1]:="O"; iname[i+2]:="b"; iname[i+3]:="j"; iname[i+4]:=0X;
        Kernel.OpenBuf(B, iname, MAX(LONGINT), found) (*buffer complete object file*)
      END;
      IF  found THEN  Kernel.BufRCh(B, ch0); Kernel.BufRCh(B, ch1);
        IF  ch0=0BBX  THEN  NEW(mod); NEW(mod.import, DefMaxImport); NEW(mod.struct, DefMaxStruct);
          NEW(mod.reimp, DefMaxReimp); (* mod.struct[126]:=TS*5; *)
          COPY(name, mod.name); mod.refCnt:=-1;
          IF  ch1=11X THEN  mod.link:=modList; modList:=mod;
            Kernel.BufRNum(B, sfSize); Kernel.BufSkip(B, sfSize);

            Kernel.BufRNum(B, codeSize); Kernel.BufRNum(B, constSize); Kernel.BufRNum(B, dataSize);
            Kernel.BufRNum(B, nofImp); Kernel.BufRNum(B, nofEntries); Kernel.BufRNum(B, nofVar);

            Kernel.AllocBlock(dataBlk, -(dataSize+4));
            Kernel.AllocBlock(SYS.VAL(LONGINT, blk), 2*(codeSize+constSize));
            Kernel.AllocBlock(linkBlk, 4*(nofImp+nofEntries+nofVar));

            blkBase:=SYS.VAL(LONGINT, blk); mod.code:=blkBase; mod.codeLim:=blkBase+2*codeSize; mod.data:=dataBlk+4;
            mod.imodTab:=linkBlk; mod.entryTab:=mod.imodTab+4*nofImp; mod.varTab:=mod.entryTab+4*nofEntries;
            tabLim:=mod.varTab+4*nofVar; mod.nofimp:=0;

            LoadExpBlock(mod);

            Kernel.BufRBytes(B, blk^, 2*(codeSize+constSize));
            slot:=mod.entryTab;
            WHILE slot < mod.varTab DO  Kernel.BufRNum(B, offset); SYS.PUT(slot, blkBase+2*offset); INC(slot, 4)  END;
            WHILE slot < tabLim DO  Kernel.BufRNum(B, offset); SYS.PUT(slot, mod.data+offset); INC(slot, 4) END;

            Kernel.BufRNum(B, fixoff);
            IF  fixoff#0  THEN  Fixup(blkBase+2*fixoff, mod)  END;

            CheckUseBlock(mod);

            IF  res=0 THEN
              Kernel.BufRNum(B, refSize); Kernel.AllocBlock(SYS.VAL(LONGINT, blk), refSize);
              Kernel.BufRBytes(B, blk^, refSize); mod.refs:=SYS.VAL(LONGINT, blk);
              Kernel.BufRNum(B, cmdSize); Kernel.AllocBlock(SYS.VAL(LONGINT, blk), cmdSize);
              Kernel.BufRBytes(B, blk^, cmdSize); mod.comms:=SYS.VAL(LONGINT, blk);
              SYS.GET(mod.entryTab, body); SYS.GET(mod.entryTab+4, globPtrDesc); SYS.PUT(dataBlk, globPtrDesc+1);
              mod.nofimp:=0; Kernel.CloseBuf(B); mod.refCnt := 0; CacheFlush;
              (* SYS.GET(16AH, TS); mod.struct[127]:=TS*5; *) body; res:=0; Clear
            ELSE  Kernel.CloseBuf(B); Kernel.DeAllocBlock(linkBlk); Kernel.DeAllocBlock(blkBase); Kernel.DeAllocBlock(dataBlk);
              slot:=mod.imodTab; i:=0; WHILE i<mod.nofimp DO SYS.GET(slot, import); DEC(import.refCnt); INC(slot, 4); INC(i) END;
              IF modList = mod THEN modList := mod.link
              ELSE import := modList; WHILE import.link # mod DO import := import.link END; import.link := mod.link
              END;
              mod:=NIL;
            END;
          ELSIF (ch1=88X)&(extended.Load#NIL) THEN  mod.link:=modList; modList:=mod; extended.Load(B, mod);
            IF res#0 THEN
              IF modList = mod THEN modList := mod.link
              ELSE import := modList; WHILE import.link # mod DO import := import.link END; import.link := mod.link
              END;
              mod:=NIL;
            END;
          ELSE  err(2, name); Kernel.CloseBuf(B); mod:=NIL  END
        ELSE  err(2, name)  END
      ELSE  err(1, name)  END
    ELSIF mod.refCnt < 0 THEN err(7, name) END;
    RETURN mod
  END ThisMod;

  (** Returns a procedure variable representing an exported command in a module. Calling this procedure, executes the command. *)
  PROCEDURE ThisCommand*(mod: Module; name: ARRAY OF CHAR): Command;
    VAR B: Kernel.Buffer; cname: ModuleName; adr: LONGINT; P: Command;
  BEGIN
    IF  mod.comms#0 THEN  Kernel.SetBuf(B, mod.comms); Kernel.BufRString(B, cname);
      LOOP
        IF  cname=""  THEN  err(1, name); RETURN NIL
        ELSE  Kernel.BufRNum(B, adr);
          IF  cname=name  THEN  res:=0; Clear; SYS.GET(mod.entryTab+4*adr, P); RETURN P
          ELSE  Kernel.BufRString(B, cname) END
        END
      END
    ELSIF extended.ThisCmd#NIL  THEN  RETURN extended.ThisCmd(mod, name)  END
  END ThisCommand;


  PROCEDURE Delete(mod: Module);
    VAR m: Module;
  BEGIN m:=modList;
    IF  mod=m THEN  modList:=mod.link
    ELSE
      WHILE mod#m.link  DO  m:=m.link END;
      m.link:=m.link.link
    END
  END Delete;

  PROCEDURE Unload*(mod: Module; all: BOOLEAN);
    VAR p: LONGINT; imp: Module;
  BEGIN p:=mod.imodTab;
    IF  p#0 THEN  (*native module*)
      WHILE p < mod.entryTab  DO  SYS.GET(p, imp); DEC(imp.refCnt); INC(p, 4);
        IF  all & (imp.refCnt=0)  THEN  Unload(imp, TRUE) END
      END
    ELSIF extended.Unlink#NIL THEN  extended.Unlink(mod, all) END;
    Delete(mod)
  END Unload;

  (** Free a module from memory. Only modules with no clients can be freed. The all flag requests that all imported modules should be freed too (i.e. a recursive call to Free). *)
  PROCEDURE Free*(name: ARRAY OF CHAR; all: BOOLEAN);
    VAR mod: Module; h: TerminationHandler;
  BEGIN mod:=modList;
    WHILE (mod#NIL) & (mod.name#name) DO  mod:=mod.link END;
    IF  mod=NIL THEN  err(1, name)
    ELSIF mod.refCnt#0  THEN  err(2, name)
    ELSE
      IF mod.term # NIL THEN h := mod.term; mod.term := NIL; h() END;
      Unload(mod, all); res:=0; Clear
    END
  END Free;

  PROCEDURE KeepCore;
    VAR mod: Module;
  BEGIN mod:=modList;
    WHILE mod#NIL DO  INC(mod.refCnt); mod:=mod.link  END
  END KeepCore;

  (** Install a procedure to be called before a module is freed from memory, or before the Oberon system terminates.
  The termination handler  is associated with the module where it is located *)
  PROCEDURE InstallTermHandler* (h: TerminationHandler);
    VAR m: Module; adr: LONGINT; found: BOOLEAN;
  BEGIN
    m := modList; adr := SYS.VAL(LONGINT, h); found := FALSE;
    WHILE (m # NIL) & ~found DO
      IF (m.code <= adr) & (adr < m.codeLim) THEN found := TRUE
      ELSE m := m.link
      END
    END;
    IF found THEN m.term := h END;
  END InstallTermHandler;

  PROCEDURE TermModules();
    VAR m: Module; h: TerminationHandler;
  BEGIN
    m := modList;
    WHILE m # NIL DO
      IF m.term # NIL THEN h := m.term; m.term := NIL; h() END;
      m := m.link;
    END
  END TermModules;

(* Memory *)

  PROCEDURE- mark0()  008H, 0E9H, 000H, 000H, 0FFH, 0FFH; (*BSET.B #0, -1(A1)*)

  PROCEDURE* Mark1;
    VAR mod: Module;
  BEGIN mod:=modList;
    WHILE mod#NIL DO  SYS.PUTREG(9, mod.data); mark1;
      IF  mod.publics#0 THEN  SYS.PUTREG(9, mod.publics); mark0; mark1  END;
      IF  mod.privates#0  THEN  SYS.PUTREG(9, mod.privates); mark0; mark1 END;
      IF  mod.import#NIL  THEN  SYS.PUTREG(9, mod.import); mark0  END;
      IF  mod.struct#NIL  THEN  SYS.PUTREG(9, mod.struct); mark0  END;
      IF  mod.reimp#NIL THEN  SYS.PUTREG(9, mod.reimp); mark0 END;
      mod:=mod.link
    END
  END Mark1;

  PROCEDURE* Scan;
  BEGIN scan
  END Scan;


(* Keyboard Break *)

  PROCEDURE* ValidateBrk;
    VAR bpt, fp, applLimit: LONGINT; mod: Module;
  BEGIN SYS.GETREG(14, fp); SYS.GET(fp, fp); SYS.GET(fp, fp); SYS.GET(130H, applLimit);
    IF  (fp < applLimit) OR (fp >= Kernel.stackOrg) THEN  Kernel.theTrap.pc:=0; RETURN  END;
    SYS.GET(fp+36H, bpt); mod:=modList; (* Caller of Macintosh DEQUEUE routine *)
    LOOP
      LOOP
        IF  mod=NIL THEN  SYS.GET(fp, fp);
          IF  (fp < applLimit) OR (fp >= Kernel.stackOrg) THEN  Kernel.theTrap.pc:=0; RETURN  END;
          SYS.GET(fp+4, bpt); mod:=modList; EXIT  (* Not This Frame *)
        ELSIF (mod.code >= bpt) OR (mod.codeLim < bpt)  THEN  mod:=mod.link (* Check Next Module *)
        ELSE  Kernel.theTrap.pc:=bpt; RETURN  END (* Patch Instruction with TPT.W #22 *)
      END
    END
  END ValidateBrk;


(* Status Information *)

  PROCEDURE ShowFrame(base: LONGINT; global: BOOLEAN; showVar: Command);
    VAR mode, ch: CHAR; s: SHORTINT; i: INTEGER; sadr: LONGINT;
  BEGIN Kernel.BufRCh(B, mode);
    WHILE mode < 0FEX DO  theObj.class:=ORD(mode) MOD 10H; theObj.rdonly:=ODD(ORD(mode) DIV 10H);
      theObj.global:=global;
      Kernel.BufRNum(B, theObj.adr); Kernel.BufRString(B, theObj.name); INC(theObj.adr, base);
      IF  ODD(ORD(mode) DIV 20H)  THEN SYS.GET(theObj.adr, theObj.adr) (*indirect*) END;
      CASE  theObj.class  OF
      | 2:  SYS.GET(theObj.adr, theObj.boolval)
      | 3:  SYS.GET(theObj.adr, theObj.chval)
      | 4:  SYS.GET(theObj.adr, s); theObj.intval:=s
      | 5:  SYS.GET(theObj.adr, i); theObj.intval:=i
      | 6, 13:  SYS.GET(theObj.adr, theObj.intval)
      | 7:  SYS.GET(theObj.adr, theObj.rval)
      | 8:  SYS.GET(theObj.adr, theObj.lrlval)
      | 9:  SYS.GET(theObj.adr, theObj.setval)
      | 15: i:=0; sadr:=theObj.adr;
        LOOP  SYS.GET(sadr, ch);
          IF (ch < " ") OR (ch >= 90X) OR (i=31) THEN EXIT END;
          theObj.strval[i]:=ch; INC(i); INC(sadr)
        END;
        theObj.strval[i]:=0X; theObj.class:=10;
      ELSE  END;
      showVar(); Kernel.BufRCh(B, mode)
    END
  END ShowFrame;

  PROCEDURE EnumCommands*(mod: Module; showProc: Command);
  BEGIN theMod:=mod;
    IF  mod.comms#0 THEN  Kernel.SetBuf(B, mod.comms); Kernel.BufRString(B, theProc.name);
      WHILE theProc.name#"" DO  Kernel.BufRNum(B, theProc.adr); showProc(); Kernel.BufRString(B, theProc.name)  END
    ELSIF extended.EnumCmds#NIL THEN  extended.EnumCmds(mod, showProc)  END
  END EnumCommands;

  PROCEDURE EnumGlobals*(mod: Module; showVar: Command);
    VAR ch: CHAR; adr: LONGINT; name: ARRAY 32 OF CHAR;
  BEGIN theMod:=mod;
    IF  mod.refs#0  THEN  Kernel.SetBuf(B, mod.refs);
      LOOP  Kernel.BufRCh(B, ch);
        IF  ch=0FFX THEN  RETURN
        ELSIF ch=0FEX THEN  Kernel.BufRNum(B, adr); Kernel.BufRString(B, name); (* start proc *)
          IF  name="" THEN  ShowFrame(mod.data, TRUE, showVar); RETURN  END
        ELSIF ch < 0FEX THEN  Kernel.BufRNum(B, adr); Kernel.BufRString(B, name)  (* skip object *)
        END
      END
    ELSIF extended.EnumGlobs#NIL  THEN  extended.EnumGlobs(mod, showVar)  END
  END EnumGlobals;

  PROCEDURE EnumStkFrames*(showProc, showVar: Command);
    VAR adr: LONGINT; ch: CHAR;
  BEGIN theMod:=modList; theProc.fp:=Kernel.theTrap.fp; theProc.pc:=Kernel.theTrap.pc;
    WHILE (theMod#NIL)&((theMod.code >= theProc.pc) OR (theMod.codeLim <= theProc.pc))  DO  theMod:=theMod.link END;
    LOOP  theProc.relpc:=theProc.pc-theMod.code;
      IF  theMod.refs#0 THEN  Kernel.SetBuf(B, theMod.refs);
        LOOP  Kernel.BufRCh(B, ch);
          IF  ch=0FFX THEN  theProc.name:=""; showProc(); EXIT
          ELSIF ch=0FEX THEN  Kernel.BufRNum(B, adr); Kernel.BufRString(B, theProc.name); (* start proc *)
            IF  theProc.pc <= theMod.code+adr THEN  showProc();
              IF  theProc.name="" THEN  ShowFrame(theMod.data, TRUE, showVar) ELSE  ShowFrame(theProc.fp, FALSE, showVar) END;
              EXIT
            END
          ELSIF ch < 0FEX THEN  Kernel.BufRNum(B, adr); Kernel.BufRString(B, theObj.name) (* skip object *)
          END
        END
      ELSIF extended.EnumLocls#NIL  THEN  extended.EnumLocls(theMod, theProc.fp, theProc.pc, showProc, showVar) END;
      SYS.GET(theProc.fp+4, theProc.pc); SYS.GET(theProc.fp, theProc.fp);
      IF  theProc.fp > Kernel.stackOrg  THEN  EXIT  END;
      theMod:=modList;  (* find module of next procedure *)
      WHILE (theMod#NIL)&((theMod.code >= theProc.pc) OR (theMod.codeLim <= theProc.pc))  DO  theMod:=theMod.link END;
      IF  theMod=NIL  THEN  EXIT  END
    END
  END EnumStkFrames;

BEGIN
  SYS.GETREG(13, a5); SYS.GET(a5-24, modList); SYS.GET(a5-20, mark1); SYS.GET(a5-16, scan);
  Kernel.InstallQ(Kernel.mkQ, Mark1); Kernel.InstallQ(Kernel.scQ, Scan); Kernel.InstallQ(Kernel.brkQ, ValidateBrk);
  Kernel.InstallQ(Kernel.quitQ, TermModules); KeepCore;
  theMod:=ThisMod("Interchange")
END Modules.