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

MODULE Interchange; (*mf 11.11.94 / od Jan 95 / tk 30.6.96 *)

  (* 30.6.96  Method support (mfix) *)

  IMPORT
    TB, SYS:=SYSTEM, PLT:=OPLT, PLL:=OPLL, PLC:=OPLC, PLV:=OPLV, Kernel, Modules;

  TYPE
    CommandDesc = RECORD
      name: ARRAY 24 OF CHAR;
      offset: INTEGER
    END;

  CONST
    Var=1; Par=2; VarPar=3; Con=4; LProc=6; XProc=7; TypDynArr=8; TypArray=9; TypPointer=10; TypRecord=11;
    TypProcTyp=12; TProc = 14;
    Byte=1; Bool=2; Char=3; SInt=4; Int=5; LInt=6; Real=7; LReal=8; Set=9; String=10; Pointer=13; Comp=15; Array=2;
    DynArr = 3; Record = 4;
    Local=FALSE; Global=TRUE;
    Reg = 16; FReg = 18; Cond = 19;


  VAR
    KM : Modules.Module;
    KernelSB : LONGINT;
    verbose : BOOLEAN;
    verboseHook*: PROCEDURE (M: Modules.Module);
    FlushCache: PROCEDURE (adr, len: LONGINT);

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
      IF  n=Modules.fileNotFound  THEN  Str(" not found");
      ELSIF n=Modules.invalidObjFile  THEN  Str(" not a valid object file")
      ELSIF n=Modules.cmdNotFound THEN  Str(" not found")
      ELSIF n=Modules.modNotFound THEN  Str(" not found")
      ELSIF n=Modules.modInUse  THEN  Str(" in use")
      ELSIF n=Modules.libNotFound THEN  Str(" not found")
      ELSIF n=Modules.symNotFound THEN  Str(" symbols not found")
      END
    END
  END err;

  PROCEDURE^ Import(VAR B: Kernel.Buffer; M: Modules.Module);

  PROCEDURE BuildSym(VAR B: Kernel.Buffer; M: Modules.Module);  (*construct object list from buffer*)
    VAR nofEntries, adr, nofRecs : LONGINT; obj, fld: PLT.Object; ent: INTEGER; mnolev : SHORTINT; mod: Modules.Module;
  BEGIN Import(B, M);
    IF Modules.res=0 THEN M.nofstrc:=1; obj:=NIL;
      mod:=Modules.modList; WHILE mod#NIL DO mod.nofreimp:=0; mod:=mod.link END;
      PLT.ReadScope(B, M, 0, obj, Global);  M.publics:=SYS.VAL(LONGINT, obj);
      nofEntries:=1; adr:=0;  nofRecs:=-4;
      WHILE obj#NIL DO
        CASE obj.mode OF
        | Var: PLL.TypSize(obj.typ); PLL.Align(adr, PLL.Base(obj.typ)); obj.adr:=adr; obj.linkadr:=adr; INC(adr, obj.typ.size);
        | XProc: SYS.GET(M.entries+2*nofEntries, ent); obj.linkadr:=M.PC+ent*4; INC(nofEntries);
          IF nofEntries>127 THEN HALT(33) END; obj.adr:=0; PLL.ParamAdr(obj);
        | TypRecord: PLL.TypSize(obj.typ); obj.typ.tdadr:=nofRecs;
          DEC(nofRecs, 4); obj.linkadr:=-1; (* mfix *)
        | TypDynArr, TypArray, TypPointer, TypProcTyp: PLL.TypSize(obj.typ); obj.linkadr:=-1;
        | Con:
        ELSE
        END;
        obj:=obj.nxtobj
      END;
    END;
  END BuildSym;

  PROCEDURE Decorate*(M: Modules.Module); (*append object list to module descriptor*)
    VAR B: Kernel.Buffer; ch0, ch1: CHAR; i: INTEGER; fname: Modules.ModuleName; done: BOOLEAN; symSize: LONGINT;
  BEGIN
    IF M.publics=0 THEN
      IF  M.syms#0  THEN  Kernel.SetBuf(B, M.syms); BuildSym(B, M)
      ELSE
        i:=0; ch0:=M.name[0];
        WHILE ch0#0X DO fname[i]:=ch0; INC(i); ch0:=M.name[i] END;
        fname[i]:="."; fname[i+1]:="O"; fname[i+2]:="b"; fname[i+3]:="j"; fname[i+4]:=0X;
        Kernel.OpenBuf(B, fname, 511, done);
        IF done THEN Kernel.BufRCh(B, ch0);
          IF ch0=0BBX THEN Kernel.BufRCh(B, ch1);
            Kernel.BufRNum(B, symSize);
            IF  2+15+symSize>511  THEN  Kernel.CloseBuf(B); Kernel.OpenBuf(B, fname, 2+15+symSize, done);
              Kernel.BufSkip(B, 2); Kernel.BufRNum(B, symSize)
            END;
            BuildSym(B, M)
          ELSE err(Modules.invalidObjFile, M.name) END;
          Kernel.CloseBuf(B)
        ELSE err(Modules.symNotFound, M.name) END
      END
    END
  END Decorate;

  PROCEDURE Import(VAR B: Kernel.Buffer; M: Modules.Module);
    VAR name: Modules.ModuleName; iM: Modules.Module;
  BEGIN Kernel.BufRString(B, name); M.nofreimp:=0;
    WHILE (name#"")&(Modules.res=0) DO
      iM:=Modules.ThisMod(name);
      IF Modules.res=0 THEN Decorate(iM);
        IF Modules.res=0 THEN
          M.import[M.nofimp]:=SYS.VAL(LONGINT, iM);
          INC(M.nofimp);
          IF M.nofimp>=LEN(M.import^) THEN PLT.DoubleArr(M.import) END;
          INC(iM.refCnt); Kernel.BufRString(B, name)
        END
      END
    END
  END Import;

  PROCEDURE Unlink(mod: Modules.Module; all: BOOLEAN);
    VAR i: INTEGER; imp: Modules.Module;
  BEGIN i:=mod.nofimp;
    WHILE i > 0 DO  DEC(i); imp:=SYS.VAL(Modules.Module, mod.import[i]); DEC(imp.refCnt);
      IF all & (imp.refCnt=0) THEN Modules.Unload(imp, TRUE) END
    END
  END Unlink;

  PROCEDURE* Load(VAR B: Kernel.Buffer; M: Modules.Module);
    VAR globals, obj: PLT.Object;
      below, above, TS: LONGINT; CD : CommandDesc;
      m1 : Modules.Module; found : BOOLEAN;
      iname : ARRAY 32 OF CHAR; ch0, ch1 : CHAR; i, nofptrs, ent : INTEGER; null, sfSize : LONGINT;
      base, links, consize : LONGINT; gptrTab: ARRAY 1025 OF LONGINT; body: PROCEDURE; B1: Kernel.Buffer;
  BEGIN
    Kernel.BufRNum(B, sfSize); B1:=B; Kernel.BufSkip(B1, sfSize); Import(B, M);
    IF Modules.res=0 THEN
      M.nofstrc:=1; globals:=NIL;
      Kernel.BufRNum(B1, sfSize); Kernel.BufRNum(B1, below); Kernel.BufRNum(B1, above);
      Import(B1, M);
      m1:=Modules.modList; WHILE m1#NIL DO m1.nofreimp:=0; m1:=m1.link END;
      PLT.ReadScope(B, M, 0, globals, Global); B:=B1;
      IF Modules.res=0 THEN PLT.theMod:=M;
        PLL.Open; M.publics:=SYS.VAL(LONGINT, globals);
        PLT.ReadScope(B, M, 0, globals, Local); M.privates:=SYS.VAL(LONGINT, globals);  (*append*)
        PLC.Init;
        PLL.Traverse(SYS.VAL(PLT.Object, M.publics)); PLL.Traverse(globals);
        PLL.AllocGlobalVar(SYS.VAL(PLT.Object, M.publics), globals);  (* Calculates global Var Size : PLL.dsize *)
        PLL.AllocLinkTable(M.nofimp+1);

        Kernel.AllocBlock(M.block, -4*16384); (* Code *)
        PLL.PC:=M.block; M.PC:=M.block;

        PLV.Load(B, M, globals, below, above);
        IF  Modules.res=0 THEN
          M.codeSize:=SHORT(PLL.pc);
          Kernel.AdjustBlock(M.block, LONG(M.codeSize)*4);
          SYS.MOVE(SYS.ADR(PLL.code), M.block, LONG(M.codeSize)*4);

          i:=PLL.conx MOD 8; WHILE i>0 DO DEC(PLL.conx); PLL.constant[PLL.conx]:=0X; DEC(i) END;
          consize:=PLL.ConstLength - PLL.conx; M.conSize:=SHORT(consize);         (* Const *)
          Kernel.AllocBlock(base, -PLL.dsize - consize);
          SYS.MOVE(SYS.ADR(PLL.constant[PLL.conx]), base, consize);

          M.SB:=base+consize; links:=M.SB+PLL.linkTable;
          SYS.MOVE(SYS.ADR(KernelSB), links, 4); INC(links, 4);
          FOR i:=0 TO (M.nofimp-1) DO
            m1:=SYS.VAL(Modules.Module, M.import[i]);
            SYS.MOVE(SYS.ADR(m1.SB), links, 4); INC(links, 4)
          END;
          M.dataSize:=PLL.dsize;

          obj:=SYS.VAL(PLT.Object, M.privates);
          WHILE obj#NIL DO
            IF  obj.mode=XProc  THEN  obj.linkadr:=M.block+4*PLL.entry[obj.adr]; obj.lim:=obj.lim*4+M.block; obj.psize:=obj.lim-obj.linkadr;
            ELSIF obj.mode=LProc  THEN  obj.linkadr:=M.block+4*obj.adr; obj.lim:=obj.lim*4+M.block; obj.psize:=obj.lim-obj.linkadr;
            END;
            obj:=obj.nxtobj;
          END;

          M.nofTraps:=PLL.noftraps+1; Kernel.AllocBlock(M.traps, -4*PLL.noftraps); base:=M.traps; (* Traps *)
          i:=0; WHILE i<M.nofTraps-1 DO
            SYS.PUT(base, PLL.Traps[i].pc); INC(base, 2);
            SYS.PUT(base, PLL.Traps[i].no); INC(base, 2);
            INC(i)
          END;

          Kernel.AllocBlock(M.entries, -2*PLL.entno); SYS.PUT(M.entries, SHORT(PLV.body));                    (* Entries *)
          SYS.MOVE(SYS.ADR(PLL.entry[1]), M.entries+2, 2*(PLL.entno-1)); M.nofEntries:=PLL.entno;

          obj:=SYS.VAL(PLT.Object, M.privates); nofptrs:=0;           (* Collect Ptrs + Commands / Entries*)
          WHILE obj#NIL DO
            IF  (obj.mode=XProc)&(obj.par=NIL)&(obj.typ=PLT.notyp)  THEN  INC(M.nofCmds)  END;
            IF  obj.mode=Var  THEN  PLL.FindPtrs(obj.typ, obj.adr, gptrTab, nofptrs)  END;
            obj:=obj.nxtobj;
          END;

          (*
          Kernel.AllocBlock(M.commands, -M.nofCmds*SIZE(CommandDesc));      (* Commands *)
          obj:=SYS.VAL(PLT.Object, M.publics); i:=0;
          WHILE obj#NIL DO
            IF (obj.mode=XProc)&(obj.par=NIL)&(obj.typ=PLT.notyp) THEN
              COPY(obj.name, CD.name); CD.offset:=PLL.entry[obj.adr];
              SYS.MOVE(SYS.ADR(CD), M.commands+(i*SIZE(CommandDesc)),SIZE(CommandDesc));
              INC(i);
            END; obj:=obj.nxtobj;
          END;
          *)

          M.nofPtrs:=nofptrs; Kernel.AllocBlock(M.pointers, -nofptrs*4);          (* Ptrs + Init *)
          SYS.MOVE(SYS.ADR(gptrTab), M.pointers, nofptrs*4);
          null:=0; i:=0; WHILE  i<nofptrs DO
            SYS.GET(M.pointers+(i*4), TS); TS:=TS+M.SB; SYS.PUT(TS, null);
            INC(i);
          END;

          PLL.MakeTypeDescs(M.nofTds, M.typedescs, M);              (* Type Descriptors *)

          (*
          Kernel.AllocBlock(M.refs, -PLL.refSize); M.refSize:=PLL.refSize;            (* Ref Info *)
          SYS.MOVE(SYS.ADR(PLL.refs), M.refs, PLL.refSize);
          *)

          Kernel.CloseBuf(B); M.refCnt := 0;

          IF verbose & (verboseHook#NIL) THEN verboseHook(M) END;
          SYS.PUT(SYS.ADR(body), PLV.body*4+M.PC); SYS.PUT(SYS.ADR(body)+4, M.SB);
          FlushCache(M.PC, LONG(M.codeSize)*4+8);
          body();
          Modules.res:=0;
        ELSE  Kernel.DeAllocBlock(M.block); Unlink(M, FALSE); Kernel.CloseBuf(B);  Kernel.DeAllocBlock(SYS.VAL(LONGINT, M)) END
      ELSE  Unlink(M, FALSE); Kernel.CloseBuf(B);  Kernel.DeAllocBlock(SYS.VAL(LONGINT, M)) END;
    ELSE  Unlink(M, FALSE); Kernel.CloseBuf(B); Kernel.DeAllocBlock(SYS.VAL(LONGINT, M))  END;
  END Load;

(*
  PROCEDURE Time*;  (* Oberon.Call legt Ladezeit in M.blocksize ab *)
  VAR m : Modules.Module; name : Modules.ModuleName; S: Texts.Scanner;
  BEGIN
    Texts.OpenScanner(S, Oberon.Par.text, Oberon.Par.pos); Texts.Scan(S);
    IF S.class=Texts.Name THEN
      COPY(S.s, name);
      m:=Modules.modList;
      WHILE (m#NIL) & (m.name#name) DO m:=m.link END;
      IF m#NIL THEN
        Texts.WriteString(W, name); Texts.WriteString(W, " - Loading Time : ");
        Texts.WriteInt(W, m.blockSize, 5); Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf)
      END;
    END;
  END Time;
*)
  PROCEDURE ThisCmd(mod: Modules.Module; VAR name: ARRAY OF CHAR): Modules.Command;
    VAR obj: PLT.Object; cmd: Modules.Command;
  BEGIN obj:=SYS.VAL(PLT.Object, mod.publics);
    WHILE obj#NIL DO
      IF  (obj.name=name)&(obj.mode=XProc)&(obj.par=NIL)&(obj.typ=PLT.notyp)  THEN
        Modules.res:=0;
        SYS.PUT(SYS.ADR(cmd), obj.linkadr); SYS.PUT(SYS.ADR(cmd)+4, mod.SB);
        RETURN cmd
      END;
      obj:=obj.nxtobj
    END;
    err(Modules.cmdNotFound, name); SYS.PUT(SYS.ADR(cmd), LONG(LONG(0))); SYS.PUT(SYS.ADR(cmd)+4, LONG(LONG(0)));
    RETURN cmd
  END ThisCmd;

  PROCEDURE EnumCmds(mod: Modules.Module; showCmd: Modules.Command);
    VAR obj: PLT.Object;
  BEGIN obj:=SYS.VAL(PLT.Object, mod.publics);
    WHILE obj#NIL DO
      IF  (obj.mode=XProc)&(obj.par=NIL)&(obj.typ=PLT.notyp)  THEN
        Modules.theProc.adr:=obj.adr; COPY(obj.name, Modules.theProc.name); showCmd()
      END;
      obj:=obj.nxtobj
    END
  END EnumCmds;

  PROCEDURE EnumScope(obj: PLT.Object; base: LONGINT; global: BOOLEAN; showVar: Modules.Command);
    VAR s: SHORTINT; i: INTEGER; ch: CHAR; adr, mode, li: LONGINT; si: SHORTINT; lr: LONGREAL; regalloc: BOOLEAN;
  BEGIN
    WHILE obj#NIL DO
      IF  (obj.mode=Var) OR (obj.mode=Par) OR (obj.mode=VarPar) THEN
        adr:=obj.linkadr;
        IF  adr<0 THEN
          adr:=-1-adr; mode:=adr DIV 32; adr:=adr MOD 32;
          IF  obj.mode=VarPar THEN  Modules.theObj.reg:=adr; adr:=Kernel.theRegSet.reg.R[2*adr+1]; regalloc:=FALSE;
          ELSE
            IF  mode=Reg  THEN  Modules.theObj.reg:=adr; adr:=SYS.ADR(Kernel.theRegSet.reg.R[2*adr+1]); regalloc:=TRUE
            ELSIF mode=FReg THEN  Modules.theObj.reg:=adr+256; adr:=SYS.ADR(Kernel.theRegSet.fp.R[2*adr]); regalloc:=TRUE
            ELSIF adr IN SYS.VAL(SET, Kernel.theRegSet.spec.CR) THEN  Modules.theObj.boolval:=TRUE
            ELSE  Modules.theObj.boolval:=FALSE
            END
          END
        ELSE  adr:=adr+base; regalloc:=FALSE
        END;

        IF  regalloc & (obj.typ.form IN {Byte, Bool, Char}) THEN  INC(adr, 3) END;
        Modules.theObj.adr:=adr; Modules.theObj.class:=obj.typ.form; Modules.theObj.global:=global; SYS.GET(adr, li);
        COPY(obj.name, Modules.theObj.name);
        CASE  obj.typ.form  OF
        | Byte: SYS.GET(adr, Modules.theObj.chval);
        | Char: SYS.GET(adr, Modules.theObj.chval)
        | Bool: IF  (mode=Reg) OR ~regalloc THEN  SYS.GET(adr, Modules.theObj.boolval)  END;
        | SInt: IF  ~regalloc THEN  SYS.GET(adr, si); Modules.theObj.intval:=si ELSE  Modules.theObj.intval:=li END
        | Int:  IF  ~regalloc THEN  SYS.GET(adr, i); Modules.theObj.intval:=i ELSE  Modules.theObj.intval:=li END
        | LInt, Pointer:  Modules.theObj.intval:=li
        | Real: IF  regalloc  THEN  SYS.GET(adr, lr); Modules.theObj.rval := SHORT(lr)  ELSE  SYS.GET(adr, Modules.theObj.rval) END;
        | LReal:  SYS.GET(adr, Modules.theObj.lrlval);
        | Set:  Modules.theObj.setval:=SYS.VAL(SET, li);
        | Comp:
          IF  (obj.typ.comp=Array)&(obj.typ.BaseTyp.form=Char)  THEN
            i := 1; SYS.GET(adr, ch);
            WHILE (i < 128) & (ch # 0X) DO Modules.theObj.strval[i-1]:=ch; SYS.GET(adr+i, ch); INC(i) END;
            Modules.theObj.strval[i-1]:=0X; Modules.theObj.class:=String;
          ELSE  Modules.theObj.intval:=SYS.VAL(LONGINT, obj.typ)
          END
        ELSE  END;
        showVar()
      END;
      obj:=obj.nxtobj
    END
  END EnumScope;

  PROCEDURE EnumGlobs(mod: Modules.Module; showVar: Modules.Command);
  BEGIN Modules.theObj.rdonly:=FALSE; EnumScope(SYS.VAL(PLT.Object, mod.privates), mod.SB, TRUE, showVar)
  END EnumGlobs;

  PROCEDURE EnumLocls(mod: Modules.Module; VAR sp, pc: LONGINT; showProc: Modules.Command; showVar: Modules.Command);
    VAR obj: PLT.Object; ralloc, falloc, calloc, base: LONGINT; leaf: BOOLEAN;
  BEGIN obj:=SYS.VAL(PLT.Object, mod.privates); Modules.theProc.pc:=pc; Modules.theProc.sp:=sp; Modules.theProc.relpc:=pc-mod.PC;
    LOOP
      IF  obj=NIL THEN
        COPY("$$", Modules.theProc.name); showProc();
        ralloc:=30; falloc:=31; calloc:=19; leaf:=FALSE;
        EnumGlobs(mod, showVar);
        EXIT
      ELSIF (obj.mode IN {LProc, XProc})&(obj.linkadr < pc)&(obj.lim > pc)  THEN
        COPY(obj.name, Modules.theProc.name); showProc();
        ralloc:=(obj.ival DIV 1024) MOD 32; falloc:=(obj.ival DIV 32) MOD 32; calloc:=obj.ival MOD 32; leaf:=obj.leaf;
        EnumScope(obj.locals, Kernel.theRegSet.reg.R[31*2+1], FALSE, showVar);
        EXIT
      END;
      obj:=obj.nxtobj
    END;

    SYS.GET(sp, sp);
    IF  leaf  THEN  pc := Kernel.theRegSet.spec.LR  ELSE  SYS.GET(sp+8, pc) END;
    base := sp-(31-ralloc)*4;
    WHILE ralloc < 31 DO  INC(ralloc); SYS.GET(base, Kernel.theRegSet.reg.R[2*ralloc+1]); INC(base, 4)  END;
    INC(base, (-base) MOD 8);
    WHILE falloc < 31 DO  INC(falloc); SYS.GET(base, Kernel.theRegSet.fp.R[2*falloc+1]); INC(base, 8) END;
    IF  calloc < 19 THEN  SYS.GET(sp+4, Kernel.theRegSet.spec.CR) END
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

  PROCEDURE StackInitOn*;
  BEGIN PLC.initstack := TRUE
  END StackInitOn;

  PROCEDURE StackInitOff*;
  BEGIN PLC.initstack := FALSE
  END StackInitOff;

BEGIN
  TB.Assign("MakeDataExecutable", SYS.ADR(FlushCache));
  PLC.inxchk:=TRUE; PLC.typchk:=TRUE; PLC.nilchk:=TRUE; PLC.ptrinit:=TRUE;
  KM:=Modules.ThisMod("Kernel"); KernelSB:=KM.SB;
  Modules.extended.Load:=Load; Modules.extended.Unlink:=Unlink; Modules.extended.ThisCmd:=ThisCmd;
  Modules.extended.EnumCmds:=EnumCmds; Modules.extended.EnumGlobs:=EnumGlobs; Modules.extended.EnumLocls:=EnumLocls;
END Interchange.