(* ETH Oberon, Copyright 2000 ETH Zürich Institut für Computersysteme, ETH Zentrum, CH-8092 Zürich.
Refer to the general ETH Oberon System license contract available at: http://www.oberon.ethz.ch/ *)

MODULE Modules; (** portable, except where noted / source: PPC.Modules.Mod *)
(*! Int _>Long (needs changes of 044X format. CodeSize is read using Kernel.BufRBytes(B, m.codeSize, 2); *)
  IMPORT SYS:=SYSTEM, TB, Kernel;

  CONST
    (* error messages *)
    done* = 0; fileNotFound* = 1; invalidObjFile* = 2; invalidKey* = 3;
    cmdNotFound* = 5; modNotFound* = 6; cyclicImport* = 7;
    modInUse* = 10; libNotFound* = 11; symNotFound* = 15;

    (* compiler constants, instruction formats *)
    MaxExts = 16;  MaxLinks = 250; MaxRecs = 230; nil = 0; MaxImports = 31;
    SYSMTag = -1; LinkMTag = -2; CaseETag = -2; NewRecETag = -1; NewSysETag = -2; NewArrETag = -3;
    iCAL = 038000000H; iCAU = 03C000000H; iBL = 048000001H; iBLmask = 03FFFFFCH; niBLmask = 0FC000003H; TagMask=0FFFFFFFEH;

    (* export/use section *)
    EUEnd = 0; EURecord = 1; EUobjScope = 0; EUrecScope = 1;  EUerrScope = -1; EUProcFlag = 80000000H; EUTypFlag = 0C0000000H;

    (* object file tags *)
    EntryMark = 82X; CommandMark = 83X; PointerMark=84X; ImportMark=85X;
    LinkMark=86X; DataMark=87X; ExportMark=88X; CodeMark=89X; UseMark=8AX; TypeMark=8BX; TrapMark=8CX; RefMark=8DX;

    (* symbols *)
    Reg = 16; FReg = 18; Cond = 19;
    Undef = 0; Byte = 1; Bool = 2; Char = 3; SInt = 4; Int = 5; LInt = 6; Real = 7; LReal = 8; Set = 9; String = 10;
    NilTyp = 11; NoTyp = 12; Pointer = 13; ProcTyp = 14; Comp = 15;

    ModNameLen* = 32;

    DefMaxImport=64; DefMaxStruct=32; DefMaxReimp=32;


  TYPE
    Command* = PROCEDURE;
    CommandName = ARRAY 24 OF CHAR;
    CommandPtr = POINTER TO CommandDesc;
    CommandDesc = RECORD  name: CommandName; offset: INTEGER  END;

    TrapDescPtr = POINTER TO TrapDesc;
    TrapDesc = RECORD offset, trapno: INTEGER END;

    ExportPtr* = POINTER TO ExportDesc;
    ExportDesc* = RECORD
      fp*: LONGINT; adr*: LONGINT;
      nofExp*: INTEGER; dsc*: LONGINT; (* ExportPtr *)
    END;

    ArrayPtr* = POINTER TO ARRAY OF LONGINT;

    TerminationHandler* = Kernel.Handler;

    Module* = POINTER TO ModDesc;
    ModuleName* = ARRAY ModNameLen OF CHAR;
    ModDesc* = RECORD
      link*: Module;
      name*: ModuleName;
      key*: LONGINT; refCnt*: INTEGER;
      dataSize*, blockSize*, refSize*: LONGINT;
      conSize*, codeSize*, nofEntries*, nofCmds*, nofImps*, nofTds*, nofPtrs*, nofTraps*: INTEGER;
      block*, SB*, PC* : LONGINT;
      entries* : LONGINT; (* POINTER TO ARRAY OF INTEGER; *)
      commands* : LONGINT;
      imports* : LONGINT; (* POINTER TO ARRAY OF LONGINT; *)
      typedescs*: LONGINT;
      pointers*: LONGINT;
      traps*: LONGINT;  (* POINTER TO ARRAY OF TrapDesc; *)
      refs*: LONGINT; (* POINTER TO ARRAY OF CHAR *)
      syms*: LONGINT; (* POINTER TO ARRAY OF CHAR *);
      publics*, privates* : LONGINT;
      nofimp*: INTEGER; import*: ArrayPtr;  (*for native modules, nofimp counts only re_exported imports*)
      nofstrc* : INTEGER; struct* : ArrayPtr; (*for portable modules, nofimp counts all imports, imodTab set to zero*)
      nofreimp*: INTEGER; reimp*: ArrayPtr;
      export*: ExportDesc;
      term*: TerminationHandler;
    END;

    Tag = POINTER TO TypeDesc;
    TypeDesc = RECORD
      (* ProcedureDesc methods starrting at -8-MaxExts*4 in negative direction *)
      (* LONGINT basetags starting at -8 in negative direction *)
      (* Tag at -4 *)
      size: LONGINT;
      ptroff: LONGINT;  (* array terminated by -4-nofptr*4 *)
    END;

    SuperTag = POINTER TO SuperDesc;
    SuperDesc = RECORD
      tdsize, ptroff: LONGINT;  (* ptroff contains always -4 *)
      tag: Tag;
      pad: ARRAY 3 OF SHORTINT;
      ext0: SHORTINT;
      name: ARRAY 32 OF CHAR;
      mod: Module;
    END;

    LinkEntry = RECORD
      mod, ent: SHORTINT;
      offset: INTEGER;
    END;

  VAR
    res*: INTEGER; resMsg*: ARRAY 256 OF CHAR;
    resMsgLen*: INTEGER; modList*: Module;

    extended*: RECORD
      Load*: PROCEDURE(VAR buf: Kernel.Buffer; mod: Module);
      Unlink*: PROCEDURE(mod: Module; all: BOOLEAN);
      ThisCmd*: PROCEDURE(mod: Module; VAR name: ARRAY OF CHAR): Command;
      EnumCmds*: PROCEDURE(mod: Module; showCmd: Command);
      EnumGlobs*: PROCEDURE(mod: Module; showVar: Command);
      EnumLocls*: PROCEDURE(mod: Module; VAR sp, pc: LONGINT; showProc, showCmd: Command);
    END;
    theMod*: Module;
    theProc*: RECORD name*: ModuleName; adr*, pc*, relpc*, sp*: LONGINT END;
    theObj*: RECORD name*: ModuleName; adr*: LONGINT; reg*: LONGINT; class*: INTEGER; global*, rdonly*, boolval*: BOOLEAN; chval*: CHAR; intval*: LONGINT; setval*: SET; rval*: REAL; lrlval*: LONGREAL; strval*: ARRAY 128 OF CHAR END;
    oldTrap: TB.ExceptionHandler;
    FPURegProcs: RECORD SaveFProc, RestFProc: LONGINT END;
    FlushCache: PROCEDURE (adr, len: LONGINT);
    brkinstr: LONGINT; dbgInstalled: BOOLEAN;

(** Returns a handle to an already loaded module. *)
PROCEDURE FindMod*(VAR modname: ARRAY OF CHAR): Module; (** non-portable *)
(*! make fail-safe *)
  VAR m: Module;
BEGIN
(*  EnterCriticalSection();*)
  m := modList;
  WHILE (m # NIL) & (m.name # modname) DO
    m := m.link
  END;
(*  LeaveCriticalSection();*)
  RETURN m
END FindMod;

  (* ----- auxiliaries ----- *)

  PROCEDURE ^ ThisCommand* (mod: Module; name: ARRAY OF CHAR): Command;
  PROCEDURE BootCommand(mod: Module; name: ARRAY OF CHAR; VAR cmd: Command);
  BEGIN cmd:=ThisCommand(mod, name);
  END BootCommand;

  PROCEDURE SetTag(adr: LONGINT; tag: LONGINT); (* Set tag of record at offset -4 *)
  BEGIN SYS.PUT(adr-4, tag);
  END SetTag;

  PROCEDURE GetTag(adr: LONGINT): Tag;  (* Get tag of record at offset -4 *)
    VAR t: Tag;
  BEGIN SYS.GET(adr-4, t); RETURN t;
  END GetTag;

  PROCEDURE SetPtr(tag: Tag; nr: INTEGER; val: LONGINT);  (* Set pointer nr in typedesc tag *)
  BEGIN SYS.PUT(SYS.ADR(tag.ptroff)+4*nr, val);
  END SetPtr;

  PROCEDURE SetMeth(tag: Tag; nr: INTEGER; off: INTEGER; val: LONGINT); (* Set methodfield  / 0=PC / 4=SB *)
  BEGIN SYS.PUT(SYS.VAL(LONGINT, tag)-12-(MaxExts+nr*2)*4+off, val);
  END SetMeth;

  PROCEDURE GetMeth(tag: Tag; nr, off: INTEGER): LONGINT; (* Get methodfield off in typdesc tag *)
    VAR m: LONGINT;
  BEGIN SYS.GET(SYS.VAL(LONGINT, tag)-12-(MaxExts+nr*2)*4+off, m); RETURN m;
  END GetMeth;

  PROCEDURE SetBase(tag: Tag; nr: INTEGER; val: LONGINT); (* Set basetype nr in typedesc tag *)
  BEGIN SYS.PUT(SYS.VAL(LONGINT, tag)-(2+nr)*4, val);
  END SetBase;

  PROCEDURE GetBase(tag: Tag; nr: INTEGER): LONGINT;  (* Get basetype nr in typedesc tag *)
    VAR t: LONGINT;
  BEGIN SYS.GET(SYS.VAL(LONGINT, tag)-(2+nr)*4, t); RETURN t;
  END GetBase;

  PROCEDURE And(x, y: LONGINT): LONGINT;
  BEGIN RETURN SYS.VAL(LONGINT, SYS.VAL(SET, x) * SYS.VAL(SET, y));
  END And;

  PROCEDURE Or(x, y: LONGINT): LONGINT;
  BEGIN RETURN SYS.VAL(LONGINT, SYS.VAL(SET, x) + SYS.VAL(SET, y));
  END Or;

  PROCEDURE Instr16(x: LONGINT): LONGINT;
  BEGIN RETURN And(x,  0FFFF0000H);
  END Instr16;

  PROCEDURE Disp16(x: LONGINT): LONGINT;
  BEGIN RETURN ASH(ASH(x, 16), -16);
  END Disp16;

  PROCEDURE Split(x: LONGINT; VAR u, l: LONGINT);
  BEGIN u:=And(ASH(x, -16) + And(ASH(x, -15), 1), 0FFFFH); l:=And(x, 0FFFFH);
  END Split;

  PROCEDURE Instr26(x: LONGINT): LONGINT;
  BEGIN RETURN And(x, niBLmask);
  END Instr26;

  PROCEDURE Disp26(x: LONGINT): LONGINT;
  BEGIN RETURN ASH(ASH(x, 6), -8);
  END Disp26;

  PROCEDURE Opcode(x: LONGINT): LONGINT;
  BEGIN RETURN And(x, 0FC000000H);
  END Opcode;

  PROCEDURE Align8(x: LONGINT): LONGINT;
  BEGIN RETURN x+ (-x) MOD 8;
  END Align8;


  (* ----- error messages ----- *)

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
      IF  res=fileNotFound  THEN  Str(" not found");
      ELSIF res=invalidObjFile  THEN  Str(" not a valid object file")
      ELSIF res=cmdNotFound THEN  Str(" not found")
      ELSIF res=modNotFound THEN  Str(" not found")
      ELSIF res=modInUse  THEN  Str(" in use")
      ELSIF res=libNotFound THEN  Str(" not found")
      ELSIF res=symNotFound THEN  Str(" symbols not found")
      ELSIF res=cyclicImport  THEN  Str(" cyclic imported")
      END
    END
  END err;

  (* ----- unloading modules ----- *)

  PROCEDURE Delete(m: Module);
    VAR m0: Module;
  BEGIN m0:=modList;
    IF m0=m THEN modList:=m.link
    ELSE
      WHILE m0.link#m DO m0:=m0.link END;
      m0.link:=m.link;
    END;
  END Delete;

  PROCEDURE Unload*(m: Module; all: BOOLEAN);
    VAR imp: Module; i: LONGINT;
  BEGIN i:=m.nofImps;
    IF  i>0 THEN  (* native module *)
      WHILE i>0 DO DEC(i); SYS.GET(m.imports+4*i, imp); DEC(imp.refCnt);
        IF all & (imp.refCnt=0) THEN Unload(imp, all) END;
      END;
    ELSIF (i<0) & (extended.Unlink#NIL) THEN  extended.Unlink(m, all) END;
    Delete(m);
  END Unload;

  (* Free a module from memory. Only modules with no clients can be freed. The all flag requests that all imported modules should be freed too (i.e. a recursive call to Free). *)
  PROCEDURE Free* (name: ARRAY OF CHAR; all: BOOLEAN);
    VAR h: TerminationHandler; m: Module;
  BEGIN m:=modList;
    WHILE (m#NIL) & (m.name#name) DO m:=m.link END;
    IF m=NIL THEN res:=modNotFound
    ELSIF m.refCnt#0 THEN res:=modInUse
    ELSE
      IF m.term # NIL THEN h := m.term; m.term := NIL; h() END;
      Unload(m, all); res:=done
    END;
  END Free;


  (* ----- commands ----- *)

  (** Returns a procedure variable representing an exported command in a module. Calling this procedure, executes the command. *)
  PROCEDURE ThisCommand* (mod: Module; name: ARRAY OF CHAR): Command;
    VAR i: LONGINT; cmdPtr: CommandPtr; cmd: Command;
  BEGIN
    IF  mod.nofImps>=0  THEN
      i:=mod.nofCmds;
      WHILE i>0 DO DEC(i);
        cmdPtr:=SYS.VAL(CommandPtr, mod.commands+i*SIZE(CommandDesc));
        IF cmdPtr.name=name THEN res:=done;
          SYS.PUT(SYS.ADR(cmd), mod.PC+cmdPtr.offset*4); SYS.PUT(SYS.ADR(cmd)+4, mod.SB);
          RETURN cmd
        END
      END;
      SYS.PUT(SYS.ADR(cmd), LONG(LONG(0))); SYS.PUT(SYS.ADR(cmd)+4, LONG(LONG(0)));
      err(cmdNotFound, name);
    ELSIF extended.ThisCmd#NIL  THEN  cmd:=extended.ThisCmd(mod, name)  END;
    RETURN cmd;
  END ThisCommand;


  (* ----- module loading ----- *)

  PROCEDURE ^ ThisMod*(name: ARRAY OF CHAR): Module;

  PROCEDURE FixupObj(code, link: LONGINT; fixval: LONGINT);
    VAR instr, nextlink, u, l: LONGINT;
  BEGIN
    REPEAT
      SYS.GET(code+link*4, instr);
      IF Instr26(instr)=iBL THEN
        nextlink:=-Disp26(instr);
        instr:=Instr26(instr);
        l:=fixval-(code+link*4);
        SYS.PUT(code+link*4, Or(And(l, iBLmask), instr));
      ELSIF Opcode(instr)=iCAU THEN
        nextlink:=-Disp16(instr); instr:=Instr16(instr); Split(fixval, u, l);
        SYS.PUT(code+link*4, Or(instr, u));
        SYS.GET(code+link*4+4, instr); instr:=Instr16(instr);
        SYS.PUT(code+link*4+4, Or(instr, l));
      END;
      link:=nextlink
    UNTIL link=0;
  END FixupObj;

  PROCEDURE Fixup(mod: Module; links: ARRAY OF LinkEntry; noflinks: INTEGER; tdadr: ARRAY OF INTEGER; linktbl: LONGINT);
    VAR h, i, len, link, nextlink, instr, fixval, u, l, basemod, baseadr, data, code: LONGINT;
    entry: LinkEntry; ent: INTEGER;
    basetag, tag: Tag; supertag: SuperTag;
    m: Module;
    j, entno, nofmth: INTEGER;
    kernel: Module; cont: BOOLEAN;
  BEGIN
    (* Fixup link table *)
    data:=mod.SB+linktbl;
    kernel:=ThisMod("Kernel"); SYS.PUT(data, kernel.SB);
    i:=0; WHILE i<mod.nofImps DO INC(data, 4); SYS.GET(mod.imports+i*4, m);
      SYS.PUT(data, m.SB); INC(i)
    END;

    (* Fixup type descs *)
    data:=mod.SB;
    i:=0; WHILE i<mod.nofTds DO cont:=FALSE;
      SYS.GET(data+tdadr[i], tag); j:=0;
      h:=SYS.VAL(LONGINT, GetBase(tag, 0)); basemod:=h DIV 10000H; baseadr:=ASH(ASH(h, 16), -16);
      IF basemod>=0 THEN
        IF basemod=0 THEN (* this mod *)
          m:=mod;
          j:=0; WHILE (j<mod.nofTds) & (tdadr[j]#baseadr) DO INC(j) END;
          IF j>i THEN entno:=tdadr[i]; tdadr[i]:=tdadr[j]; tdadr[j]:=entno; cont:=TRUE;
          END;  (* swap to get correct initialization order *)
        ELSE  SYS.GET(mod.imports+(basemod-1)*4, m)
        END;
        IF ~cont THEN SYS.GET(m.SB+baseadr, basetag); j:=0;
          h:=GetBase(basetag, j); SetBase(tag, j, h);   (* copy tags *)
          WHILE h#nil DO INC(j); h:=GetBase(basetag, j); SetBase(tag, j, h) END;
        END;
      END;
      IF ~cont THEN
        SetBase(tag, j, SYS.VAL(LONGINT, tag)); (* points to itself *)
        supertag:=SYS.VAL(SuperTag, And(SYS.VAL(LONGINT, GetTag(SYS.VAL(LONGINT, tag))), TagMask));
        supertag.ext0:=SHORT(j); INC(j);
        WHILE j<MaxExts DO SetBase(tag, j, nil); INC(j) END;
        nofmth:=supertag.pad[0]; supertag.pad[0]:=0;
        j:=0;
        WHILE j<nofmth DO
          entno:=SHORT(GetMeth(tag, j, 0));
          IF entno<0 THEN (* inherited *)
            h:=GetMeth(basetag, j, 0); SetMeth(tag, j, 0, h);
            h:=GetMeth(basetag, j, 4); SetMeth(tag, j, 4, h);
          ELSE (* overwritten *)
            SYS.GET(mod.entries+entno*2, ent);
            SetMeth(tag, j, 0, ent*4+mod.PC);
            SetMeth(tag, j, 4, mod.SB);
          END;
          INC(j);
        END;
        INC(i);
      END;
    END;

    (* fixup code section *)
    code:=mod.PC;
    i:=0; WHILE i<noflinks DO
      entry:=links[i];
      IF (entry.mod=LinkMTag) & (entry.ent=CaseETag) THEN
        link:=entry.offset DIV 4;
        REPEAT
          SYS.GET(data+link*4, nextlink); nextlink:=ASH(nextlink, -18);
          SYS.GET(data+link*4+4, instr); instr:=ASH(instr, -16);
          WHILE instr>=0 DO
            SYS.GET(data+link*4+instr*4, h); h:=And(h, 0FFFFH)*4 + code; SYS.PUT(data+link*4+instr*4, h);
            DEC(instr);
          END;
          link:=nextlink;
        UNTIL link=0;
      ELSE (* fixup procedure calls or assignments *)
        IF entry.mod=SYSMTag THEN
          IF entry.ent=NewRecETag THEN fixval:=SYS.VAL(LONGINT, Kernel.newRec)
          ELSIF entry.ent=NewSysETag THEN fixval:=SYS.VAL(LONGINT, Kernel.newSys);
          ELSIF entry.ent=NewArrETag THEN fixval:=SYS.VAL(LONGINT, Kernel.newArr);
          ELSIF entry.ent<33 THEN fixval:=FPURegProcs.SaveFProc+entry.ent*4;
          ELSIF (32<entry.ent) & (entry.ent<65) THEN fixval:=FPURegProcs.RestFProc+(entry.ent-32)*4;
          END;
        ELSIF entry.mod=0 THEN SYS.GET(mod.entries+entry.ent*2, ent); fixval:=ent*4+mod.PC;
        ELSE HALT(99); SYS.GET(mod.imports+(entry.mod-1)*4, m); (* this case should never occure *)
          SYS.GET(m.entries+entry.ent*2, ent); fixval:=ent*4+m.PC;
        END;
        link:=-entry.offset;
        FixupObj(code, link, fixval);
      END;
      INC(i);
    END;
  END Fixup;

  PROCEDURE FindTDescAdr(M: Module; fp: LONGINT; VAR adr: LONGINT);
    VAR elem: ExportPtr; dsc: LONGINT; i: INTEGER;
  BEGIN
    dsc:=M.export.dsc; elem:=SYS.VAL(ExportPtr, dsc);
    i:=0; WHILE (i<M.export.nofExp) & (elem.fp#fp) DO INC(i); elem:=SYS.VAL(ExportPtr, dsc+i*SIZE(ExportDesc)) END;
    IF i<M.export.nofExp THEN elem:=SYS.VAL(ExportPtr, elem.dsc); adr:=-elem.adr ELSE adr:=0 END;
  END FindTDescAdr;

  PROCEDURE LoadExpBlock(VAR B: Kernel.Buffer; M: Module);
    VAR struct: ARRAY 1024 OF ExportPtr; nofStr: INTEGER;

    PROCEDURE LoadScope(VAR scope: ExportDesc; level: INTEGER; adr: LONGINT);
      VAR no, no2: INTEGER; fp, off: LONGINT; dsc, elem: ExportPtr;
    BEGIN
      Kernel.BufRBytes(B, scope.nofExp, 2); no:=0; no2:=0;
      Kernel.AllocBlock(scope.dsc, -SIZE(ExportDesc)*scope.nofExp);
      dsc:=SYS.VAL(ExportPtr, scope.dsc); dsc.adr:=adr;
      IF level=EUrecScope THEN INC(nofStr); struct[nofStr]:=SYS.VAL(ExportPtr, SYS.ADR(scope)) END;
      Kernel.BufRNum(B, fp);
      WHILE fp#EUEnd DO
        IF fp=EURecord THEN Kernel.BufRNum(B, off);
          elem:=SYS.VAL(ExportPtr, SYS.VAL(LONGINT, dsc)+no2*SIZE(ExportDesc));
          IF off<0 THEN elem.nofExp:=struct[-off].nofExp; elem.dsc:=struct[-off].dsc;   (* old type *)
          ELSE LoadScope(elem^, EUrecScope, off) END;
        ELSE
          elem:=SYS.VAL(ExportPtr, SYS.VAL(LONGINT, dsc)+no*SIZE(ExportDesc));
          IF level=EUobjScope THEN Kernel.BufRNum(B, elem.adr) END;
          elem.fp:=fp; no2:=no; INC(no)
        END;
        Kernel.BufRNum(B, fp);
      END;
    END LoadScope;

  BEGIN nofStr:=0; LoadScope(M.export, EUobjScope, 0)
  END LoadExpBlock;

  PROCEDURE CheckUseBlock(VAR B: Kernel.Buffer; M: Module);
    VAR mod: Module; name: ModuleName;

    PROCEDURE Err;
    BEGIN
      IF res=0 THEN Str(M.name); Str(" imports incompatible version of "); Str(mod.name); Str(": "); res:=16
      ELSE Ch(9X) END;
    END Err;

    PROCEDURE CheckScope(scope: ExportDesc; level: INTEGER);
      VAR fp, link, i, tdadr, dsc: LONGINT; elem, tadr: ExportPtr; tmpErr: BOOLEAN;
    BEGIN tmpErr:=(level=EUerrScope);
      dsc:=scope.dsc; i:=0;
      Kernel.BufRNum(B, fp);
      WHILE fp#EUEnd DO
        IF fp=EURecord THEN Kernel.BufRNum(B, link);
          elem:=SYS.VAL(ExportPtr, dsc+i*SIZE(ExportDesc));
          IF tmpErr THEN CheckScope(elem^, EUerrScope)
          ELSE
            IF link#0 THEN tadr:=SYS.VAL(ExportPtr, elem.dsc);
              SYS.GET(mod.SB-tadr.adr, tdadr); SYS.PUT(M.SB-link, tdadr);  (* tdadr at tadr[0] *)
            END;
            CheckScope(elem^, EUrecScope);
          END;
        ELSE Kernel.BufRString(B, name);
          IF level>=EUobjScope THEN tmpErr:=FALSE;
            IF level=EUobjScope THEN Kernel.BufRNum(B, link) END;
            elem:=SYS.VAL(ExportPtr, dsc);
            i:=0; WHILE (i<scope.nofExp) & (elem.fp#fp) DO INC(i); elem:=SYS.VAL(ExportPtr, dsc+i*SIZE(ExportDesc)) END;
            IF i>=scope.nofExp THEN Err; tmpErr:=TRUE; Ln; Ch(9X);
              IF name="@" THEN Str("RECORD ")
              ELSE Str(name) END; Str(" incompatible");
            ELSIF (level=EUobjScope) & (link#0) THEN
              IF And(link, EUProcFlag)=0 THEN SYS.PUT(M.SB-link, mod.SB+elem.adr) (* FixupObj(M.PC, link, elem.adr) *)
              ELSE FixupObj(M.PC, link-EUProcFlag, elem.adr*4+mod.PC) END;
            END
          END
        END;
        Kernel.BufRNum(B, fp);
      END;
    END CheckScope;

  BEGIN Kernel.BufRString(B, name);
    WHILE (name#"") & (res=0) DO
      mod:=ThisMod(name);
      IF res=0 THEN CheckScope(mod.export, EUobjScope);
      END;
      Kernel.BufRString(B, name);
    END;
  END CheckUseBlock;

  (** Returns a handle to an already loaded module, or loads a module and all its imported modules. *)
  PROCEDURE ThisMod*(name: ARRAY OF CHAR): Module;
    VAR B: Kernel.Buffer; ch, ch0, ch1: CHAR; fname: ARRAY 40 OF CHAR; m, m0: Module; i, mno, j: SHORTINT; found: BOOLEAN;
      size, baseadr: LONGINT; links: ARRAY MaxLinks OF LinkEntry; nofLinks, lnkTbl: INTEGER;
      code, entries, commands, imports, typedescs, pointers, traps, refs, adr, lastadr: LONGINT;
      cmd: CommandPtr; mname: ModuleName;
      tdadr: ARRAY MaxRecs OF INTEGER; imp: Module;
      basemod, nofmth, nofinhmth, nofnewmth, nofptr, mthno, entno, ent: INTEGER;
      supertag: SuperTag; tag: Tag; body: Command;

    PROCEDURE Check(tag: CHAR);
    BEGIN Kernel.BufRCh(B, ch); IF ch#tag THEN res:=invalidObjFile END;
    END Check;

    PROCEDURE AllocTypeDescriptor(recsize, nofmth, nofptr: INTEGER);
      VAR size, negpart: LONGINT; i: INTEGER; st: LONGINT;
    BEGIN
      negpart:=nofmth*SIZE(Command)+(MaxExts+2)*4;
      size:=4+SIZE(SuperDesc)+negpart+SIZE(TypeDesc)+nofptr*4;
      Kernel.AllocBlock(st, -size); supertag:=SYS.VAL(SuperTag, st+4);
      SetTag(SYS.VAL(LONGINT, supertag), Or(SYS.VAL(LONGINT, supertag), 1));
      tag:=SYS.VAL(Tag, SYS.VAL(LONGINT, supertag)+SIZE(SuperDesc)+negpart);
      supertag.tdsize:=SIZE(TypeDesc)+nofptr*4+negpart;
      supertag.ptroff:=-4; supertag.tag:=tag; supertag.pad[0]:=SHORT(nofmth);
      SetTag(SYS.VAL(LONGINT, tag), Or(SYS.VAL(LONGINT, supertag), 1));
      tag.size:=recsize;
      SetPtr(tag, nofptr, -4);
      i:=0; WHILE i<nofmth DO SetMeth(tag, i, 0, -1); INC(i) END;
    END AllocTypeDescriptor;

  BEGIN
    m:=modList; res:=done; Clear;
    WHILE (m#NIL) & (name#m.name) DO m:=m.link END;
    IF m=NIL THEN
      COPY(name, fname); i:=0;
      WHILE fname[i]#0X DO INC(i) END;
      fname[i]:="."; fname[i+1]:="O"; fname[i+2]:="b"; fname[i+3]:="j"; fname[i+4]:=0X;
      Kernel.OpenBuf(B, fname, MAX(LONGINT), found);
      IF  found THEN
        Kernel.BufRCh(B, ch0); Kernel.BufRCh(B, ch1);
        IF  ch0=0BBX  THEN  NEW(m); NEW(m.import, DefMaxImport); NEW(m.struct, DefMaxStruct);
          NEW(m.reimp, DefMaxReimp); m.nofImps:=-1; m.refCnt:=-1; m.term := NIL;
          COPY(name, m.name);
          IF  ch1=044X  THEN  m.link:=modList; modList:=m; Kernel.BufRNum(B, size); Kernel.BufSkip(B, size);

            Kernel.BufRBytes(B, m.refSize, 4); Kernel.BufRBytes(B, m.nofEntries, 2); Kernel.BufRBytes(B, m.nofCmds, 2);
            Kernel.BufRBytes(B, m.nofPtrs, 2); Kernel.BufRBytes(B, m.nofTds, 2); Kernel.BufRBytes(B, m.nofImps, 2);
            Kernel.BufRBytes(B, lnkTbl, 2); Kernel.BufRBytes(B, nofLinks, 2); Kernel.BufRBytes(B, m.dataSize, 4);
            Kernel.BufRBytes(B, m.conSize, 2); Kernel.BufRBytes(B, m.codeSize, 2); Kernel.BufRBytes(B, m.nofTraps, 2); INC(m.nofTraps);
            Kernel.BufRString(B, m.name);

            code := Align8(m.conSize+m.dataSize);
            entries := Align8(code+m.codeSize*4);
            commands := Align8(entries+m.nofEntries*2);
            imports := Align8(commands+m.nofCmds*SIZE(CommandDesc));
            typedescs := Align8(imports+(m.nofImps+1)*SIZE(Module));
            pointers := Align8(typedescs+m.nofTds*4);
            traps := Align8(pointers+m.nofPtrs*4);
            refs := Align8(traps+m.nofTraps*SIZE(TrapDesc));
            m.blockSize := Align8(refs+m.refSize);

            Kernel.AllocBlock(m.block, -m.blockSize-8);

            m.SB := m.block+m.conSize; m.PC := m.block+code;
            m.entries:=m.block+entries; m.commands:=m.block+commands;
            m.imports:=m.block+imports; m.typedescs:=m.block+typedescs;
            m.pointers:=m.block+pointers; m.traps:=m.block+traps;
            m.refs:=m.block+refs;

            Check(EntryMark);
            adr:=m.entries; lastadr:=adr+m.nofEntries*2;
            WHILE adr<lastadr DO Kernel.BufRCh(B, ch); SYS.PUT(adr, ch); INC(adr) END;

            Check(CommandMark);
            i:=0; WHILE i<m.nofCmds DO
              cmd:=SYS.VAL(CommandPtr, m.commands+i*SIZE(CommandDesc));
              Kernel.BufRString(B, cmd.name); Kernel.BufRBytes(B, cmd.offset, 2); INC(i)
            END;

            Check(PointerMark);
            adr:=m.pointers; lastadr:=adr+m.nofPtrs*4;
            WHILE adr<lastadr DO Kernel.BufRCh(B, ch); SYS.PUT(adr, ch); INC(adr) END;

            Check(ImportMark);
            mno:=0; WHILE (mno<m.nofImps) & (res=done) DO
              Kernel.BufRString(B, mname); imp:=ThisMod(mname);
              IF res=done THEN INC(imp.refCnt); SYS.PUT(m.imports+4*mno, imp); INC(mno) END;
            END;

            Check(LinkMark);
            Kernel.BufRBytes(B, links, nofLinks*SIZE(LinkEntry));

            Check(DataMark);
            adr:=m.block; lastadr:=adr+m.conSize;
            WHILE adr<lastadr DO Kernel.BufRCh(B, ch); SYS.PUT(adr, ch); INC(adr) END;

            Check(ExportMark);
            LoadExpBlock(B, m);

            Check(CodeMark);
            adr:=m.PC; lastadr:=adr+m.codeSize*4;
            WHILE adr<lastadr DO Kernel.BufRBytes(B, size, 4); SYS.PUT(adr, size); INC(adr, 4) END;

            Check(UseMark);
            CheckUseBlock(B, m);

            IF res=done THEN
              Check(TypeMark);
              i:=0; WHILE i<m.nofTds DO
                Kernel.BufRBytes(B, size, 4); Kernel.BufRBytes(B, tdadr[i], 2); Kernel.BufRBytes(B, basemod, 2);
                Kernel.BufRBytes(B, baseadr, 4);
                IF basemod>0 THEN SYS.GET(m.imports+4*basemod-4, imp); FindTDescAdr(imp, baseadr, baseadr) END;
                Kernel.BufRBytes(B, nofmth, 2); Kernel.BufRBytes(B, nofinhmth, 2); Kernel.BufRBytes(B, nofnewmth, 2);
                Kernel.BufRBytes(B, nofptr, 2);
                AllocTypeDescriptor(SHORT(size), nofmth, nofptr);
                Kernel.BufRString(B, supertag.name); supertag.mod:=m;
                SetBase(tag, 0, ASH(basemod, 16) + baseadr MOD 10000H);
                j:=0; WHILE j<nofnewmth DO
                  Kernel.BufRBytes(B, mthno, 2); Kernel.BufRBytes(B, entno, 2);
                  SetMeth(tag, mthno, 0, entno);  (* meth.PC:=entno *)
                  INC(j);
                END;
                SetPtr(tag, nofptr, -(nofptr*4+4));
                j:=0; WHILE j<nofptr DO Kernel.BufRBytes(B, adr, 4); SetPtr(tag, j, adr); INC(j) END;
                SYS.PUT(m.typedescs+4*i, tag);
                SYS.PUT(m.SB+tdadr[i], tag);
                INC(i)
              END;

              Check(TrapMark);
              adr:=m.traps; lastadr:=adr+(m.nofTraps-1)*SIZE(TrapDesc);
              WHILE adr<lastadr DO Kernel.BufRCh(B, ch); SYS.PUT(adr, ch); INC(adr) END;

              Check(RefMark);
              adr:=m.refs; lastadr:=adr+m.refSize;
              WHILE adr<lastadr DO Kernel.BufRCh(B, ch); SYS.PUT(adr, ch); INC(adr) END;

              Fixup(m, links, nofLinks, tdadr, lnkTbl);

              m.refCnt:=0;
              SYS.GET(m.entries, ent);
              SYS.PUT(SYS.ADR(body), m.PC+ent*4); SYS.PUT(SYS.ADR(body)+4, m.SB);
              FlushCache(m.block, m.blockSize+8);
              body;
              res:=done; Clear;
            ELSE
              WHILE mno>0 DO DEC(mno); SYS.GET(m.imports+4*mno, imp); DEC(imp.refCnt) END;
              IF modList=m THEN modList:=m.link
              ELSE
                imp:=modList; WHILE imp.link#m DO imp:=imp.link END; imp.link:=m.link
               END;
              Kernel.DeAllocBlock(m.block); m:=NIL
            END;
            Kernel.CloseBuf(B);
          ELSIF (ch1=88X) & (extended.Load#NIL) THEN  m.link:=modList; modList:=m; extended.Load(B, m);
            IF res # done THEN
              IF modList=m THEN modList:=m.link
              ELSE imp:=modList; WHILE imp.link#m DO imp:=imp.link END; imp.link:=m.link END;
              m := NIL
            END;
          ELSE  err(invalidObjFile, name); Kernel.CloseBuf(B); RETURN NIL
          END;
        ELSE err(invalidObjFile, name); m:=NIL;
        END
      ELSE  err(fileNotFound, name); RETURN NIL
      END
    ELSIF m.refCnt < 0 THEN err(cyclicImport, name); RETURN NIL
    END;
    RETURN m;
  END ThisMod;


  (* ----- enumerators ----- *)

  PROCEDURE EnumCommands*(mod: Module; showCmd: Command);
    VAR i, len: INTEGER; cmd: CommandPtr;
  BEGIN theMod:=mod;
    IF  mod.nofImps>0 THEN
      i:=0; len:=mod.nofCmds; cmd:=SYS.VAL(CommandPtr, mod.commands);
      WHILE i<len DO
        COPY(cmd.name, theProc.name); theProc.adr:=cmd.offset;
        cmd:=SYS.VAL(CommandPtr, SYS.VAL(LONGINT, cmd)+SIZE(CommandDesc)); INC(i);
        showCmd;
      END
    ELSIF (mod.nofImps<0) & (extended.EnumCmds#NIL) THEN  extended.EnumCmds(mod, showCmd) END
  END EnumCommands;

(* Keyboard Break *)

  PROCEDURE* ValidateBrk;
    VAR sp, pc: LONGINT; mod: Module; trap: TrapDescPtr;

    PROCEDURE NextFrame;
      VAR l: LONGINT;
    BEGIN
      l:=sp; SYS.GET(sp, sp); IF sp<l THEN SYS.GET(l+8, sp); sp:=l+sp END;
      IF  ODD(sp) THEN  DEC(sp) END;
    END NextFrame;

    PROCEDURE Try(offset: LONGINT);
    BEGIN
      SYS.GET(sp+offset, pc);
      mod:=modList; WHILE (mod # NIL) & ((pc < mod.PC) OR (pc > mod.PC+mod.codeSize*4)) DO mod:=mod.link END;
    END Try;

  BEGIN
    SYS.GETREG(1, sp);  (* ValidateBrk *)
    NextFrame;  (* Kernel.handleQ *)
    NextFrame;  (* Kernel.KbdSnoop *)
    NextFrame;  (* OS Frame 1 *)
    NextFrame;  (* OS Frame 2 *)
    Try(150H); IF mod = NIL THEN Try(154H) END;
    IF (mod # NIL) & (pc # 0) THEN
      SYS.GET(pc, brkinstr); SYS.PUT(pc, 7FE00008H); FlushCache(pc, 4); (* tw ALWAYS, PC, PC *)
      trap := SYS.VAL(TrapDescPtr, mod.traps+4*mod.nofTraps-4);
      trap.offset := SHORT((pc-mod.PC) DIV 4); trap.trapno := 22;
    END;
(*
    SYS.GET(sp+150H, pc);
    mod:=modList; WHILE (mod # NIL) & ((pc < mod.PC) OR (pc > mod.PC+mod.codeSize*4)) DO mod:=mod.link END;
    IF mod = NIL THEN SYS.GET(sp+154H, pc) END;
    LOOP
      mod:=modList; WHILE (mod # NIL) & ((pc < mod.PC) OR (pc > mod.PC+mod.codeSize*4)) DO mod:=mod.link END;
      IF mod # NIL THEN EXIT ELSE NextFrame; SYS.GET(sp+8, pc) END;
      IF sp>Kernel.resumeSP THEN EXIT END
    END;
    IF pc # 0 THEN SYS.GET(pc, brkinstr); SYS.PUT(pc, 7FE00008H); FlushCache(pc, 4) END;  (* tw ALWAYS, PC, PC *)
    trap := SYS.VAL(TrapDescPtr, mod.traps+4*mod.nofTraps-4);
    trap.offset := SHORT((pc-mod.PC) DIV 4); trap.trapno := 22;
*)
  END ValidateBrk;


  PROCEDURE ReadInt(VAR i: LONGINT; VAR pos: LONGINT);
    VAR n: LONGINT; s: SHORTINT; x: CHAR;
  BEGIN
    s := 0; n := 0; SYS.GET(pos, x); INC(pos);
    WHILE ORD(x) >= 128 DO INC(n, ASH(ORD(x) - 128, s)); INC(s, 7); SYS.GET(pos, x); INC(pos) END;
    i := n + ASH(ORD(x) MOD 64 - ORD(x) DIV 64 * 64, s)
  END ReadInt;

  PROCEDURE FindProc(pc: LONGINT; mod: Module; VAR ref, refend, adr: LONGINT);
    VAR ch: CHAR; r: LONGINT;
  BEGIN ref:=-1;
    pc:=(pc-mod.PC) DIV 4;
    r:=mod.refs; refend:=r;
    IF  r#0 THEN  INC(refend, mod.refSize)  END;
    LOOP
      IF  r>=refend THEN  EXIT  END;
      SYS.GET(r, ch); INC(r);
      IF  ch=0F8X THEN  ReadInt(adr, r);
        IF  adr>=pc THEN  ref:=r; EXIT  END;
      END
    END
  END FindProc;

  PROCEDURE ShowFrame(VAR ref: LONGINT; refend, base: LONGINT; global: BOOLEAN; showVar: Command);
    VAR pos, adr, mode, li: LONGINT; i: INTEGER; si, form: SHORTINT; ch, VarFlag: CHAR; regalloc: BOOLEAN; lr: LONGREAL;
  BEGIN
    pos := ref; SYS.GET(pos, VarFlag); INC(pos);
    WHILE (pos < refend) & (VarFlag # 0F8X) DO
      SYS.GET(pos, form); INC(pos);
      ReadInt(adr, pos);
      SYS.GET(pos, ch); INC(pos);
      i:=0; WHILE (ch # 0X) & (pos < refend) DO theObj.name[i]:=ch; SYS.GET(pos, ch); INC(pos); INC(i)  END;
      theObj.name[i]:=0X; theObj.reg:=0; theObj.global:=global;
      IF  adr<0 THEN
        adr := -1-adr; mode := adr DIV 32; adr := adr MOD 32;
        IF  VarFlag = 3X  THEN  theObj.reg:=adr; adr:=Kernel.theRegSet.reg.R[2*adr+1]; regalloc:=FALSE;
        ELSE
          IF  mode = Reg  THEN  theObj.reg:=adr; adr:=SYS.ADR(Kernel.theRegSet.reg.R[2*adr+1]); regalloc:=TRUE
          ELSIF mode = FReg THEN theObj.reg:=adr+256; adr:=SYS.ADR(Kernel.theRegSet.fp.R[2*adr]); regalloc:=TRUE
          ELSIF adr IN SYS.VAL(SET, Kernel.theRegSet.spec.CR) THEN  theObj.boolval:=TRUE
          ELSE  theObj.boolval:=FALSE
          END
        END
      ELSE  adr:=adr+base; regalloc:=FALSE
      END;

      IF  regalloc & (form IN {Byte, Bool, Char}) THEN  INC(adr, 3) END;
      theObj.adr:=adr; theObj.class:=form; SYS.GET(adr, li);
      CASE  form  OF
        |  Byte:  SYS.GET(adr, theObj.chval);
        |  Char:  SYS.GET(adr, theObj.chval);
        |  Bool:  IF  (mode=Reg) OR ~regalloc THEN  SYS.GET(adr, theObj.boolval)  END;
        |  SInt:  IF  ~regalloc THEN  SYS.GET(adr, si); theObj.intval:=si ELSE  theObj.intval:=li END
        |  Int: IF  ~regalloc THEN  SYS.GET(adr, i); theObj.intval:=i ELSE  theObj.intval:=li END
        |  LInt, Pointer: theObj.intval:=li
        |  Real:  IF  regalloc  THEN  SYS.GET(adr, lr); theObj.rval := SHORT(lr)  ELSE  SYS.GET(adr, theObj.rval) END;
        |  LReal: SYS.GET(adr, theObj.lrlval);
        |  Set: theObj.setval:=SYS.VAL(SET, li);
        |  Comp:
            i := 1; SYS.GET(adr, ch);
            WHILE (i < 128) & (ch # 0X) DO theObj.strval[i-1]:=ch; SYS.GET(adr+i, ch); INC(i) END;
            theObj.strval[i-1]:=0X; theObj.class:=String;
      ELSE
      END;
      showVar();
      SYS.GET(pos, VarFlag); INC(pos)
    END;
    ref := pos-1
  END ShowFrame;

  PROCEDURE EnumStkFrames*(showProc, showVar: Command); (* first eliminated *)
    VAR pc, sp, ref, refend, fsize, psize, ralloc, falloc, calloc, base: LONGINT; mod: Module; leaf, body: BOOLEAN; ch: CHAR;
  BEGIN
    pc:=Kernel.theRegSet.spec.PC; sp:=Kernel.theRegSet.reg.R[2*1+1];
    WHILE sp<=Kernel.resumeSP DO
      mod:=modList;  WHILE  (mod#NIL) & ((pc<mod.PC) OR (pc>mod.PC+mod.codeSize*4)) DO  mod:=mod.link END;
      theMod:=mod;
      IF  (mod#NIL) & (mod.nofImps>=0)  THEN
        FindProc(pc, mod, ref, refend, theProc.adr);
        theProc.pc:=pc; theProc.sp:=sp; theProc.relpc:=pc-mod.PC;
        IF  ref>0 THEN
          ReadInt(fsize, ref); ReadInt(psize, ref); ReadInt(ralloc, ref); ReadInt(falloc, ref); ReadInt(calloc, ref);
          SYS.GET(ref, leaf); INC(ref);
          SYS.GET(ref, ch); INC(ref); body := ch = "$";
          base:=0; WHILE  (ch # 0X) & (ref < refend)  DO  theProc.name[base]:=ch; INC(base); SYS.GET(ref, ch); INC(ref) END;
          theProc.name[base]:=0X; showProc;

          IF  body  THEN  base := mod^.SB ELSE  base := Kernel.theRegSet.reg.R[31*2+1]  END;
          ShowFrame(ref, refend, base, body, showVar);

          SYS.GET(sp, sp);
          IF  leaf  THEN  pc := Kernel.theRegSet.spec.LR  ELSE  SYS.GET(sp+8, pc) END;
          base := sp-(31-ralloc)*4;
          WHILE ralloc < 31 DO  INC(ralloc); SYS.GET(base, Kernel.theRegSet.reg.R[2*ralloc+1]); INC(base, 4)  END;
          INC(base, (-base) MOD 8);
          WHILE falloc < 31 DO  INC(falloc); SYS.GET(base, Kernel.theRegSet.fp.R[2*falloc+1]); INC(base, 8) END;
          IF  calloc < 19 THEN  SYS.GET(sp+4, Kernel.theRegSet.spec.CR) END
        ELSE
          theProc.name:="Undefined Procedure"; SYS.GET(sp, sp); SYS.GET(sp+8, pc); showProc();
          RETURN
        END
      ELSIF (mod#NIL) & (extended.EnumLocls#NIL)  THEN  extended.EnumLocls(mod, sp, pc, showProc, showVar)
      ELSE  theMod:=NIL; theProc.relpc:=-1; theProc.name:="MacOS toolbox";
        showProc(); pc:=sp; SYS.GET(sp, sp); IF sp<pc THEN SYS.GET(pc+8, sp); sp:=pc+sp END;  (* calculate offset *)
        SYS.GET(sp+8, pc);
        IF  ODD(sp) THEN  DEC(sp) END;
      END
    END;
  END EnumStkFrames;

  PROCEDURE EnumGlobals*(mod: Module; showVar: Command);
    VAR ch: CHAR; adr, p: LONGINT; name: ARRAY 32 OF CHAR; ref, refend: LONGINT;
  BEGIN theMod:=mod; ref:=mod.refs; refend:=ref;
    IF  mod.refs#0  THEN  INC(refend, mod.refSize);
      LOOP
        IF  ref>=refend THEN  EXIT  END;
        SYS.GET(ref, ch); INC(ref);
        IF  ch=0F8X THEN
          ReadInt(p, ref); ReadInt(p, ref); ReadInt(p, ref); ReadInt(p, ref); ReadInt(p, ref); ReadInt(p, ref);
          SYS.GET(ref, ch); INC(ref);
          SYS.GET(ref, ch); INC(ref);
          IF  ch="$"  THEN  EXIT  END;
        END
      END;
      IF  (ref<refend) & (ch="$") THEN  INC(ref, 2); ShowFrame(ref, refend, mod.SB, TRUE, showVar)  END;
    ELSIF (mod.nofImps<0) & (extended.EnumGlobs#NIL)  THEN  extended.EnumGlobs(mod, showVar)  END
  END EnumGlobals;


  (* ----- trap handling ----- *)

  PROCEDURE FindTrapClass(mod: Module; pc: LONGINT; VAR class: INTEGER);
    VAR pos, len: LONGINT; trap: TrapDescPtr;
  BEGIN
    pc:=(pc-mod.PC) DIV 4; class:=256; pos:=0;
    IF  mod.traps#0 THEN  len:=mod.nofTraps ELSE  len:=0  END;
    trap:=SYS.VAL(TrapDescPtr, mod.traps);
    WHILE (pos<len) & (pc#trap.offset)  DO  INC(pos); trap:=SYS.VAL(TrapDescPtr, SYS.VAL(LONGINT, trap)+4)  END;
    IF  pos<len THEN  class:=trap.trapno  END;
  END FindTrapClass;

  PROCEDURE* trap(context: TB.ExceptionInfo): LONGINT;
    VAR m: Module; adr, pc: LONGINT;
  BEGIN
    Kernel.theRegSet:=context^;
    m:=modList; pc:=Kernel.theRegSet.spec.PC;
    WHILE (m#NIL) & ((pc<m.PC) OR (pc>m.PC+m.codeSize*4)) DO  m:=m.link END;
    Kernel.theTrap.mod:=SYS.VAL(LONGINT, m);
    IF  Kernel.theTrap.mod#0  THEN
      FindTrapClass(SYS.VAL(Module, Kernel.theTrap.mod), Kernel.theRegSet.spec.PC, Kernel.theTrap.class)
    ELSE  Kernel.theTrap.class:=256 END;
    Kernel.theTrap.kind:=Kernel.theRegSet.kind;
    IF  ((context.kind=2)&(Kernel.theTrap.class>255) OR (context.kind=9))&dbgInstalled THEN RETURN -1 END;  (* launch MacsBug *)
    Kernel.theTrap.pc:=Kernel.theRegSet.spec.PC; Kernel.theTrap.fp:=Kernel.theRegSet.reg.R[2*1+1];
    Kernel.theTrap.oserr:=SHORT(Kernel.theRegSet.reg.R[2*3+1]);
    IF  Kernel.theTrap.class = 22 THEN  SYS.PUT(Kernel.theTrap.pc, brkinstr); FlushCache(Kernel.theTrap.pc, 4)  END;
    Kernel.HandleQ(Kernel.trapQ);
    Kernel.Resume(context); RETURN 0;
  END trap;


  (* ----- gargage collection ----- *)

  PROCEDURE SetMark (adr: LONGINT);
    VAR set: SET;
  BEGIN SYS.GET(adr - 4, set); set := set + {Kernel.MarkBit}; SYS.PUT(adr - 4, set)
  END SetMark;

  PROCEDURE MarkModules;
    VAR mod: Module; data, offset, i, p: LONGINT; ptr: Kernel.Block; set: SET;
  BEGIN
    mod := modList;
    WHILE mod # NIL DO
      SetMark (SYS.VAL(LONGINT, mod));
      data := mod.SB;
      FOR i := 0 TO mod.nofPtrs - 1 DO
        SYS.GET(mod.pointers + 4*i, offset);
        SYS.GET(data + offset, ptr);
        IF ptr # NIL THEN Kernel.Mark(ptr) END
      END;
      FOR i := 0 TO mod.nofTds - 1 DO
        SYS.GET(mod.typedescs + 4*i, p);
        IF p # 0 THEN
          SYS.GET(p-4, set);
          p := SYS.VAL(LONGINT, set - {Kernel.RecBit, Kernel.MarkBit});
          IF Kernel.RecBit IN set THEN SetMark(p) END
        END
      END;
      IF mod.privates#0 THEN Kernel.Mark(SYS.VAL(Kernel.Block, mod.privates)) END;
      IF mod.publics#0 THEN Kernel.Mark(SYS.VAL(Kernel.Block, mod.publics)) END;
      IF mod.import#NIL THEN Kernel.Mark(SYS.VAL(Kernel.Block, mod.import)) END;
      IF mod.struct#NIL THEN Kernel.Mark(SYS.VAL(Kernel.Block, mod.struct)) END;
      IF mod.reimp#NIL THEN Kernel.Mark(SYS.VAL(Kernel.Block, mod.reimp)) END;
      mod := mod.link
    END;
  END MarkModules;

  (** Install a procedure to be called before a module is freed from memory, or before the Oberon system terminates.
  The termination handler  is associated with the module where it is located *)
  PROCEDURE InstallTermHandler* (h: TerminationHandler);
    VAR m: Module; adr: LONGINT; found: BOOLEAN;
  BEGIN
    m := modList; SYS.GET(SYS.ADR(h), adr); found := FALSE;
    WHILE (m # NIL) & ~found DO
      IF (m.PC <= adr) & (adr < m.PC + m.codeSize*4) THEN found := TRUE
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

BEGIN
  SYS.GET(0BFFH, theObj.chval); dbgInstalled:=ODD(ORD(theObj.chval) DIV 32);  (* test bit 5: Set if debugger is installed *)
  TB.Assign("SYSFPURegProcs", SYS.ADR(FPURegProcs));
  TB.Assign("SYSModList", -SYS.ADR(modList));
  TB.Assign("MakeDataExecutable", SYS.ADR(FlushCache));
  Kernel.InstallQ(Kernel.mkQ, MarkModules); Kernel.InstallQ(Kernel.brkQ, ValidateBrk);
  Kernel.InstallQ(Kernel.quitQ, TermModules);
  oldTrap:=TB.InstallExceptionHandler(trap); Kernel.theTrap.pc:=0;
  theMod:=ThisMod("Interchange");
END Modules.
