(* ETH Oberon, Copyright 2000 ETH Zürich Institut für Computersysteme, ETH Zentrum, CH-8092 Zürich.
Refer to the general ETH Oberon System license contract available at: http://www.oberon.ethz.ch/ *)

MODULE OPLL;  (* mmb 17.1.91 / 31.5.94  / od Feb 95 / tk 30.6.96 *)

  (* 30.6.96  Method support (mfix) *)

  IMPORT
    SYS:=SYSTEM, Kernel, PLT:=OPLT, Modules;

  CONST
    Var=1; Par=2; VarPar=3; TypDynArr=8; TypArray=9; TypPointer=10; TypRecord=11; TypProcTyp=12;
    (* structure forms *)
    Undef = 0; Byte = 1; Bool = 2; Char = 3; SInt = 4; Int = 5; LInt = 6;
    Real = 7; LReal = 8; Set = 9; String = 10; NilTyp = 11; NoTyp = 12;
    Pointer = 13; ProcTyp = 14; Comp = 15;

    (* composite structure forms *)
    Basic = 1; Array = 2; DynArr = 3; Record = 4;

    (* item/object modes *)
    Con = 4; Fld = 5; (*Typ = 5;*) LProc = 6; XProc = 7; SProc = 8; CProc = 9; IProc = 10;
    Head = 12; TProc = 14; Based = 14; Indexed = 15; Reg = 16; RegSI = 17; FReg = 18; Cond = 19;

    (* module visibility of objects *)
    internal = 0; external = 1; externalR = 2;

    memTag = 1024;

    (* fields in the POWER architecture instruction encoding *)
    fAA = 00000002H;
    fBA = 00010000H;
    fBB = 00000800H;
    fBD = 00000004H;
    fBF = 00800000H;
    fBFA = 00040000H;
    fBI = 00010000H;
    fBO = 00200000H;
    fBT = 00200000H;
    fD = 00000001H;
    fEO = 00000002H;
    fEO1 = 00000002H;
    fFXM = 00001000H;
    fFLM = 00020000H;
    fFRA = 00010000H;
    fFRB = 00000800H;
    fFRC = 00000040H;
    fFRS = 00200000H;
    fFRT = 00200000H;
    fI = 00001000H;
    fLI = 00000004H;
    fMB = 00000040H;
    fME = 00000002H;
    fNB = 00000800H;
    fOE = 00000400H;
    fOPCD = 04000000H;
    fRA = 00010000H;
    fRB = 00000800H;
    fRS = 00200000H;
    fRT = 00200000H;
    fSH = 00000800H;
    fSI = 00000001H;
    fSPR = 00010000H;
    fTO = 00200000H;
    fLK = 00000001H;
    fUI = 00000001H;
    fXO = 00000002H;
    REC = 1;

    (* opcodes, POWER architecture *)
    iA =  7C000014H;
    iABS =  7C0002D0H;
    iAE =  7C000114H;
    iAI =  30000000H;
    iAME =  7C0001D4H;
    iAND =  7C000038H;
    iANDC =  7C000078H;
    iANDIL =  70000000H;
    iANDIU =  74000000H;
    iAZE =  7C000194H;
    iB =  48000000H;
    iBC =  40000000H;
    iBCC =  4C000420H;
    iBCR =  4C000020H;
    iCAL =  38000000H;
    iCAU =  3C000000H;
    iCAX =  7C000214H;
    iCLCS =  7C000426H;
    iCLF =  7C0000ECH;
    iCLI =  7C0003ECH;
    iCMP =  7C000000H;
    iCMPI =  2C000000H;
    iCMPL =  7C000040H;
    iCMPLI =  28000000H;
    iCNTLZ =  7C000034H;
    iCRAND =  4C000202H;
    iCRANDC =  4C000102H;
    iCREQV =  4C000242H;
    iCRNAND =  4C0001C2H;
    iCRNOR =  4C000042H;
    iCROR =  4C000382H;
    iCRORC =  4C000342H;
    iCRXOR =  4C000182H;
    iDCLST =  7C0004ECH;
    iDCLZ =  7C0007ECH;
    iDCS =  7C0004ACH;
    iDIV =  7C000296H;
    iDIVS =  7C0002D6H;
    iDOZ =  7C000210H;
    iDOZI =  24000000H;
    iEQV =  7C000238H;
    iEXTS =  7C000734H;
    iFA = 0FC00002AH;
    iFABS = 0FC000210H;
    iFCMPO = 0FC000040H;
    iFCMPU = 0FC000000H;
    iFD = 0FC000024H;
    iFM = 0FC000032H;
    iFMA = 0FC00003AH;
    iFMR = 0FC000090H;
    iFMS = 0FC000038H;
    iFNABS = 0FC000110H;
    iFNEG = 0FC000050H;
    iFNMA = 0FC00003EH;
    iFNMS = 0FC00003CH;
    iFRSP = 0FC000018H;
    iFS = 0FC000028H;
    iICS =  4C00012CH;
    iL = 080000000H;
    iLBRX =  7C00042CH;
    iLBZ = 088000000H;
    iLBZU = 08C000000H;
    iLBZUX =  7C0000EEH;
    iLBZX =  7C0000AEH;
    iLFD = 0C8000000H;
    iLFDU = 0CC000000H;
    iLFDUX =  7C0004EEH;
    iLFDX =  7C0004AEH;
    iLFS = 0C0000000H;
    iLFSU = 0C4000000H;
    iLFSUX =  7C00046EH;
    iLFSX =  7C00042EH;
    iLHA = 0A8000000H;
    iLHAU = 0AC000000H;
    iLHAUX =  7C0002EEH;
    iLHAX =  7C0002AEH;
    iLHBRX =  7C00062CH;
    iLHZ = 0A0000000H;
    iLHZU = 0A4000000H;
    iLHZUX =  7C00026EH;
    iLHZX =  7C00022EH;
    iLM = 0B8000000H;
    iLSCBX =  7C00022AH;
    iLSI =  7C0004AAH;
    iLSX =  7C00042AH;
    iLU = 084000000H;
    iLUX =  7C00006EH;
    iLX =  7C00002EH;
    iMASKG =  7C00003AH;
    iMASKIR =  7C00043AH;
    iMCRF =  4C000000H;
    iMCRFS = 0FC000080H;
    iMCRXR =  7C000400H;
    iMFCR =  7C000026H;
    iMFFS = 0FC00048EH;
    iMFMSR =  7C0000A6H;
    iMFSPR =  7C0002A6H;
    iMFSR =  7C0004A6H;
    iMFSRI =  7C0004E6H;
    iMTCRF =  7C000120H;
    iMTFSB0 = 0FC00008CH;
    iMTFSB1 = 0FC00004CH;
    iMTFSF = 0FC00058EH;
    iMTSFI = 0FC00010CH;
    iMTMSR =  7C000124H;
    iMTSPR =  7C0003A6H;
    iMTSR =  7C0001A4H;
    iMTSRI =  7C0001E4H;
    iMUL =  7C0000D6H;
    iMULI =  1C000000H;
    iMULS =  7C0001D6H;
    iNABS =  7C0003D0H;
    iNAND =  7C0003B8H;
    iNEG =  7C0000D0H;
    iNOR =  7C0000F8H;
    iOR =  7C000378H;
    iORC =  7C000338H;
    iORIL =  60000000H;
    iORIU =  64000000H;
    iRAC =  7C000664H;
    iRFI =  4C000064H;
    iRFSVC =  4C0000A4H;
    iRLIMI =  50000000H;
    iRLINM =  54000000H;
    iRLMI =  58000000H;
    iRLNM =  5C000000H;
    iRRIB =  7C000432H;
    iSF =  7C000010H;
    iSFE =  7C000110H;
    iSFI =  20000000H;
    iSFME =  7C0001D0H;
    iSFZE =  7C000190H;
    iSL =  7C000030H;
    iSLE =  7C000132H;
    iSLEQ =  7C0001B2H;
    iSLIQ =  7C000170H;
    iSLLIQ =  7C0001F0H;
    iSLLQ =  7C0001B0H;
    iSLQ =  7C000130H;
    iSR =  7C000430H;
    iSRA =  7C000630H;
    iSRAI =  7C000670H;
    iSRAIQ =  7C000770H;
    iSRAQ =  7C000730H;
    iSRE =  7C000532H;
    iSREA =  7C000732H;
    iSREQ =  7C0005B2H;
    iSRIQ =  7C000570H;
    iSRLIQ =  7C0005F0H;
    iSRLQ =  7C0005B0H;
    iSRQ =  7C000530H;
    iST = 90000000H;
    iSTB = 98000000H;
    iSTBRX =  7C00052CH;
    iSTBU = 9C000000H;
    iSTBUX =  7C0001EEH;
    iSTBX =  7C0001AEH;
    iSTFD = 0D8000000H;
    iSTFDU = 0DC000000H;
    iSTFDUX =  7C0005EEH;
    iSTFDX =  7C0005AEH;
    iSTFS = 0D0000000H;
    iSTFSU = 0D4000000H;
    iSTFSUX =  7C00056EH;
    iSTFSX =  7C00052EH;
    iSTH = 0B0000000H;
    iSTHBRX =  7C00072CH;
    iSTHU = 0B4000000H;
    iSTHUX =  7C00036EH;
    iSTHX =  7C00032EH;
    iSTM = 0BC000000H;
    iSTSI =  7C0005AAH;
    iSTSX =  7C00052AH;
    iSTU = 94000000H;
    iSTUX =  7C00016EH;
    iSTX =  7C00012EH;
    iSVC =  44000000H;
    iT =  7C000008H;
    iTI =  0C000000H;
    iTLBI =  7C000264H;
    iXOR =  7C000278H;
    iXORIL =  68000000H;
    iXORIU =  6C000000H;
    iMR = iCAL;
    iMTCR = iMTCRF+0FFH*fFXM;

    (* special register definitions *)
    SB = 2; SP = 1; FP = 31; SLpar = 11; virtualFP = 32; spCTR = 9; spMQ = 0; spLR = 8;

    (* register allocation parameters *)
    SaveRlimit = 12;
    SaveFlimit = 13;
    TempRegs* = {3..12};
    TempFRegs* = {0..13};
    TempCRFields* = {1,6,7};
    TempCRBits* = {4..7,24..31};

    cALWAYS = 1FH;

    (* RTS procedure tags *)
    LinkMTag = 0FEX; CaseE2Tag = 0FEX;

    (* various constants *)
    CodeSize = 16384; (* words *)
    ConstLength* = 4096+4096; (* bytes *)
    MaxExts = 16; MaxRecs = 64; (* mfix *)
    MaxLinks = 250; MaxTraps = 2048+256;
    LowWord = 10000H;
    MaxEntry* = 128;

  TYPE
    Item* = RECORD
      mode*, mnolev*, dmode*, dreg*: SHORTINT;
      adr*: LONGINT;
      typ*: PLT.Struct;
      offset*: LONGINT;
      reg*: LONGINT;
      Tjmp*, Fjmp*: INTEGER;
    END;

    Label* = INTEGER;

    LinkEntry = RECORD
      mod, ent: CHAR;
      pos: Label
    END;

    SaveDesc* = RECORD
      savedR, savedF, ParR, ParF: SET;
      offset: LONGINT
    END;

    Tag = POINTER TO TypeDescriptor;
    TypeDescriptor = RECORD
      recsize : LONGINT;
      ptroff : LONGINT;
    END;

    TypeName = ARRAY 32 OF CHAR;

    SuperTag = POINTER TO SuperDescriptor;
    SuperDescriptor = RECORD
      tdsize : LONGINT;
      ptroff : LONGINT;
      tag : Tag;
      nofmth : SHORTINT;
      pad : ARRAY 2 OF SHORTINT;
      extlevel : SHORTINT;
      typename : TypeName;
      module : Modules.Module;
    END;

  VAR
    entno*, level*: INTEGER;
    dsize*: LONGINT;
    linkTable*: LONGINT;
    pc*: LONGINT;
    entry*: ARRAY MaxEntry OF Label;
    TempR, TempF, ParR, ParF, TempCRF, TempCRB, HoldR: SET;
    TempRpos, TempFpos, TempCRFpos, TempCRBpos, SaveRpos, SaveFpos: LONGINT;
    nofrec, noflk, noftraps*: INTEGER;
    conx*: INTEGER;
    procStart: LONGINT;
    saveStart, SLsize: LONGINT;
    CaseLink: INTEGER;
    recTab: ARRAY MaxRecs OF PLT.Struct;
    code*: ARRAY CodeSize OF LONGINT;
    constant*: ARRAY ConstLength OF CHAR;
    links: ARRAY MaxLinks OF LinkEntry;
    CRF0used: BOOLEAN;
    Traps*: ARRAY MaxTraps OF RECORD no*, pc*: INTEGER END;
    PC* : LONGINT;
    SaveFProc, RestFProc : ARRAY 33 OF LONGINT;
    refSize* : LONGINT;
    (* refs* : ARRAY 10*1024 OF CHAR; *)
    fixProc*: PLT.Object;

  PROCEDURE err*(n: INTEGER);
  BEGIN
  END err;

(*
  PROCEDURE RefW(ch : CHAR);
  BEGIN refs[refSize]:=ch; INC(refSize);
  END RefW;
*)

  PROCEDURE Align* (VAR offset: LONGINT; base: INTEGER);
  BEGIN
    CASE base OF
      1: (* ok *)
    | 2: INC(offset, offset MOD 2)
    | 4: INC(offset, (-offset) MOD 4)
    | 8: INC(offset, (-offset) MOD 8)
    END
  END Align;

  PROCEDURE Base* (typ: PLT.Struct): INTEGER; (* typ^.comp # DynArr *)
    VAR array: BOOLEAN;
  BEGIN
    array := typ.comp = Array;
    WHILE typ^.comp = Array DO typ := typ^.BaseTyp END ;
    IF typ^.comp = Record THEN RETURN ABS(typ^.align) (*!!!*)
    ELSIF typ^.form = ProcTyp THEN RETURN 4
    ELSIF array & (typ.form = Char) THEN RETURN 4
    ELSE RETURN SHORT(typ^.size)
    END
  END Base;

  PROCEDURE ^ ParamAdr* (VAR firstPar: PLT.Object); (* mfix *)

  PROCEDURE TypSize*(typ : PLT.Struct);
  VAR f, c, fbase, base, nofptr: INTEGER; btyp: PLT.Struct; fld: PLT.Object; offset, size, n, dims: LONGINT;
  BEGIN
    IF typ.size<0 THEN
      f:=typ.form; c:=typ.comp; btyp:=typ.BaseTyp;
      IF c=Record THEN
        fld:=typ.dsc;
        IF typ.sysflag=1 THEN typ.align:=-2 END;
        IF btyp=NIL THEN nofptr:=0; base:=1; offset:=0
        ELSE TypSize(btyp); typ.extlev:=btyp.extlev+1; nofptr:=btyp.nofptr; offset:=btyp.size; base:=btyp.align END;
        WHILE (fld#NIL) & (fld.mode=Fld) DO
          btyp:=fld.typ;
          IF btyp#NIL THEN TypSize(btyp); size:=btyp.size;
            fbase:=Base(btyp);
            IF (typ^.align < 0) & (fbase > 2) THEN Align(offset, 2) ELSE Align(offset, fbase) END; (*68kalign*)
            fld.adr:=offset; INC(offset, size); INC(nofptr, btyp.nofptr);
            IF fbase>base THEN base:=fbase END
          END; fld:=fld.nxtobj
        END;
        IF typ^.align >= 0 THEN Align(offset, base); typ^.align := SHORT(base) END;
        typ.size:=offset; typ.nofptr:=nofptr;
        WHILE fld#NIL DO  (* Methods / mfix *)
          ParamAdr(fld);
          IF fld.adr MOD 10000H = 0 THEN  (* entno *)
            INC(fld.adr, LONG(entno)); INC(entno)
          END;
          fld := fld.nxtobj;
        END;
      ELSIF f=Pointer THEN typ.size:=4; typ.nofptr:=1
      ELSIF c=Array THEN TypSize(btyp); typ.size:=typ.n*btyp.size; typ.nofptr:=SHORT(typ.n*btyp.nofptr)
      ELSIF f=ProcTyp THEN typ.size:=8; TypSize(btyp);
      ELSE (*c=DynArr*)
        n:=typ.n; dims := n+1; btyp:=typ;
        WHILE n>=0 DO
          btyp^.offset := 4*(dims-n); btyp^.size := 4*n + 8;
          btyp := btyp^.BaseTyp; DEC(n)
        END;
        TypSize(btyp);
      END
    END;
  END TypSize;

  PROCEDURE FreeTempR* (r: LONGINT);
  BEGIN TempR := TempR + {r}*TempRegs - HoldR - ParR
  END FreeTempR;

  PROCEDURE FreeTempF* (r: LONGINT);
  BEGIN TempF := TempF + {r}*TempFRegs - ParF
  END FreeTempF;

  PROCEDURE FreeTempCRBs* (s: SET);
    VAR i: INTEGER; f: SET;
  BEGIN
    IF s*{0..3} # {} THEN CRF0used := FALSE END;
    TempCRB := TempCRB + s*TempCRBits;
    i := 0;
    WHILE i < 32 DO
      f := {i..i+3}; IF f*TempCRB=f THEN TempCRB := TempCRB-f; TempCRF := TempCRF+{i DIV 4} END;
      INC(i, 4)
    END
  END FreeTempCRBs;

  PROCEDURE GetSaveF* (): LONGINT;
    VAR r: LONGINT;
  BEGIN
    ASSERT(SaveFpos > SaveFlimit);
    r := SaveFpos; SaveFpos := r-1; RETURN r
  END GetSaveF;

  PROCEDURE GetSaveR* (): LONGINT;
    VAR r: LONGINT;
  BEGIN
    ASSERT(SaveRpos > SaveRlimit);
    r := SaveRpos; SaveRpos := r-1; RETURN r
  END GetSaveR;

  PROCEDURE GetTempF* (): LONGINT;
    VAR r, t: LONGINT;
  BEGIN
    r := TempFpos; t := r+1;
    WHILE (t # r) & ~(t IN TempF) DO t := (t+1) MOD 32 END;
    IF t IN TempF THEN TempFpos := t; EXCL(TempF, t) ELSE err(216) END;
    RETURN t
  END GetTempF;

  PROCEDURE GetTempR* (): LONGINT;
    VAR r, t: LONGINT;
  BEGIN
    r := TempRpos; t := r+1;
    WHILE (t # r) & ~(t IN TempR) DO t := (t+1) MOD 32 END;
    IF t IN TempR THEN TempRpos := t; EXCL(TempR, t) ELSE err(215) END;
    RETURN t
  END GetTempR;

  PROCEDURE GetTempCRF* (): LONGINT;
    VAR r, t: LONGINT;
  BEGIN
    r := TempCRFpos; t := r+1;
    WHILE (t # r) & ~(t IN TempCRF) DO t := (t+1) MOD 8 END;
    IF t IN TempCRF THEN TempCRFpos := t; EXCL(TempCRF, t) ELSE err(215) END;
    RETURN t
  END GetTempCRF;

  PROCEDURE GetTempCRB* (): LONGINT;
    VAR r, t: LONGINT;
  BEGIN
    IF TempCRB = {} THEN r := GetTempCRF(); TempCRB := {r*4..r*4+3} END;
    r := TempCRBpos; t := r+1;
    WHILE (t # r) & ~(t IN TempCRB) DO t := (t+1) MOD 32 END;
    IF t IN TempCRB THEN TempCRBpos := t; EXCL(TempCRB, t) ELSE err(215) END;
    RETURN t
  END GetTempCRB;

  PROCEDURE GetCRF0* (): LONGINT;
  BEGIN
    IF CRF0used THEN RETURN GetTempCRF() ELSE CRF0used := TRUE; RETURN 0 END
  END GetCRF0;

  PROCEDURE GetTempRegs* (nrRegs: LONGINT; freeable: SET): LONGINT;
    VAR toGet, free: SET; r, t: LONGINT;
  BEGIN
    r := TempRpos; t := r;
    REPEAT
      t := (t+1) MOD 32; IF t+nrRegs > 32 THEN t := 0 END;
      toGet := {t..t+nrRegs-1}
    UNTIL (t = r) OR (TempR*toGet = toGet);
    IF TempR*toGet = toGet THEN TempR := TempR-toGet; TempRpos := t+nrRegs
    ELSIF freeable # {} THEN free := TempR+freeable;
      REPEAT
        t := (t+1) MOD 32; IF t+nrRegs > 32 THEN t := 0 END;
        toGet := {t..t+nrRegs-1}
      UNTIL (t = r) OR (free*toGet = toGet);
      IF free*toGet = toGet THEN TempR := TempR-toGet; TempRpos := t+nrRegs ELSE err(215) END
    END;
    RETURN t
  END GetTempRegs;

  PROCEDURE FreeTempRegs* (r, nrRegs: LONGINT);
  BEGIN TempR := TempR+{r..r+nrRegs-1}*TempRegs-HoldR
  END FreeTempRegs;

  PROCEDURE LockTempR* (regs: SET);
  BEGIN
    ASSERT(regs-TempR = {}); TempR := TempR-regs
  END LockTempR;

  PROCEDURE LockTempF* (regs: SET);
  BEGIN
    ASSERT(regs-TempF = {}); TempF := TempF-regs
  END LockTempF;

  PROCEDURE HoldTempR* (r: LONGINT);
  BEGIN INCL(HoldR, r)
  END HoldTempR;

  PROCEDURE UnholdTempR* (r: LONGINT);
  BEGIN EXCL(HoldR, r)
  END UnholdTempR;

  PROCEDURE LockParR* (r: LONGINT);
  BEGIN
    EXCL(TempR, r); INCL(ParR, r)
  END LockParR;

  PROCEDURE LockParF* (r: LONGINT);
  BEGIN
    EXCL(TempF, r); INCL(ParF, r)
  END LockParF;

  PROCEDURE FreePar*;
  BEGIN
    TempR := TempR+ParR; ParR := {}; TempF := TempF+ParF; ParF := {}
  END FreePar;

  PROCEDURE AllocConst* (VAR s: ARRAY OF SYS.BYTE; len: LONGINT; VAR adr: LONGINT; align: SHORTINT);
    VAR fill: LONGINT;
  BEGIN
    fill := (conx-len) MOD align;
    WHILE fill > 0 DO DEC(conx); constant[conx] := 0X; DEC(fill) END;
    conx := SHORT(conx-len); IF conx < 255 THEN err(230); conx := ConstLength END;
    adr := conx-ConstLength; SYS.MOVE(SYS.ADR(s[0]), SYS.ADR(constant[conx]), len)
  END AllocConst;

  PROCEDURE AllocTypDesc* (typ: PLT.Struct);
    VAR nil: LONGINT;
  BEGIN
    ASSERT(typ^.comp IN {Record, Array});
    IF (typ^.comp = Record) THEN
      nil := 0; AllocConst(nil, 4, typ^.tdadr, 4);
      IF typ^.extlev > MaxExts THEN err(233)
      ELSIF nofrec < MaxRecs THEN
        recTab[nofrec] := typ; INC(nofrec)
      ELSE err(223)
      END
    END (* no type desc for arrays *)
  END AllocTypDesc;

  PROCEDURE AllocCaseTable* (high: LONGINT; VAR table: LONGINT);
    VAR tab: ARRAY 512 OF LONGINT; l: INTEGER; i: LONGINT;
  BEGIN
    IF CaseLink = -1 THEN
      IF noflk < MaxLinks THEN
        l := noflk; INC(noflk); links[l].pos := 0; links[l].mod := LinkMTag; links[l].ent := CaseE2Tag;
        CaseLink := l
      ELSE err(231); l := 0; CaseLink := l
      END
    ELSE l := CaseLink
    END;
    tab[0] := links[l].pos*10000H; tab[1] := high*10000H; INC(high); IF high < 3 THEN high := 3 END;
    i := 2; WHILE i < high DO tab[i] := 0; INC(i) END;
    AllocConst(tab, high*4, table, 4);
    IF l >= 0 THEN links[l].pos := SHORT(table) END
  END AllocCaseTable;

  PROCEDURE AllocLinkTable* (noMod: LONGINT);
    VAR x: ARRAY 32 OF LONGINT; i: LONGINT;
  BEGIN
    i := 0; WHILE i < 32 DO x[i] := 0; INC(i) END;
    AllocConst(x, noMod*4, linkTable, 4)
  END AllocLinkTable;

  PROCEDURE ParamAdr* (VAR firstPar: PLT.Object);
    VAR
      par: PLT.Object; typ: PLT.Struct;
      padr, vadr: LONGINT; f, c: INTEGER; pused: SET;

    PROCEDURE Alloc (ps, vs: LONGINT);
    BEGIN
      IF (par^.mode # VarPar) & (typ^.form IN {Real, LReal}) & (f <= 13) THEN
        par^.adr := -1-(FReg*32+f); INCL(pused, f+16); INC(f)
      ELSIF (padr + ps <= 11*4) THEN
        par^.adr := -1-(Reg*32+padr DIV 4); pused := pused + {(padr+4) DIV 4 .. (padr+ps) DIV 4}
      ELSE par^.adr := padr+12
      END;
      IF vs = 0 THEN par^.linkadr := memTag+padr-12
      ELSE Align(vadr, Base(typ)); par^.linkadr := vadr; INC(vadr, vs)
      END;
      INC(padr, ps)
    END Alloc;

  BEGIN
    padr := 3*4; vadr := 0; par := firstPar.par; f := 1; pused := {};
    WHILE par # NIL DO
      typ := par^.typ;
IF typ=NIL THEN (* HALT(77) *) ELSE
      c := typ^.comp; TypSize(typ);
      IF c = DynArr THEN Alloc(typ^.size, 0);
      ELSIF (par^.mode = VarPar) THEN
        IF c = Record THEN Alloc(8, 0)
        ELSE Alloc(4, 0)
        END
      ELSE
        IF c IN {Record, Array} THEN Alloc(4, typ^.size)
        ELSIF typ^.form IN {LReal, ProcTyp} THEN Alloc(8, 0)
        ELSE Alloc(4, 0)
        END
      END;
END;
      par := par.nxtobj;
    END;
    DEC(padr, 3*4); Align(padr, 8); Align(vadr, 8);
    firstPar.ival:=padr*10000H ; firstPar.intval2:=vadr ; firstPar.setval:=pused;
  END ParamAdr;

  PROCEDURE VarAdr* (var: PLT.Object; VAR varSize : LONGINT);
    VAR adr: LONGINT; typ: PLT.Struct;
  BEGIN
    adr := varSize;
    WHILE var # NIL DO
      IF var.mode=Var THEN
        typ := var^.typ; TypSize(typ);
        Align(adr, Base(typ)); var.adr := adr; var.linkadr := adr; INC(adr, typ.size);
      END;
      var := var.nxtobj;
    END;
    Align(adr, 8); varSize:=adr;
  END VarAdr;

  PROCEDURE AllocGlobalVar*(publics, globals: PLT.Object);
    VAR adr, size : LONGINT; nofptr: INTEGER; obj : PLT.Object;
  BEGIN
    adr:=0; nofptr:=0; obj:=publics;
    WHILE obj#NIL DO
      IF obj.mode=Var THEN
        size:=obj.typ.size; INC(nofptr, obj.typ.nofptr);
        Align(adr, Base(obj.typ));
        obj.adr:=-adr-1; obj.linkadr:=adr; INC(adr, size)
      END;
      obj:=obj.nxtobj
    END;
    obj:=globals;
    WHILE obj#NIL DO
      IF (obj.mode=Var) & (obj.adr=0) THEN
        size:=obj.typ.size; INC(nofptr, obj.typ.nofptr);
        Align(adr, Base(obj.typ));
        obj.adr:=adr; obj.linkadr:=adr; INC(adr, size)
      ELSIF (obj.mode=Var) THEN obj.adr:=obj.linkadr END;
      obj:=obj.nxtobj
    END;
    Align(adr, 8);
    dsize:=adr;
  END AllocGlobalVar;

  PROCEDURE Traverse*(obj: PLT.Object);
    VAR typ: PLT.Struct; tobj: PLT.Object;
  BEGIN
    tobj:=obj;
    (* calculate type sizes *)
    WHILE tobj#NIL DO
      IF tobj.mode IN {TypDynArr, TypArray, TypProcTyp, TypPointer, TypRecord} THEN TypSize(tobj.typ) END;
      tobj:=tobj.nxtobj
    END;
    (* calculate addresses *)
    WHILE obj#NIL DO
      typ:=obj.typ;
      CASE obj.mode OF
      | TypDynArr:
      | TypRecord: IF typ.tdadr=0 THEN AllocTypDesc(typ) END;
      | TypProcTyp: ParamAdr(obj);
      | LProc, XProc: ParamAdr(obj); obj.linkadr:=-1;
        IF (obj.mode=XProc) & (obj.adr=0) THEN INC(obj.adr, LONG(entno)); INC(entno)
        ELSIF obj.mode=LProc THEN obj.adr:=-1 END;
      ELSE
      END;
      obj:=obj.nxtobj
    END
  END Traverse;

  PROCEDURE Put* (instr: LONGINT);
  BEGIN code[pc] := instr; INC(pc)
  END Put;

  PROCEDURE Link* (VAR link: LONGINT; mod, ent: CHAR): LONGINT;
    VAR l, v: LONGINT;
  BEGIN
    l := link;
    IF l = -1 THEN
      IF noflk < MaxLinks THEN
        l := noflk; INC(noflk); links[l].pos := 0; links[l].mod := mod; links[l].ent := ent
      ELSE err(231); l := 0
      END
    END;
    link := l; v := links[l].pos; links[l].pos := SHORT(-pc); RETURN v
  END Link;

  PROCEDURE PutLCall* (VAR x: Item);
    VAR p: LONGINT;
  BEGIN
    IF x.mode = XProc THEN p := entry[x.offset] ELSE p := x.offset END;
    IF p < -1 THEN Put(iB+(p MOD 1000000H)*4+fLK)
    ELSIF p = -1 THEN Put(iB+fLK)
    ELSE Put(iB+((p-pc) MOD 1000000H)*4+fLK)
    END;
    IF p < 0 THEN
      IF x.mode = XProc THEN entry[x.offset] := SHORT(1-pc) ELSE x.offset := 1-pc END
    END
  END PutLCall;

  PROCEDURE PutXCall* (VAR x: Item);
    VAR lval: LONGINT;
  BEGIN
    lval:=(x.adr - PC) DIV 4 - pc;
    Put(iB+(lval MOD 1000000H)*4+fLK)
  END PutXCall;

  PROCEDURE LoadProcAddr* (VAR x: Item; rt: LONGINT);
    VAR t: LONGINT; lval, val: LONGINT;
  BEGIN
    IF x.mnolev < 0 THEN lval := x.adr
    ELSE
      IF entry[x.offset] >= 0 THEN lval := PC+(4*entry[x.offset])
      ELSE
        lval := fixProc.linkadr;
        IF lval = -1 THEN INC(lval) ELSE lval := pc - lval END;
        fixProc.linkadr := pc;
      END
    END;
    t := GetTempR(); FreeTempR(t);
    val:=lval DIV LowWord;
    IF lval MOD LowWord>32767 THEN INC(val) END;
    (* eventuell muss hier R0 geloescht werden *)
    Put(iCAU+t*fRT+ val);
    IF rt < 0 THEN rt := GetTempR() END;
    Put(iCAL+rt*fRT+t*fRA + lval MOD LowWord);
    x.mode := Reg; x.reg := rt; x.typ := PLT.linttyp;
  END LoadProcAddr;

  PROCEDURE SaveRegisters* (VAR x: Item; VAR saved: SaveDesc; VAR sSize: LONGINT);
    VAR offset, i: LONGINT; toSave: SET;
  BEGIN
    offset := saveStart; toSave := TempFRegs-TempF; saved.savedF := toSave; i := 0;
    REPEAT
      IF i IN toSave THEN DEC(offset, 8); Put(iSTFD+i*fFRS+FP*fRA+(offset MOD LowWord)) END;
      INC(i)
    UNTIL i = 32;
    toSave := TempRegs-TempR;
    saved.savedR := toSave; i := 0;
    REPEAT
      IF i IN toSave THEN DEC(offset, 4); Put(iST+i*fRS+FP*fRA+(offset MOD LowWord)) END;
      INC(i)
    UNTIL i = 32;
    TempR := TempRegs; TempF := TempFRegs; saved.ParR := ParR; saved.ParF := ParF; ParR := {}; ParF := {};
    saved.offset := offset; saveStart := offset;
    offset := (-offset)-SLsize; IF sSize < offset THEN sSize := offset END;
  END SaveRegisters;

  PROCEDURE RestoreRegisters* (VAR x: Item; VAR saved: SaveDesc; rt: LONGINT);
    VAR offset, i: LONGINT; toRest: SET;
  BEGIN
    TempR := TempRegs-saved.savedR; TempF := TempFRegs-saved.savedF; ParR := saved.ParR; ParF := saved.ParF;
    offset := saved.offset; toRest := saved.savedR;
    IF x.typ^.form = ProcTyp THEN
      IF {3,4}*toRest # {} THEN
        IF rt < 0 THEN rt := GetTempRegs(2, {}) END;
        Put(iMR+3*fRA+rt*fRT); Put(iMR+4*fRA+(rt+1)*fRT); x.reg := rt
      ELSE TempR := TempR - {3,4}
      END
    ELSIF x.mode = Reg THEN
      IF 3 IN toRest THEN
        IF rt < 0 THEN rt := GetTempR() END;
        Put(iMR+3*fRA+rt*fRT); x.reg := rt
      ELSE EXCL(TempR, 3)
      END
    END;
    i := 31;
    REPEAT
      IF i IN toRest THEN Put(iL+i*fRT+FP*fRA+(offset MOD LowWord)); INC(offset, 4) END;
      DEC(i)
    UNTIL i < 0;
    toRest := saved.savedF;
    IF x.mode = FReg THEN
      IF 1 IN toRest THEN
        IF rt < 0 THEN rt := GetTempF() END;
        Put(iFMR+1*fFRB+rt*fFRT); x.reg := rt
      ELSE EXCL(TempF, 1)
      END
    END;
    i := 31;
    REPEAT
      IF i IN toRest THEN Put(iLFD+i*fFRT+FP*fRA+(offset MOD LowWord)); INC(offset, 8) END;
      DEC(i)
    UNTIL i < 0;
    saveStart := offset
  END RestoreRegisters;

  PROCEDURE FixCase* (low, high, table: LONGINT); (* note: this procedure is dependent on big-endian ordering *)
    VAR adr: LONGINT; val: LONGINT;
  BEGIN
    val := (pc*4) + PC;
    adr := SYS.ADR(constant[ConstLength+table+low*4]);
    WHILE low <= high DO SYS.PUT(adr, val); INC(low); INC(adr, 4) END
  END FixCase;

  PROCEDURE SetCaseBranch* (table: LONGINT);  (* note: this procedure is dependent on big-endian ordering *)
    VAR adr: LONGINT; val: LONGINT;
  BEGIN
    val := (pc*4) + PC;
    adr := SYS.ADR(constant[ConstLength+table+2*4]);
    SYS.PUT(adr-2, val)
  END SetCaseBranch;

  PROCEDURE Fixup* (VAR l: Label);
    VAR ll, instr, link, op, assh: LONGINT;
  BEGIN
    IF l # 0 THEN ll := (l MOD LowWord) + 0FFFF0000H ELSE ll := 0 END;
    WHILE ll # 0 DO
      instr := code[-ll]; link := instr MOD 4000000H; op := instr-link;
      assh := SYS.LSH(op, -26); ASSERT((assh = 16) OR (assh = 18));
      IF op = iB THEN code[-ll] := op+(pc+ll)*4+fLK
      ELSE code[-ll] := instr-(instr MOD LowWord)+(pc+ll)*4
      END;
      ll := instr DIV 4 MOD 4000H;
      IF ll # 0 THEN INC(ll, 0FFFFC000H) END
    END;
    l := SHORT(pc)
  END Fixup;

  PROCEDURE FixupProcAsgn* (l: LONGINT);
    VAR instr1, instr2, link, lval, val: LONGINT;
  BEGIN
    link:=l;
    WHILE link # 0 DO
      instr1 := (code[l] DIV LowWord)*10000H; instr2 := code[l+1];
      link := instr2 MOD LowWord; instr2 := (instr2 DIV LowWord)*10000H;

      lval := PC + 4*pc; val:=lval DIV LowWord;
      IF lval MOD LowWord>32767 THEN INC(val) END;
      code[l]:=instr1 + val; code[l+1]:=instr2 +  lval MOD LowWord;

      l := l - link;
    END
  END FixupProcAsgn;

  PROCEDURE SetTrap* (trapno: INTEGER);
  BEGIN
    IF noftraps < MaxTraps THEN
      Traps[noftraps].no := trapno; Traps[noftraps].pc := SHORT(pc); INC(noftraps)
    ELSE err(236)
    END
  END SetTrap;

  PROCEDURE GenProcEntry* (fsize, ralloc, falloc, calloc, FP: LONGINT; leaf, nested: BOOLEAN);
    VAR t1, t2: LONGINT; p: Item;
  BEGIN
    IF ~leaf THEN Put(iMFSPR+spLR*fSPR) END;
    Put(iSTM+(ralloc+1)*fRS+SP*fRA+((ralloc-31) MOD 4000H)*4);
    IF falloc < 31 THEN
      ASSERT(12 IN TempR);
      t1 := (32-ralloc-(ralloc MOD 2))*4+(32-falloc)*8; Put(iCAL+12*fRT+SP*fRA+((-t1) MOD LowWord));
      p.mode := XProc; p.adr:=SYS.ADR(SaveFProc)+(falloc+1)*4; PutXCall(p)
    END;
    IF calloc < 19 THEN t1 := GetTempR(); FreeTempR(t1); Put(iMFCR+t1*fRT) END;
    IF ~leaf THEN Put(iST+SP*fRA+8) END;
    IF calloc < 19 THEN Put(iST+t1*fRS+SP*fRA+4) END;
    procStart := pc;
    IF fsize < 32767-512 THEN
      Put(iSTU+SP*fRS+SP*fRA)
    ELSE
      t1 := GetTempR(); FreeTempR(t1); Put(iCAU+t1*fRT);
      t2 := GetTempR(); FreeTempR(t2); Put(iCAL+t2*fRT+t1*fRA);
      Put(iSTUX+SP*fRT+SP*fRA+t2*fRB)
    END;
    Put(iCAL+FP*fRT+SP*fRA); saveStart := 0; SLsize := 0;
    IF ~leaf THEN Put(iST+SB*fRS+SP*fRA+20) END;  (* save SB *)
    IF nested THEN saveStart := -8; SLsize := 8 END
  END GenProcEntry;

  PROCEDURE GenProcExit* (fsize, psize, ralloc, falloc, calloc, FP: LONGINT; leaf: BOOLEAN);
    VAR u, l, t: LONGINT; SPreset: BOOLEAN; p: Item;
  BEGIN
    IF psize > 512-6*4 THEN err(302) END;
    IF fsize < 32767-512 THEN
      INC(code[procStart], (-fsize-psize) MOD LowWord); INC(code[procStart+1], psize)
    ELSE
      u := -fsize-psize; l := u MOD LowWord; u := (SYS.LSH(u, -16)+SYS.LSH(l, -15)) MOD LowWord;
      INC(code[procStart], u); INC(code[procStart+1], l); INC(code[procStart+3], psize)
    END;
    SPreset := fsize >= 32767-512;
    IF SPreset THEN Put(iL+SP*fRT+SP*fRA); fsize := 0; FP := SP END;
    IF ~leaf THEN Put(iL+FP*fRA+fsize+8) END;
    IF calloc < 19 THEN t := GetTempR();
      IF (falloc < 31) & (t = 12) THEN FreeTempR(t); t := GetTempR() END;
      Put(iL+t*fRT+FP*fRA+fsize+4)
    END;
    IF ~SPreset THEN Put(iL+SP*fRT+SP*fRA) END;
    IF falloc < 31 THEN
      ASSERT(12 IN TempR);
      u := (32-ralloc-(ralloc MOD 2))*4+(32-falloc)*8; Put(iCAL+12*fRT+SP*fRA+((-u) MOD LowWord));
      p.mode := XProc;
      p.adr:=SYS.ADR(RestFProc)+(falloc+1)*4; PutXCall(p)
    END;
    IF ~leaf THEN Put(iMTSPR+spLR*fSPR) END;
    IF calloc < 19 THEN FreeTempR(t); Put(iMTCR+t*fRS) END;
    Put(iLM+(ralloc+1)*fRS+SP*fRA+((ralloc-31) MOD 4000H)*4);
    Put(iBCR+cALWAYS*fBO)
  END GenProcExit;

  PROCEDURE FixupFP* (FPlink, FPlink4: Label; psize: LONGINT);
    VAR h: LONGINT;
  BEGIN
    WHILE FPlink # 0 DO
      h := code[-FPlink]; code[-FPlink] := h-(h MOD LowWord)+psize;
      FPlink := SHORT(ASH(SYS.LSH(h, 16), -16))
    END;
    WHILE FPlink4 # 0 DO
      h := code[-FPlink4]; code[-FPlink4] := h-(h MOD LowWord)+psize-4;
      FPlink4 := SHORT(ASH(SYS.LSH(h, 16), -16))
    END
  END FixupFP;

  PROCEDURE EndStat*;
  BEGIN
    ASSERT((TempR = TempRegs) & (TempF = TempFRegs) & (TempCRF = TempCRFields) &
        (TempCRB = {}) & (ParR = {}) & (ParF = {}) & (HoldR = {}))
  END EndStat;
(*
  PROCEDURE OutNum (i: LONGINT);
  BEGIN
    WHILE (i < -64) OR (i > 63) DO
      RefW(CHR(i MOD 128 + 128)); i := i DIV 128
    END;
    RefW(CHR(i MOD 128))
  END OutNum;

  PROCEDURE OutRefPoint* (fsize, psize, ralloc, falloc, calloc: LONGINT; leaf: BOOLEAN);
  BEGIN
    RefW(0F8X); OutNum(pc);
    OutNum(fsize); OutNum(psize); OutNum(ralloc); OutNum(falloc); OutNum(calloc);
    RefW(SYS.VAL(CHAR, leaf))
  END OutRefPoint;

  PROCEDURE OutRefName* (name: ARRAY OF CHAR);
    VAR ch: CHAR; i: INTEGER;
  BEGIN i := 0;
    REPEAT ch := name[i]; RefW(ch); INC(i) UNTIL ch = 0X
  END OutRefName;

  PROCEDURE OutRefs* (obj: PLT.Object);
    VAR f: SHORTINT;
  BEGIN
    WHILE obj # NIL DO
      IF (obj^.mode = Var) OR (obj^.mode = VarPar) THEN
        f := obj^.typ^.form;
        IF (f IN {Byte .. Set, Pointer})
          OR (obj^.typ^.comp = Array) & (obj^.typ^.BaseTyp^.form = Char) & (obj^.typ^.size <= 32) THEN
          IF obj^.mode = Var THEN RefW(1X) ELSE RefW(3X) END ;
          IF obj^.typ^.comp = Array THEN RefW(0FX)
          ELSE RefW(SYS.VAL(CHAR, f))
          END;
          OutNum(obj^.linkadr);
          OutRefName(obj^.name)
        END
      END;
      obj:=obj.nxtobj;
    END
  END OutRefs;
*)
  PROCEDURE FindPtrs* (typ: PLT.Struct; adr: LONGINT; VAR tab: ARRAY OF LONGINT; VAR last: INTEGER);
    VAR fld: PLT.Object; btyp: PLT.Struct; i, n: LONGINT;
  BEGIN
    IF typ.form = Pointer THEN
      IF (typ.sysflag=0) & (last < LEN(tab)) THEN tab[last] := adr; INC(last) END
    ELSIF typ.comp = Record THEN
      btyp := typ^.BaseTyp; fld := typ.dsc;
      IF btyp # NIL THEN FindPtrs(btyp, adr, tab, last) END ;
      WHILE (fld # NIL) & (fld.mode=Fld) DO
        FindPtrs(fld.typ, fld.adr + adr, tab, last);
        fld := fld.nxtobj
      END
    ELSIF typ.comp = Array THEN
      btyp := typ^.BaseTyp; n := typ^.n; i:=0;
      WHILE i < n DO FindPtrs(btyp, adr, tab, last); INC(adr, btyp.size); INC(i) END
    END
  END FindPtrs;

  PROCEDURE Close*;
    VAR i: INTEGER;
  BEGIN i := 0;
    WHILE i < MaxRecs DO recTab[i] := NIL; INC(i) END
  END Close;

  PROCEDURE MakeTypeDescs*(VAR noftds : INTEGER; VAR typedescs : LONGINT; M : Modules.Module);
  VAR
    i, nofptrs : INTEGER; typ, btyp : PLT.Struct; ptrTab: ARRAY 1025 OF LONGINT;  (* mfix *)
    negpart, tdsize, p, val, j, h, mthno, mentno : LONGINT; supertag : SuperTag; tag, basetag : Tag; basemod, baseadr, ent : INTEGER;
    base : Modules.Module; go : BOOLEAN;
    nofnewmth: INTEGER; NewMthTab: ARRAY MaxEntry OF PLT.Object;

    PROCEDURE FindNewMths (obj: PLT.Object);
    BEGIN
      WHILE obj # NIL DO
        IF obj^.mode = TProc THEN NewMthTab[nofnewmth] := obj; INC(nofnewmth) END ;
        obj := obj.nxtobj;
      END
    END FindNewMths;

  BEGIN
    noftds:=nofrec; Kernel.AllocBlock(typedescs, -4*nofrec);
    i:=0; WHILE i<nofrec DO
      typ:=recTab[i]; nofptrs:=0; FindPtrs(typ, 0, ptrTab, nofptrs);
      btyp:=typ.BaseTyp;
      IF btyp=NIL THEN basemod:=-1; baseadr:=-1 ELSE basemod:=PLT.GetTypMno(btyp); baseadr:=SHORT(btyp.tdadr) END;
      negpart:=4*(MaxExts+2) + (*nofmth*) typ.n * 8;
      tdsize:=4 + SIZE(SuperDescriptor) + negpart + SIZE(TypeDescriptor) + nofptrs*4;
      Kernel.AllocBlock(p, -tdsize); p:=p+4;
      supertag:=SYS.VAL(SuperTag, p);
      val:=1; SYS.PUT(p-4, val);  (* Mark *)
      tag:=SYS.VAL(Tag, p + SIZE(SuperDescriptor) + negpart);
      supertag.tdsize:=SIZE(SuperDescriptor) + nofptrs*4 + negpart;
      supertag.ptroff:=-4; supertag.tag:=tag; supertag.nofmth:=SHORT(SHORT(typ.n));
      IF ~ODD(p) THEN val:=p+1 ELSE val:=p END;
      SYS.PUT(SYS.VAL(LONGINT, tag) - 4, val);
      tag.recsize:=typ.size;
      supertag.module:=M; COPY(typ.strobj.name, supertag.typename);
      SYS.PUT(SYS.VAL(LONGINT, tag)-8, basemod);
      SYS.PUT(SYS.VAL(LONGINT, tag)-6, baseadr);
      SYS.MOVE(SYS.ADR(ptrTab), SYS.ADR(tag.ptroff), 4*nofptrs);
      val:=- (nofptrs+1)*4;
      SYS.PUT(SYS.ADR(tag.ptroff)+(4*nofptrs), val);
      val:=SYS.VAL(LONGINT, tag); SYS.PUT(typedescs+(4*i), val); SYS.PUT(M.SB+typ.tdadr, val);

      j := 0; WHILE j < typ.n DO SYS.PUT(SYS.VAL(LONGINT, tag)-12-(MaxExts+j*2)*4, LONG(LONG(-1))); INC(j) END;
      nofnewmth := 0; FindNewMths(typ.dsc);
      WHILE nofnewmth > 0 DO DEC(nofnewmth);
        mthno := NewMthTab[nofnewmth].adr DIV 10000H;
        mentno := NewMthTab[nofnewmth].adr MOD 10000H;
        SYS.PUT(SYS.VAL(LONGINT, tag)-12-(MaxExts+mthno*2)*4, mentno);
      END;

      INC(i);
    END;

    i:=0;
    WHILE i<nofrec DO
      SYS.GET(typedescs+(4*i), tag);
      SYS.GET(SYS.VAL(LONGINT, tag)-8, basemod);
      SYS.GET(SYS.VAL(LONGINT, tag)-6, baseadr);
      j:=0; go:=FALSE;
      IF basemod>=0 THEN
        IF basemod=0 THEN
          base:=M;
          j:=0; WHILE (j<noftds)&(recTab[j].tdadr#baseadr) DO INC(j) END;
          ASSERT(j < noftds);
          IF (j>i) THEN
            typ:=recTab[i]; recTab[i]:=recTab[j]; recTab[j]:=typ;
            SYS.GET(typedescs+(4*i), p);
            SYS.GET(typedescs+(4*j), val); SYS.PUT(typedescs+(4*i), val); SYS.PUT(typedescs+(4*j), p);
            (* Continue *) go:=TRUE;
          END;
        ELSE
          ASSERT(basemod <= M.nofimp);
          base:=SYS.VAL(Modules.Module, M.import[basemod-1]);
        END;
        IF ~go THEN
          SYS.GET(base.SB+baseadr, basetag);
          j:=0; SYS.GET(SYS.VAL(LONGINT, basetag)-8-(4*j), val);
          WHILE val#0 DO
            SYS.PUT(SYS.VAL(LONGINT, tag)-8-(4*j), val);
            INC(j); SYS.GET(SYS.VAL(LONGINT, basetag)-8-(4*j), val);
          END;
        END;
      END;
      IF ~go THEN
        SYS.PUT(SYS.VAL(LONGINT, tag)-8-(4*j), tag);
        SYS.GET(SYS.VAL(LONGINT, tag)-4, supertag);
        IF ODD(SYS.VAL(LONGINT,supertag)) THEN DEC(SYS.VAL(LONGINT, supertag)) END;
        INC(j); supertag.extlevel:=SHORT(SHORT(j));
        WHILE (j<16) DO SYS.PUT(SYS.VAL(LONGINT, tag)-8-(4*j), 0); INC(j) END;

        j := 0;
        WHILE j < supertag.nofmth DO
          SYS.GET(SYS.VAL(LONGINT, tag)-12-(MaxExts+j*2)*4, mentno);
          IF mentno < 0 THEN  (* inherited *)
            SYS.GET(SYS.VAL(LONGINT, basetag)-12-(MaxExts+j*2)*4, h);
            SYS.PUT(SYS.VAL(LONGINT, tag)-12-(MaxExts+j*2)*4, h);
            SYS.GET(SYS.VAL(LONGINT, basetag)-12-(MaxExts+j*2)*4+4, h);
            SYS.PUT(SYS.VAL(LONGINT, tag)-12-(MaxExts+j*2)*4+4, h);
          ELSE  (* overwritten *)
            SYS.GET(M.entries+mentno*2, ent);
            SYS.PUT(SYS.VAL(LONGINT, tag)-12-(MaxExts+j*2)*4, ent*4+M.PC);
            SYS.PUT(SYS.VAL(LONGINT, tag)-12-(MaxExts+j*2)*4+4, M.SB);
          END;
          INC(j)
        END;

        INC(i)
      END;
    END;
  END MakeTypeDescs;

  PROCEDURE Open*;
    VAR i : LONGINT;
  BEGIN
    pc := 0; conx := ConstLength; nofrec := 0; level := 0;
    TempR := TempRegs; TempF := TempFRegs; TempRpos := 0; TempFpos := 0; dsize := 0; entno := 1;
    TempCRF := TempCRFields; TempCRB := {}; TempCRFpos := 0; TempCRBpos := 0; ParR := {}; ParF := {};
    CRF0used := FALSE; HoldR := {};
    i := 0; WHILE i < MaxEntry DO entry[i] := -1; INC(i) END;
    noflk := 0; noftraps := 0; CaseLink := -1;
    refSize:=0;
  END Open;

  PROCEDURE Init;
    VAR i, instr : LONGINT;
  BEGIN
    instr:=0DC0C0008H;
    FOR i:=0 TO 31 DO SaveFProc[i]:=instr; INC(instr, 00200000H) END;
    SaveFProc[32]:=04E800020H;
    instr:=0CC0C0008H;
    FOR i:=0 TO 31 DO RestFProc[i]:=instr; INC(instr, 00200000H) END;
    RestFProc[32]:=04E800020H;
  END Init;

BEGIN
  Init
END OPLL.Open
