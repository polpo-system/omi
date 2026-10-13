(* ETH Oberon, Copyright 2000 ETH Zürich Institut für Computersysteme, ETH Zentrum, CH-8092 Zürich.
Refer to the general ETH Oberon System license contract available at: http://www.oberon.ethz.ch/ *)

MODULE OPLC;  (* mmb 4.3.91 / 20.11.94  / od Jan 95 / tk 9.7.96 *)

  (* 5.7.96 Compare - lscbx. removed *)
  (* 9.7.96 iABS - absfix *)
  (* 8.8.96 Problem in INC with arrays solved *)

  IMPORT
    SYSTEM, PLT:=OPLT, PLL:=OPLL, Kernel;

  CONST
    (* symbol values and ops *)
    TdopEql=1EH; TdopNeq=1FH; TdopLss=20H; TdopLeq=21H; TdopGtr=22H; TdopGeq=23H;
    eql = 9; neq = 10; lss = 11; leq = 12; gtr = 13; geq = 14;

    (* structure forms *)
    Undef = 0; Byte = 1; Bool = 2; Char = 3; SInt = 4; Int = 5; LInt = 6;
    Real = 7; LReal = 8; Set = 9; String = 10; NilTyp = 11; NoTyp = 12;
    Pointer = 13; ProcTyp = 14; Comp = 15;
    (* structure sets *)
    RealTypes = {Real, LReal};

    (* composite structure forms *)
    Basic = 1; Array = 2; DynArr = 3; Record = 4;

    (* item/object modes *)
    Var = 1; Par=2; VarPar = 3; Con = 4; Fld = 5;  LProc = 6; XProc = 7; SProc = 8; CProc = 9; IProc = 10;
    Head = 12; Based = 14; Indexed = 15; Reg = 16; RegSI = 17; FReg = 18; Cond = 19;

    (* compiler options: *)
    powerpc = TRUE; (* use PowerPC instruction set *)

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
    fREC = 1;

    (* condition code bits *)
    bLT = 0; bGT = 1; bEQ = 2; bSO = 3;

    (* special register definitions *)
    SB = 2; SP = 1; SLpar = 11; virtualFP = 32; spCTR = 9; spMQ = 0; spLR = 8; spXER = 1;

    (* opcodes of the POWER architecture *)
    iA =  7C000014H;
    iADDC = iA;
    iABS =  7C0002D0H;
    iAE =  7C000114H;
    iAI =  30000000H;
    iADDIC = iAI;
    iADDICR = 34000000H;
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
    iADDI = iCAL;
    iADD = iCAX;
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
    iDIVW = 7C0003D6H;
    iDOZ =  7C000210H;
    iDOZI =  24000000H;
    iEQV =  7C000238H;
    iEXTS =  7C000734H;
    iEXTSB = 7C000774H;
    iFA = 0FC00002AH;
    iFADDS = 0EC00002AH;
    iFABS = 0FC000210H;
    iFCMPO = 0FC000040H;
    iFCMPU = 0FC000000H;
    iFD = 0FC000024H;
    iFDIVS = 0EC000024H;
    iFM = 0FC000032H;
    iFMULS = 0EC000032H;
    iFMA = 0FC00003AH;
    iFMADDS = 0EC00003AH;
    iFMR = 0FC000090H;
    iFMS = 0FC000038H;
    iFMSUBS = 0EC000038H;
    iFNABS = 0FC000110H;
    iFNEG = 0FC000050H;
    iFNMA = 0FC00003EH;
    iFNMADDS = 0EC00003EH;
    iFNMS = 0FC00003CH;
    iFNMSUBS = 0EC00003CH;
    iFRSP = 0FC000018H;
    iFS = 0FC000028H;
    iFSUBS = 0EC000028H;
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
    iMTXER = iMTSPR+spXER*fSPR;
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
    iSUB = 7C000050H;
    iSVC =  44000000H;
    iT =  7C000008H;
    iTI =  0C000000H;
    iTLBI =  7C000264H;
    iXOR =  7C000278H;
    iXORIL =  68000000H;
    iXORIU =  6C000000H;
    iBCNT = iBC+16*fBO;
    iBDNZ = iBCNT;
    iBDZ = iBC+18*fBO;
    iNOT = iSFI+0FFFFH;
    iUPPER = 4000000H;
    iBT = iBC+15*fBO;
    iBF = iBC+7*fBO;
    iBA = iBC+31*fBO;
    iBCNTNZ = iBC+16*fBO;
    iBCNTNZNM = iBC+0*fBO+bEQ*fBI;
    iBM = iBT+bEQ*fBI;
    iBNM = iBF+bEQ*fBI;
    iLIL = iCAL;

    cALWAYS = 1FH;

    (* trap numbers *)
    IndexCheck = 1; DivideTrap = 2; CaseTrap = 3; TypeGuard = 4; FuncTrap = 5; DimTrap = 6; NilTrap = 7;

    (* trap fields *)
    tUGE = 5; tULE = 6; tNEQ = 27; tEQ = 4; tSLE = 20; tALWAYS = 31;

    LowWord = 10000H;

  VAR
    FP: LONGINT;
    BLI, XLI, BSI, XSI: ARRAY Pointer+1 OF LONGINT;
    IntToRealAddr, RealToIntAddr, scratch: LONGINT;
    IntToRealBlock, RealToIntBlock: ARRAY 16 OF CHAR;
    zero, CAPmask: PLL.Item;
    LoopLevel: INTEGER;
    leaveProc: PLL.Label;
    FPlink, FPlink4: PLL.Label;
    LoopStart, LoopEnd: ARRAY 16 OF PLL.Label;
    CRbit, switch: ARRAY geq-eql+1 OF INTEGER;
    aopSize, sSize, SLsize: LONGINT;

    inxchk*, typchk*, nilchk*, ptrinit*, dbginfo*, initstack*: BOOLEAN;

  PROCEDURE CNTLZ (i: LONGINT): LONGINT;
    VAR j: LONGINT; s: SET;
  BEGIN
    s := SYSTEM.VAL(SET, i); j := 0;
    WHILE ~(j IN s) & (j < 32) DO INC(j) END;
    RETURN j
  END CNTLZ;

  PROCEDURE MoveReg(rt, rs: LONGINT);
  BEGIN
    IF rs # 0 THEN PLL.Put(iCAL+rt*fRT+rs*fRA) ELSE PLL.Put(iAI+rt*fRT+rs*fRA) END
  END MoveReg;

  PROCEDURE IMIN (a, b: LONGINT): LONGINT;
  BEGIN IF a < b THEN RETURN a ELSE RETURN b END
  END IMIN;

  PROCEDURE CheckR (rt: LONGINT): LONGINT;
  BEGIN IF (rt < 0) OR (rt = 1) THEN RETURN PLL.GetTempR() ELSE RETURN rt END
  END CheckR;

  PROCEDURE CheckF (rt: LONGINT): LONGINT;
  BEGIN IF rt < 0 THEN RETURN PLL.GetTempF() ELSE RETURN rt END
  END CheckF;

  PROCEDURE CheckCRB (rt: LONGINT): LONGINT;
  BEGIN IF rt < 0 THEN RETURN PLL.GetTempCRB() ELSE RETURN rt END
  END CheckCRB;

  PROCEDURE CheckVFP (r: LONGINT): LONGINT;
  BEGIN (*IF r = virtualFP THEN PLL.FixMark; RETURN SP ELSE RETURN r END*) RETURN r
  END CheckVFP;

  PROCEDURE^ Load* (VAR x: PLL.Item; rt: LONGINT);

  PROCEDURE^ RegToCond (VAR x: PLL.Item);

  PROCEDURE PutBranchInstr (instr: LONGINT; VAR l: PLL.Label);
    VAR ll: LONGINT;
  BEGIN
    IF l > 0 THEN ll := l-PLL.pc ELSE ll := l END;
    ll := ll MOD 4000H; PLL.Put(instr+ll*4);
    IF l <= 0 THEN l := SHORT(-PLL.pc+1) END
  END PutBranchInstr;

  PROCEDURE PutBranch* (VAR l: PLL.Label);
  BEGIN PutBranchInstr(iBA, l)
  END PutBranch;

  PROCEDURE PutCondBranch* (VAR x: PLL.Item; Tjmp: BOOLEAN);
    VAR pospol: BOOLEAN; cbit, l: LONGINT;
  BEGIN
    IF x.mode = Con THEN
      IF Tjmp = (x.offset # 1) THEN RETURN  (* optimize untaken or taken branches *)
      ELSIF Tjmp THEN PutBranch(x.Tjmp)
      ELSE PutBranch(x.Fjmp)
      END
    END;
    IF x.mode # Cond THEN Load(x, -1); RegToCond(x) END;
    cbit := x.reg; pospol := cbit >= 0; IF ~pospol THEN cbit := -1-cbit END;
    IF Tjmp THEN l := x.Tjmp ELSE l := x.Fjmp END;
    IF l > 0 THEN l := l-PLL.pc END; l := l MOD 4000H; PLL.FreeTempCRBs({cbit});
    IF pospol = Tjmp THEN PLL.Put(iBT+cbit*fBI+l*4) ELSE PLL.Put(iBF+cbit*fBI+l*4) END;
    IF Tjmp THEN
      IF x.Tjmp <= 0 THEN x.Tjmp := SHORT(-PLL.pc+1) END
    ELSE
      IF x.Fjmp <= 0 THEN x.Fjmp := SHORT(-PLL.pc+1) END
    END
  END PutCondBranch;

  PROCEDURE SetLabel* (VAR l: PLL.Label);
  BEGIN
    IF l < 0 THEN PLL.Fixup(l) ELSE l := SHORT(PLL.pc) END
  END SetLabel;

  PROCEDURE MoveCond (VAR x: PLL.Item; rt: LONGINT): LONGINT;
    VAR instr, src: LONGINT; l: PLL.Label;
  BEGIN
    src := x.reg; l := 0;
    IF (x.Tjmp = 0) & (x.Fjmp = 0) THEN
      IF src < 0 THEN src := -1-src; instr := iCRNOR ELSE instr := iCROR END;
      PLL.FreeTempCRBs({src}); rt := CheckCRB(rt); PLL.Put(instr+rt*fBT+src*fBA+src*fBB)
    ELSE
      rt := CheckCRB(rt); PutCondBranch(x, FALSE);
      PLL.Fixup(x.Tjmp); PLL.Put(iCREQV+rt*fBT); PutBranch(l);
      PLL.Fixup(x.Fjmp); PLL.Put(iCRXOR+rt*fBT); PLL.Fixup(l)
    END;
    RETURN rt
  END MoveCond;

  PROCEDURE CondToReg (VAR x: PLL.Item; rt: LONGINT);
    VAR src, t: LONGINT; l: PLL.Label;
  BEGIN
    ASSERT(x.mode = Cond);
    src := x.reg;
    IF (x.Tjmp = 0) & (x.Fjmp = 0) THEN
      src := x.reg; IF src < 0 THEN src := MoveCond(x, -1) END;
      PLL.FreeTempCRBs({src}); t := PLL.GetTempR(); PLL.Put(iMFCR+t*fRT);
      PLL.FreeTempR(t); rt := CheckR(rt); PLL.Put(iRLINM+rt*fRA+t*fRS+((src+1) MOD 32)*fSH+31*fMB+31*fME);
    ELSE
      rt := CheckR(rt); PutCondBranch(x, FALSE);
      SetLabel(x.Tjmp); PLL.Put(iCAL+rt*fRT+1); l := 0; PutBranch(l);
      SetLabel(x.Fjmp); PLL.Put(iCAL+rt*fRT); SetLabel(l)
    END;
    x.mode := Reg; x.reg := rt
  END CondToReg;

  PROCEDURE RegToCond (VAR x: PLL.Item);
    VAR src, t: LONGINT;
  BEGIN
    ASSERT(x.mode IN {Reg, RegSI});
    src := x.reg; PLL.FreeTempR(src); t := PLL.GetTempCRF(); PLL.Put(iCMPI+t*fBF+src*fRA+0);  (* << mmb 16.12.91 *)
    t := t*4; PLL.FreeTempCRBs({t..t+3}-{t+bEQ}); x.mode := Cond; x.reg := -1-(t+bEQ)
  END RegToCond;

  PROCEDURE FindFP (curlev, tofind, rt: LONGINT): LONGINT;
    VAR y: PLL.Item;
  BEGIN
    ASSERT(curlev >= tofind);
    IF curlev = tofind THEN RETURN FP
    ELSE
      y.mode := Based; y.reg := FP; y.offset := -4; y.typ := PLT.linttyp; y.dreg := -1;
      WHILE curlev > tofind+1 DO Load(y, -1); y.mode := Based; y.offset := -4; DEC(curlev) END;
      Load(y, rt); RETURN y.reg
    END
  END FindFP;

  PROCEDURE ReduceIndex (VAR x: PLL.Item; inx, rt: LONGINT);
    VAR src: LONGINT;
  BEGIN
    ASSERT(x.mode IN {Indexed, Based});
    src := x.reg; PLL.FreeTempR(src); PLL.FreeTempR(inx); rt := CheckR(rt);
    PLL.Put(iCAX+rt*fRT+src*fRA+inx*fRB); x.reg := rt
  END ReduceIndex;

  PROCEDURE BaseOrInx (VAR x: PLL.Item; rt: LONGINT);
    VAR offset, mnolev, t: LONGINT; typ: PLT.Struct; DArr: BOOLEAN;
  BEGIN
    DArr := x.typ.comp = DynArr;
    CASE x.mode OF
      Based, Indexed:
    |  Var, Par, VarPar:
        mnolev := x.mnolev;
        IF mnolev < 0 THEN
          offset := x.offset; typ := x.typ; x.mode := Based; x.reg := SB;
          x.offset := -(mnolev*4) + PLL.linkTable; x.typ := PLT.linttyp;
          t := rt; IF offset # 0 THEN t := -1 END;
          Load(x, t); x.mode := Based; x.offset := offset; x.typ := typ
        ELSIF mnolev = 0 THEN
          x.mode := Based; x.reg := SB
        ELSIF (x.mode = VarPar) OR DArr THEN
          x.reg := FindFP(PLL.level, x.mnolev, -1);
          IF DArr THEN t := x.reg; offset := x.offset END;
          x.mode := Based; typ := x.typ; x.typ := PLT.linttyp; Load(x, -1);
          x.mode := Based; x.offset := 0; x.typ := typ;
          IF DArr THEN x.dreg := SHORT(SHORT(t)); x.adr := offset; x.dmode := Based END
        ELSE
          x.reg := FindFP(PLL.level, x.mnolev, -1); x.mode := Based
        END
    ELSE HALT(33)   (* illegal use of object *)
    END
  END BaseOrInx;

  PROCEDURE Base (VAR x: PLL.Item; rt: LONGINT);
  BEGIN
    IF x.mode = Indexed THEN ReduceIndex(x, x.offset, rt); x.mode := Based; x.offset := 0 ELSE BaseOrInx(x, rt) END;
    ASSERT(x.mode = Based);
  END Base;

  PROCEDURE ShortBase (VAR x: PLL.Item; rt: LONGINT);
    VAR u, l, base: LONGINT;
  BEGIN
    ASSERT(x.mode = Based);
    u := x.offset; l := u MOD LowWord; u := (SYSTEM.LSH(u, -16)+SYSTEM.LSH(l, -15)) MOD LowWord;
    IF u # 0 THEN
      base := x.reg; PLL.FreeTempR(base); rt := CheckR(rt); PLL.Put(iCAU+rt*fRT+base*fRA+u); x.reg := rt;
      x.offset := ASH(SYSTEM.LSH(l, 16), -16)
    END;
  END ShortBase;

  PROCEDURE MakeReg (VAR x: PLL.Item; rt: LONGINT);
    VAR s: LONGINT;
  BEGIN
    ASSERT(x.mode IN {Reg, RegSI});
    IF x.mode = RegSI THEN
      s := x.reg; PLL.FreeTempR(s);
      rt := CheckR(rt); PLL.Put(iEXTSB+rt*fRA+s*fRS);
      x.reg := rt; x.mode := Reg
    END
  END MakeReg;

  PROCEDURE LoadAddr* (VAR x: PLL.Item; rt: LONGINT);
    VAR u, l, base, inx, t: LONGINT;
  BEGIN
    BaseOrInx(x, rt); base := x.reg;
    IF x.mode = Based THEN
      u := x.offset; l := u MOD LowWord; u := (SYSTEM.LSH(u, -16)+SYSTEM.LSH(l, -15)) MOD LowWord;
      IF u # 0 THEN
        ASSERT(base # virtualFP);
        PLL.FreeTempR(base);
        IF l # 0 THEN
          t := PLL.GetTempR(); PLL.Put(iCAU+t*fRT+base*fRA+u);
          PLL.FreeTempR(t); rt := CheckR(rt); PLL.Put(iCAL+rt*fRT+t*fRA+l)
        ELSE
          rt := CheckR(rt); PLL.Put(iCAU+rt*fRT+base*fRA+u)
        END
      ELSIF l # 0 THEN
        base := CheckVFP(base); PLL.FreeTempR(base); rt := CheckR(rt); PLL.Put(iCAL+rt*fRT+base*fRA+l)
      ELSIF base = 0 THEN (* load constant 0 *)
        rt := CheckR(rt); PLL.Put(iCAL+rt*fRT)
      ELSE rt := base (* do not move *)
      END
    ELSE
      ASSERT(base # virtualFP); inx := x.offset;
      PLL.FreeTempR(base); PLL.FreeTempR(inx); rt := CheckR(rt); PLL.Put(iCAX+rt*fRT+base*fRA+inx*fRB)
    END;
    IF x.dreg # -1 THEN PLL.UnholdTempR(x.dreg);
      IF x.dreg # rt THEN PLL.FreeTempR(x.dreg) END;
      x.dreg := -1
    END;
    x.mode := Reg; x.reg := rt; x.typ := PLT.linttyp
  END LoadAddr;

  PROCEDURE Load* (VAR x: PLL.Item; rt: LONGINT);
    VAR form, base: LONGINT; RealType: BOOLEAN;
  BEGIN
    form := x.typ^.form; RealType := form IN RealTypes;
    ASSERT(x.typ^.form IN {Byte, Bool, Char, SInt, Int, LInt, Real, LReal, Set, NilTyp, Pointer});
    CASE x.mode OF
      Reg, RegSI, FReg, Cond:
        rt := x.reg
    |  Var, VarPar, Par, Based:
        BaseOrInx(x, -1); ShortBase(x, -1);
        ASSERT(x.mode = Based);
        base := x.reg; PLL.FreeTempR(base); base := CheckVFP(base);
        IF RealType THEN rt := CheckF(rt); x.mode := FReg ELSE rt := CheckR(rt); x.mode := Reg END;
        PLL.Put(BLI[form]+rt*fRT+base*fRA+(x.offset MOD LowWord));
        IF form = SInt THEN x.mode := RegSI END
    |  Indexed:
        base := x.reg; PLL.FreeTempR(base); ASSERT(base # virtualFP);
        IF RealType THEN rt := CheckF(rt); x.mode := FReg ELSE rt := CheckR(rt); x.mode := Reg END;
        PLL.Put(XLI[form]+rt*fRT+base*fRA+x.offset*fRB); PLL.FreeTempR(x.offset);
        IF form = SInt THEN x.mode := RegSI END
    |  Con:
        ASSERT(x.typ^.form IN {Byte, Bool, Char, SInt, Int, LInt, Set, NilTyp, Pointer});
        x.mode := Based; x.reg := 0; LoadAddr(x, rt); rt := x.reg
    ELSE HALT(34)
    END;
    x.reg := rt;
    IF x.dreg # -1 THEN PLL.UnholdTempR(x.dreg);
      IF (x.dreg # rt) OR RealType THEN PLL.FreeTempR(x.dreg) END;
      x.dreg := -1
    END
  END Load;

  PROCEDURE Store (VAR x, y: PLL.Item);
    VAR smode, dmode, dest, src, inx, form: LONGINT;
  BEGIN
    ASSERT((x.typ^.form = y.typ^.form) &
          (x.typ^.form IN {Byte, Bool, Char, SInt, Int, LInt, Real, LReal, Set, Pointer, NilTyp}));
    form := x.typ^.form; smode := y.mode; dmode := x.mode;
    ASSERT(y.mode IN {Reg, RegSI, FReg, Cond});
    IF (form = Bool) & ((y.Tjmp # 0) OR (y.Fjmp # 0)) & (smode # Cond) THEN RegToCond(y); smode := Cond END;
    CASE dmode OF
      Reg, RegSI:
        dest := x.reg;
        IF smode = Cond THEN CondToReg(y, dest) END;
        IF y.mode = RegSI THEN MakeReg(y, dest) END;
        IF y.reg # dest THEN src := y.reg; PLL.FreeTempR(src); MoveReg(dest, src) END
    |  FReg:
        src := y.reg; dest := x.reg; IF src # dest THEN PLL.FreeTempF(src); PLL.Put(iFMR+x.reg*fFRT+src*fFRB) END
    |  Cond:
        dest := x.reg;
        IF smode = Reg THEN RegToCond(y) END;
        IF (y.Tjmp # 0) OR (y.Fjmp # 0) OR (y.reg # dest) THEN y.reg := MoveCond(y, dest); ASSERT(y.reg = dest) END;
    |  Var, VarPar, Par, Based:
        BaseOrInx(x, -1);
        IF smode = Cond THEN CondToReg(y, -1)
        ELSIF smode = RegSI THEN MakeReg(y, -1)
        END;
        ShortBase(x, -1); src := y.reg; dest := x.reg;
        IF smode = FReg THEN PLL.FreeTempF(src) ELSE PLL.FreeTempR(src) END;
        PLL.FreeTempR(dest); PLL.Put(BSI[form]+src*fRS+dest*fRA+(x.offset MOD LowWord))
    |  Indexed:
        IF smode = Cond THEN CondToReg(y, -1)
        ELSIF smode = RegSI THEN MakeReg(y, -1)
        END;
        src := y.reg; dest := x.reg; inx := x.offset;
        IF smode = FReg THEN PLL.FreeTempF(src) ELSE PLL.FreeTempR(src) END;
        PLL.FreeTempR(dest); PLL.FreeTempR(inx); PLL.Put(XSI[form]+src*fRS+dest*fRA+inx*fRB)
    END;
    IF x.dreg # -1 THEN PLL.UnholdTempR(x.dreg); PLL.FreeTempR(x.dreg); x.dreg := -1 END
  END Store;

  PROCEDURE Move (VAR x, y, z: PLL.Item; aligned8: BOOLEAN);
    VAR src, dest, r1, r2, iter, slack, h, l: LONGINT; loop, loopend: PLL.Label;
  BEGIN
    (* this is the long version *)
    loop := 0; loopend := 0;
    IF z.mode = Con THEN
      iter := z.offset DIV 8; slack := z.offset MOD 8;
      r1 := PLL.GetTempRegs(2, {}); r2 := r1+1;
      IF iter > 0 THEN
        Base(x, -1); Base(y, -1);
        (* before entering the pipelined loop, dest is at offset -4, src at offset 0 *)
        DEC(x.offset, 4); LoadAddr(x, -1); LoadAddr(y, -1); src := y.reg; dest := x.reg;
        IF ~(src IN PLL.TempRegs) THEN src := PLL.GetTempR(); MoveReg(src, y.reg) END;
        IF ~(dest IN PLL.TempRegs) THEN dest := PLL.GetTempR(); MoveReg(dest, x.reg) END;
        IF iter > 1 THEN DEC(iter);
          IF iter > 1 THEN
            IF iter > 32767 THEN
              l := iter MOD LowWord; h := (SYSTEM.LSH(iter, -16)+SYSTEM.LSH(l, -15)) MOD LowWord;
              PLL.Put(iCAU+r1*fRT+h); PLL.Put(iCAL+r1*fRT+r1*fRA+l)
            ELSE
              PLL.Put(iCAL+r1*fRT+iter)
            END;
            PLL.Put(iMTSPR+r1*fRS+spCTR*fSPR)
          END;
          PLL.Put(iL+r1*fRT+src*fRA+0);  PLL.Put(iL+r2*fRT+src*fRA+4);
          SetLabel(loop);
          PLL.Put(iST+r1*fRS+dest*fRA+4); PLL.Put(iLU+r1*fRT+src*fRA+8);
          PLL.Put(iSTU+r2*fRS+dest*fRA+8); PLL.Put(iL+r2*fRT+src*fRA+4);
          IF iter > 1 THEN PutBranchInstr(iBCNTNZ, loop) END;
          PLL.Put(iST+r1*fRS+dest*fRA+4); PLL.Put(iST+r2*fRS+dest*fRA+8)
          (* now, dest is at offset -12, and src at offset -8 *)
        ELSE
          PLL.Put(iL+r1*fRT+src*fRA+0); PLL.Put(iL+r2*fRT+src*fRA+4);
          PLL.Put(iST+r1*fRS+dest*fRA+4); PLL.Put(iST+r2*fRS+dest*fRA+8)
          (* as above, dest is at offset -12, src at offset -8 *)
        END;
        IF slack > 0 THEN PLL.Put(iCAL+src*fRT+src*fRA+8); PLL.Put(iCAL+dest*fRT+dest*fRA+12) END
      ELSE
        CASE slack OF
        | 1: x.typ := PLT.sinttyp; y.typ := PLT.sinttyp; Load(y, -1); Store(x, y); slack := 0
        | 2: x.typ := PLT.inttyp; y.typ := PLT.inttyp; Load(y, -1); Store(x, y); slack := 0
        | 4: x.typ := PLT.linttyp; y.typ := PLT.linttyp; Load(y, -1); Store(x, y); slack := 0
        ELSE LoadAddr(x, -1); LoadAddr(y, -1); src := y.reg; dest := x.reg
        END
      END;
      IF slack > 0 THEN
        PLL.Put(iLSI+r1*fRT+src*fRA+slack*fNB); PLL.Put(iSTSI+r1*fRS+dest*fRA+slack*fNB)
      END
    ELSE
      Base(x, -1); Base(y, -1);
      DEC(x.offset, 4); DEC(y.offset, 4); LoadAddr(x, -1); LoadAddr(y, -1); src := y.reg; dest := x.reg;
      r1 := PLL.GetTempRegs(2, {}); r2 := r1+1; Load(z, -1);
      PLL.Put(iRLINM+z.reg*fRS+r1*fRA+29*fSH+3*fMB+31*fME+fREC); PLL.Put(iMTSPR+r1*fRS+spCTR*fSPR);
      IF ~(src IN PLL.TempRegs) THEN src := PLL.GetTempR(); MoveReg(src, y.reg) END;
      IF ~(dest IN PLL.TempRegs) THEN dest := PLL.GetTempR(); MoveReg(dest, x.reg) END;
      IF ~aligned8 THEN
        PLL.Put(iRLINM+z.reg*fRS+r2*fRA+29*fMB+31*fME); PLL.Put(iMTSPR+r2*fRS+spXER*fSPR)
      END;
      PLL.FreeTempR(z.reg); loopend := 0; PutBranchInstr(iBM, loopend); SetLabel(loop);
      PLL.Put(iLU+r1*fRT+src*fRA+4); PLL.Put(iLU+r2*fRT+src*fRA+4);
      PLL.Put(iSTU+r1*fRS+dest*fRA+4); PLL.Put(iSTU+r2*fRS+dest*fRA+4);
      PutBranchInstr(iBCNTNZ, loop); SetLabel(loopend);
      IF ~aligned8 THEN
        slack := PLL.GetTempR(); PLL.Put(iCAL+slack*fRT+4);
        PLL.Put(iLSX+r1*fRT+slack*fRA+src*fRB); PLL.Put(iSTSX+r1*fRS+slack*fRA+dest*fRB);
        PLL.FreeTempR(slack)
      END
    END;
    PLL.FreeTempR(r1); PLL.FreeTempR(r2); PLL.FreeTempR(src); PLL.FreeTempR(dest)
  END Move;

  PROCEDURE CommonDesign* (VAR x: PLL.Item);
  BEGIN
    IF x.mode IN {Var, VarPar, Based, Indexed} THEN
      BaseOrInx(x, -1);
      IF x.mode = Based THEN ShortBase(x, -1) END;
      PLL.HoldTempR(x.reg);
      IF x.mode = Indexed THEN PLL.HoldTempR(x.offset) END;
    END
  END CommonDesign;

  PROCEDURE UnholdCommonDesign* (VAR x: PLL.Item);
  BEGIN
    IF x.mode IN {Based, Indexed} THEN PLL.UnholdTempR(x.reg);
      IF x.mode = Indexed THEN PLL.UnholdTempR(x.offset) END;
    END
  END UnholdCommonDesign;

  PROCEDURE^ Minus* (VAR x, y: PLL.Item; rt: LONGINT);
  PROCEDURE^ Plus* (VAR x, y: PLL.Item; rt: LONGINT);

  PROCEDURE Convert* (VAR x: PLL.Item; dtyp: PLT.Struct; rt: LONGINT; round: BOOLEAN);
    VAR sform, dform, s, t: LONGINT; y, z: PLL.Item;
  BEGIN
    sform := x.typ^.form; dform := dtyp^.form; y.dreg := -1; z.dreg := -1;
    IF sform # dform THEN
      IF sform IN {Byte, Bool, Char, SInt, Int, LInt, Set, Pointer, NilTyp} THEN
        IF dform IN {Byte, Bool, Char, SInt, Int, LInt, Set, Pointer, NilTyp} THEN Load(x, rt)
        ELSE ASSERT(dform IN {Real, LReal});
          Load(x, -1); MakeReg(x, -1);
          IF IntToRealAddr = 0 THEN
            PLL.AllocConst(IntToRealBlock, 16, IntToRealAddr, 8);
            ASSERT((-32768 <= IntToRealAddr) & (IntToRealAddr <= 32767-16))
          END;
          s := x.reg; PLL.FreeTempR(s); t := PLL.GetTempR(); PLL.Put(iXORIU+t*fRA+s*fRS+8000H);
          PLL.FreeTempR(t); PLL.Put(iST+t*fRS+SB*fRA+((IntToRealAddr+12) MOD LowWord));
          x.mode := Based; x.reg := SB; x.offset := IntToRealAddr+8; x.typ := PLT.lrltyp;
          y.mode := Based; y.reg := SB; y.offset := IntToRealAddr; y.typ := PLT.lrltyp; y.dreg := -1;
          Minus(x, y, rt)
        END
      ELSIF ~(dform IN {Real, LReal}) THEN (* ENTIER *)
        IF RealToIntAddr = 0 THEN PLL.AllocConst(RealToIntBlock, 8, RealToIntAddr, 8) END;
        IF scratch < 0 THEN scratch := PLL.dsize; INC(PLL.dsize, 8) END;
        t := PLL.GetTempF(); PLL.Put(iMFFS+t*fFRT); PLL.Put(iMTFSB1+30*fBT); PLL.Put(iMTFSB1+31*fBT);
        y.mode := Based; y.reg := SB; y.offset := RealToIntAddr; y.typ := PLT.lrltyp; Load(x, -1); x.typ := PLT.lrltyp;
        Plus(y, x, -1);
        z.mode := Based; z.reg := SB; z.offset := scratch; z.typ := PLT.lrltyp; Store(z, y);
        x.mode := Based; x.reg := SB;
        PLL.Put(iMTFSF+1*fFLM+t*fFRB); PLL.FreeTempF(t);
        IF dtyp^.form IN {Byte, Bool, Char, SInt} THEN x.offset := scratch+7
        ELSIF dtyp^.form = Int THEN x.offset := scratch+6
        ELSE x.offset := scratch+4
        END;
        x.typ := dtyp; Load(x, rt)
      ELSE (* conversion between Real and LReal *)
        Load(x, rt);
        IF round & (sform = LReal) THEN ASSERT(dform = Real);
          PLL.FreeTempF(x.reg); rt := CheckF(rt); PLL.Put(iFRSP+rt*fFRT+x.reg*fFRB); x.reg := rt; x.typ := PLT.realtyp
        END
      END
    END;
    x.typ := dtyp
  END Convert;

  PROCEDURE Field* (VAR x: PLL.Item; offset, rt: LONGINT);
  BEGIN
    IF offset = 0 THEN BaseOrInx(x, rt)
    ELSE Base(x, rt); INC(x.offset, offset);
    END;
    ASSERT(x.mode IN {Based, Indexed});
  END Field;

  PROCEDURE^ Times* (VAR x, y: PLL.Item; rt: LONGINT);
  PROCEDURE^ Ash* (VAR x, y: PLL.Item; rt: LONGINT);

  PROCEDURE TypeSize* (VAR x: PLL.Item; typ: PLT.Struct; rt: LONGINT);
    VAR y: PLL.Item; dmode: SHORTINT; dreg, doff, s: LONGINT;
  BEGIN
    IF typ^.comp # DynArr THEN
      x.mode := Con; x.typ := PLT.linttyp; x.offset := typ^.size
    ELSE
      dmode := x.dmode; dreg := x.dreg; doff := x.adr; x.mode := dmode; x.typ := PLT.linttyp;
      IF dmode = Reg THEN x.reg := dreg+typ^.offset DIV 4 ELSE x.reg := dreg; x.offset := doff+typ^.offset END;
      typ := typ^.BaseTyp; x.dreg := -1;
      WHILE typ^.comp = DynArr DO
        y.mode := dmode; y.typ := PLT.linttyp; y.dreg := -1;
        IF dmode = Reg THEN y.reg := dreg+typ^.offset DIV 4 ELSE y.reg := dreg; y.offset := doff+typ^.offset END;
        s := rt; typ := typ^.BaseTyp;
        IF (typ^.comp = DynArr) OR (typ^.size > 1) THEN s := -1 END;
        Times(x, y, s)
      END;
      s := typ^.size;
      IF s > 1 THEN
        y.mode := Con; y.dreg := -1;
        IF SYSTEM.VAL(SET, s)*SYSTEM.VAL(SET, s-1) = {} THEN
          y.offset := 31-CNTLZ(s); Ash(x, y, rt)
        ELSE
          y.offset := s; Times(x, y, rt)
        END
      END;
      x.dreg := SHORT(SHORT(dreg))
    END
  END TypeSize;

  PROCEDURE MulOrShift (VAR x, y: PLL.Item; rt: LONGINT);
    VAR n: LONGINT; z: PLL.Item;
  BEGIN
    ASSERT(y.mode = Con);
    n := y.offset;
    IF x.mode = Con THEN x.offset := x.offset * n
    ELSIF n > 1 THEN
      IF SYSTEM.VAL(SET, n)*SYSTEM.VAL(SET, n-1) = {} THEN z := y; z.offset := 31-CNTLZ(n); Ash(x, z, rt)
      ELSE Times(x, y, rt)
      END
    END
  END MulOrShift;

  PROCEDURE MulDim* (VAR nofel, len: PLL.Item; rt: LONGINT);
    VAR y: PLL.Item;
  BEGIN
    IF nofel.mode = Con THEN
      IF len.mode = Con THEN nofel.offset := nofel.offset*len.offset
      ELSE y := len; MulOrShift(y, nofel, rt); nofel := y
      END
    ELSE
      IF len.mode = Con THEN MulOrShift(nofel, len, rt)
      ELSE Times(nofel, len, rt)
      END
    END
  END MulDim;

  PROCEDURE GenDimTrap* (VAR len: PLL.Item);
  BEGIN
    IF inxchk THEN Load(len, -1); PLL.SetTrap(DimTrap); PLL.Put(iTI+tSLE*fTO+len.reg*fRA) END
  END GenDimTrap;

  PROCEDURE Index* (VAR x, y: PLL.Item; rt: LONGINT);
    VAR t, n, elemSize, inx: LONGINT; mode: SHORTINT; basedRes: BOOLEAN; v, z: PLL.Item;
  BEGIN
    z.dreg := -1;
    IF x.typ^.comp = Array THEN
      BaseOrInx(x, -1); elemSize := x.typ^.BaseTyp^.size;
      IF y.mode = Con THEN Field(x, y.offset*elemSize, rt)
      ELSE
        IF x.mode = Indexed THEN ReduceIndex(x, x.offset, -1); x.offset := 0; x.mode := Based END;
        basedRes := x.offset # 0; Load(y, -1); MakeReg(y, -1); t := rt; IF basedRes THEN t := -1 END;
        IF inxchk THEN
          n := x.typ^.n; inx := y.reg;
          IF n < 7FFFH THEN PLL.SetTrap(IndexCheck); PLL.Put(iTI+tUGE*fTO+inx*fRA+n)
          ELSE
            z.mode := Con; z.typ := PLT.linttyp; z.offset := n; Load(z, -1); t := z.reg; PLL.FreeTempR(t);
            PLL.SetTrap(IndexCheck); PLL.Put(iT+tUGE*fTO+inx*fRA+t*fRB)
          END
        END;
        z.mode := Con; z.typ := PLT.linttyp; z.offset := elemSize; MulOrShift(y, z, t);
        IF basedRes THEN ReduceIndex(x, y.reg, rt) ELSE x.mode := Indexed; x.offset := y.reg END
      END
    ELSE (* DynArr *)
      IF (y.mode = Con) & (y.offset = 0) THEN Field(x, 0, rt)
      ELSE
        IF x.mode = Indexed THEN ReduceIndex(x, x.offset, -1); x.mode := Based; x.offset := 0 END;
        basedRes := x.offset # 0;
        IF inxchk THEN
          v := y; IF (v.mode # Con) OR (v.offset >= 7FFFH) THEN Load(v, -1); MakeReg(v, -1) END;
          mode := x.dmode; z.mode := mode; z.typ := PLT.linttyp;
          IF mode = Reg THEN z.reg := x.dreg+x.typ^.offset DIV 4
          ELSE z.reg := x.dreg; z.offset := x.adr+x.typ^.offset; Load(z, -1)
          END;
          IF v.mode = Con THEN PLL.SetTrap(IndexCheck); PLL.Put(iTI+tULE*fTO+z.reg*fRA+v.offset)
          ELSE PLL.SetTrap(IndexCheck); PLL.Put(iT+tUGE*fTO+v.reg*fRA+z.reg*fRB)
          END;
          PLL.FreeTempR(z.reg);
          IF (y.mode # Reg) & (v.mode = Reg) THEN
            IF (y.mode = Con) & (SYSTEM.VAL(SET, y.offset)*SYSTEM.VAL(SET, y.offset-1) = {}) THEN
              PLL.FreeTempR(v.reg)
            ELSE y.mode := Reg; y.reg := v.reg
            END
          END
        END;
        v := x; TypeSize(v, v.typ^.BaseTyp, -1); ASSERT(x.mode = Based);
        v.dreg := -1;
        IF v.mode = Con THEN
          IF y.mode = Con THEN y.offset := y.offset*v.offset ELSE MulOrShift(y, v, -1) END
        ELSE
          IF y.mode = Con THEN MulOrShift(v, y, -1); y := v ELSE Times(y, v, -1) END
        END;
        IF ~(y.mode IN {Con, Reg}) THEN Load(y, -1); MakeReg(y, -1) END;
        IF basedRes THEN
          IF y.mode = Con THEN INC(x.offset, y.offset) ELSE ReduceIndex(x, y.reg, rt) END
        ELSE
          IF y.mode = Con THEN x.offset := y.offset ELSE x.mode := Indexed; x.offset := y.reg END
        END
      END
    END
  END Index;

  PROCEDURE Deref* (VAR x: PLL.Item; rt: LONGINT);
    VAR btyp: PLT.Struct;
  BEGIN
    ASSERT(x.typ.form = Pointer);
    Load(x, rt);
    x.mode := Based; x.offset := 0;
    btyp := x.typ.BaseTyp;
    IF btyp.comp = Array THEN
      REPEAT btyp := btyp.BaseTyp UNTIL btyp.comp # Array;
      IF (btyp.comp = Record) OR (btyp.form = Pointer) THEN x.offset := 16 END
    END;
    IF nilchk THEN PLL.SetTrap(NilTrap); PLL.Put(iTI+tEQ*fTO+x.reg*fRA) END
  END Deref;

  PROCEDURE DynArrItem* (VAR x: PLL.Item; rt: LONGINT);
    VAR dreg, doff, nofdim: LONGINT; typ: PLT.Struct; wasVar: BOOLEAN;
  BEGIN
    IF x.dmode IN {Reg, Var, VarPar, Par} THEN  (* normal dynamic arrays *) (* << mmb 15.11.91, temp fix for DynArr *)
      IF x.mode = Reg THEN
        x.dreg := SHORT(SHORT(x.reg)); x.mode := Based; x.offset := 0
      ELSE
        Base(x, -1); dreg := x.dreg;
        IF dreg = rt THEN
          dreg := PLL.GetTempR(); MoveReg(dreg, rt)
        END;
        x.dreg := SHORT(SHORT(dreg));
      END
    ELSE
      wasVar := x.mode IN {Var, VarPar, Par};
      IF x.mode = VarPar THEN x.mode := Var END;
      IF x.mode = Par THEN x.mode:=Var END;
      Base(x, -1); dreg := x.reg;
      IF wasVar THEN
        doff := x.offset; x.typ := PLT.linttyp; Load(x, rt); x.mode := Based; x.offset := 0
      ELSE
        doff := 8;
        nofdim := 0; typ := x.typ; REPEAT INC(nofdim); typ := typ^.BaseTyp UNTIL typ^.comp # DynArr;
        ASSERT(x.offset = 0);
        x.offset := (nofdim DIV 2)*8+16
      END;
      x.dmode := Based; x.dreg := SHORT(SHORT(dreg)); PLL.HoldTempR(dreg); x.adr := doff
    END
  END DynArrItem;

  PROCEDURE^ Compare* (VAR x, y: PLL.Item; subcl: INTEGER);

  PROCEDURE TypTest* (VAR x: PLL.Item; typ: PLT.Struct; guard, equal, varrec: BOOLEAN);
    CONST TdopEql=1EH;
    VAR y, z: PLL.Item; h1, h2: LONGINT;
  BEGIN
    ASSERT(x.typ^.form = typ^.form);
    IF ~guard OR typchk THEN
      IF guard THEN
        h1 := -1; h2 := -1; z := x;
        IF z.mode IN {Reg, RegSI, Based, Indexed} THEN h1 := z.reg; PLL.HoldTempR(h1) END;
        IF z.mode = Indexed THEN h2 := z.offset; PLL.HoldTempR(h2) END
      END;
      IF ~varrec THEN
        IF typ^.form = Pointer THEN Load(x, -1); x.mode := Based; x.offset := -4
        ELSE Base(x, -1); DEC(x.offset, 4)
        END;
        x.typ := PLT.linttyp; Load(x, -1);
        IF typ^.form = Pointer THEN typ := typ^.BaseTyp END
      ELSE (* VarPar *)
        IF x.mode = Based THEN
          INC(x.reg); x.mode := Reg; x.typ := PLT.linttyp
         ELSE
          x.reg := FindFP(PLL.level, x.mnolev, -1); x.mode := Based; x.typ := PLT.linttyp; INC(x.offset, 4); Load(x, -1)
        END
      END;
      y.mode := Var;  y.mnolev := -PLT.GetTypMno(typ); y.offset := typ^.tdadr; y.dreg := -1; y.typ := PLT.linttyp; Load(y, -1);
      IF ~equal THEN x.mode := Based; x.offset := -8-typ^.extlev*4; Load(x, -1) END;
      IF guard THEN
        PLL.SetTrap(TypeGuard); PLL.FreeTempR(x.reg); PLL.FreeTempR(y.reg);
        PLL.Put(iT+tNEQ*fTO+x.reg*fRA+y.reg*fRB); x := z;
        IF h1 >= 0 THEN PLL.UnholdTempR(h1) END;
        IF h2 >= 0 THEN PLL.UnholdTempR(h2) END
      ELSE
        Compare(x, y, TdopEql)
      END
    END
  END TypTest;

  PROCEDURE RealUnary (op: LONGINT; VAR x: PLL.Item; rt: LONGINT);
    VAR s: LONGINT;
  BEGIN
    Load(x, -1); s := x.reg; PLL.FreeTempF(s); rt := CheckF(rt); PLL.Put(op+rt*fFRT+s*fFRB); x.reg := rt
  END RealUnary;

  PROCEDURE FAddOp (op: LONGINT; VAR x, y: PLL.Item; rt: LONGINT);
    VAR s1, s2: LONGINT;
  BEGIN
    Load(x, -1); Load(y, -1); s1 := x.reg; s2 := y.reg; PLL.FreeTempF(s1); PLL.FreeTempF(s2); rt := CheckF(rt);
    PLL.Put(op+rt*fFRT+s1*fFRA+s2*fFRB); x.reg := rt
  END FAddOp;

  PROCEDURE FMulOp (op: LONGINT; VAR x, y: PLL.Item; rt: LONGINT);
    VAR s1, s2: LONGINT;
  BEGIN
    Load(x, -1); Load(y, -1); s1 := x.reg; s2 := y.reg; PLL.FreeTempF(s1); PLL.FreeTempF(s2); rt := CheckF(rt);
    PLL.Put(op+rt*fFRT+s1*fFRA+s2*fFRC); x.reg := rt
  END FMulOp;

  PROCEDURE FMulAddOp (op: LONGINT; VAR x, y, z: PLL.Item; rt: LONGINT);
    VAR s1, s2, s3: LONGINT;
  BEGIN
    Load(x, -1); Load(y, -1); Load(z, -1); s1 := x.reg; s2 := y.reg; s3 := z.reg;
    PLL.FreeTempF(s1); PLL.FreeTempF(s2); PLL.FreeTempF(s3); rt := CheckF(rt);
    PLL.Put(op+rt*fFRT+s1*fFRA+s2*fFRC+s3*fFRB); x.reg := rt
  END FMulAddOp;

  PROCEDURE IntUnary (op: LONGINT; VAR x: PLL.Item; rt: LONGINT);
    VAR s: LONGINT;
  BEGIN
    Load(x, -1); MakeReg(x, -1); s := x.reg; PLL.FreeTempR(s); rt := CheckR(rt); PLL.Put(op+rt*fRT+s*fRA); x.reg := rt
  END IntUnary;

  PROCEDURE IntBinary (op: LONGINT; VAR x, y: PLL.Item; rt: LONGINT);
    VAR s1, s2: LONGINT;
  BEGIN
    Load(x, -1); MakeReg(x, -1); Load(y, -1); MakeReg(y, -1); s1 := x.reg; s2 := y.reg;
    PLL.FreeTempR(s1); PLL.FreeTempR(s2); rt := CheckR(rt); PLL.Put(op+rt*fRT+s1*fRA+s2*fRB); x.reg := rt
  END IntBinary;

  PROCEDURE IntAddImm (VAR x, y: PLL.Item; rt: LONGINT);
    VAR s, t, l, u: LONGINT;
  BEGIN
    ASSERT(y.mode = Con);
    Load(x, -1); MakeReg(x, -1); s := x.reg; PLL.FreeTempR(s);
    u := y.offset; l := u MOD LowWord; u := (SYSTEM.LSH(u, -16)+SYSTEM.LSH(l, -15)) MOD LowWord;
    IF u = 0 THEN rt := CheckR(rt); PLL.Put(iAI+rt*fRT+s*fRA+l)
    ELSIF l = 0 THEN rt := CheckR(rt); PLL.Put(iCAU+rt*fRT+s*fRA+u)
    ELSE t := PLL.GetTempR(); PLL.FreeTempR(t); PLL.Put(iCAU+t*fRT+s*fRA+u);
      rt := CheckR(rt); PLL.Put(iCAL+rt*fRT+t*fRA+l)
    END;
    x.reg := rt
  END IntAddImm;

  PROCEDURE IntSubImm (VAR x, y: PLL.Item; rt: LONGINT);  (* x := x-y *)
    VAR s, u, l: LONGINT;
  BEGIN
    ASSERT(x.mode = Con);
    u := x.offset; l := u MOD LowWord; u := (SYSTEM.LSH(u, -16)+SYSTEM.LSH(l, -15)) MOD LowWord;
    IF u # 0 THEN IntBinary(iSF, y, x, rt); x.mode := y.mode; x.reg := y.reg; x.offset := y.offset
    ELSE Load(y, -1); MakeReg(y, -1); s := y.reg; PLL.FreeTempR(s); rt := CheckR(rt);
      PLL.Put(iSFI+rt*fRT+s*fRA+l); x.mode := Reg; x.reg := rt
    END
  END IntSubImm;

  PROCEDURE IntMulImm (VAR x, y: PLL.Item; rt: LONGINT);
    VAR s, u, l: LONGINT;
  BEGIN
    ASSERT(y.mode = Con);
    u := y.offset; l := u MOD LowWord; u := (SYSTEM.LSH(u, -16)+SYSTEM.LSH(l, -15)) MOD LowWord;
    IF u # 0 THEN IntBinary(iMULS, x, y, rt)
    ELSE Load(x, -1); MakeReg(x, -1); s := x.reg; PLL.FreeTempR(s); rt := CheckR(rt);
      PLL.Put(iMULI+rt*fRT+s*fRA+l); x.reg := rt
    END
  END IntMulImm;

  PROCEDURE IntCmp (VAR x, y: PLL.Item): LONGINT;
    VAR s1, s2, f: LONGINT;
  BEGIN
    Load(x, -1); MakeReg(x, -1); Load(y, -1); MakeReg(y, -1); s1 := x.reg; s2 := y.reg;
    PLL.FreeTempR(s1); PLL.FreeTempR(s2); f := PLL.GetTempCRF(); PLL.Put(iCMP+f*fBF+s1*fRA+s2*fRB);
    RETURN f
  END IntCmp;

  PROCEDURE IntCmpImm (VAR x, y: PLL.Item): LONGINT;
    VAR s1, s2, f: LONGINT;
  BEGIN
    ASSERT(y.mode = Con);
    s2 := y.offset;
    IF (-32767 < s2) & (s2 < 32768) THEN
      Load(x, -1); MakeReg(x, -1); s1 := x.reg; PLL.FreeTempR(s1); f := PLL.GetTempCRF();
      PLL.Put(iCMPI+f*fBF+s1*fRA+(s2 MOD LowWord)); RETURN f
    ELSE RETURN IntCmp(x, y)
    END
  END IntCmpImm;

  PROCEDURE SetBinary (op: LONGINT; VAR x, y: PLL.Item; rt: LONGINT);
    VAR s1, s2: LONGINT;
  BEGIN
    Load(x, -1); Load(y, -1); s1 := x.reg; s2 := y.reg; x.mode := Reg;
    PLL.FreeTempR(s1); PLL.FreeTempR(s2); rt := CheckR(rt); PLL.Put(op+rt*fRA+s1*fRS+s2*fRB); x.reg := rt
  END SetBinary;

  PROCEDURE SetInterImm (VAR x, y: PLL.Item; rt: LONGINT);
    VAR u, l, s, f: LONGINT;
  BEGIN
    u := y.offset; l := u MOD LowWord; u := SYSTEM.LSH(u, -16); Load(x, -1); s := x.reg; f := PLL.GetCRF0();
    IF (u = 0) & (f = 0) THEN PLL.FreeTempR(s); rt := CheckR(rt); PLL.Put(iANDIL+rt*fRA+s*fRS+l); x.reg := rt
    ELSIF (l = 0) & (f = 0) THEN PLL.FreeTempR(s); rt := CheckR(rt); PLL.Put(iANDIU+rt*fRA+s*fRS+u); x.reg := rt
    ELSE SetBinary(iAND, x, y, rt)
    END;
    f := f*4; PLL.FreeTempCRBs({f..f+3})
    (* here, an additional optimization can be made that uses the RLINM instruction for contiguous masks *)
  END SetInterImm;

  PROCEDURE SetSymImm (iop: LONGINT; VAR x, y: PLL.Item; rt: LONGINT);
    VAR u, l, s, t: LONGINT;
  BEGIN
    ASSERT(y.mode = Con);
    u := y.offset; l := u MOD LowWord; u := SYSTEM.LSH(u, -16);
    Load(x, -1); MakeReg(x, -1); s := x.reg; PLL.FreeTempR(s);
    IF u = 0 THEN rt := CheckR(rt); PLL.Put(iop+rt*fRA+s*fRS+l)
    ELSE
      IF l # 0 THEN t := PLL.GetTempR(); PLL.FreeTempR(t); PLL.Put(iop+t*fRA+s*fRS+l); s := t END;
      rt := CheckR(rt); PLL.Put(iop+iUPPER+rt*fRA+s*fRS+u)
    END;
    x.reg := rt
  END SetSymImm;

  PROCEDURE SetRange* (VAR x, y: PLL.Item; rt: LONGINT);
    VAR s1, s2, s3, s4, one: LONGINT;
  BEGIN
    Load(x, -1); Load(y, -1); s1 := x.reg; s2 := y.reg;
    rt := CheckR(rt); one := PLL.GetTempR(); s3 := PLL.GetTempR(); s4 := PLL.GetTempR();
    PLL.Put(iADDI+one*fRT+0FFFFH);  (* fixmask *)
    PLL.Put(iADDI+s4*fRT+s2*fRA+1);
    PLL.Put(iSR+s3*fRA+one*fRS+s1*fRB);
    PLL.Put(iSR+s4*fRA+one*fRS+s4*fRB);
    PLL.Put(iANDC+rt*fRA+s3*fRS+s4*fRB);
    PLL.FreeTempR(one);
    PLL.FreeTempR(s1); PLL.FreeTempR(s2); PLL.FreeTempR(s3); PLL.FreeTempR(s4);
    (* PLL.Put(iMASKG+rt*fRA+s1*fRS+s2*fRB); *)
    x.reg := rt
  END SetRange;

  PROCEDURE SetElem* (VAR x: PLL.Item; rt: LONGINT);
    VAR s: LONGINT;
  BEGIN
    Load(x, -1); s := x.reg; PLL.FreeTempR(s); rt := CheckR(rt);
    PLL.Put(iCAU+rt*fRT+08000H);  (* fixmask *)
    PLL.Put(iSR+rt*fRA+rt*fRS+s*fRB);
    (* PLL.Put(iMASKG+rt*fRA+s*fRS+s*fRB); *)
    x.reg := rt
  END SetElem;

  PROCEDURE Not* (VAR x: PLL.Item; rt: LONGINT);
    VAR s: LONGINT; l: PLL.Label;
  BEGIN
    l := x.Tjmp; x.Tjmp := x.Fjmp; x.Fjmp := l;
    IF x.mode = Cond THEN x.reg := -1-x.reg
    ELSE Load(x, -1); s := x.reg; PLL.FreeTempR(s); rt := CheckR(rt); PLL.Put(iSFI+rt*fRT+s*fRA+1); x.reg := rt
    END
  END Not;

  PROCEDURE Neg* (VAR x: PLL.Item; rt: LONGINT);
  BEGIN
    CASE x.typ^.form OF
      SInt, Int, LInt: IntUnary(iNEG, x, rt)
    |  Real, LReal: RealUnary(iFNEG, x, rt)
    |  Set:
        IF x.mode = RegSI THEN x.mode := Reg END;
        IntUnary(iNOT, x, rt)
    END
  END Neg;

  PROCEDURE Abs* (VAR x: PLL.Item; rt: LONGINT);
    VAR s, t0, t1: LONGINT;
  BEGIN
    CASE x.typ^.form OF
      SInt, Int, LInt:
        IF powerpc THEN
          Load(x, -1); MakeReg(x, -1);
          s := x.reg; t0 := PLL.GetTempR();
          PLL.Put(iSRAI+t0*fRA+s*fRS+31*fSH);
          PLL.FreeTempR(s); t1 := PLL.GetTempR();
          PLL.Put(iXOR+t1*fRA+t0*fRS+s*fRB);
          PLL.FreeTempR(t0); PLL.FreeTempR(t1);
          rt := CheckR(rt);
          PLL.Put(iSF+rt*fRT+t0*fRA+t1*fRB);
          x.reg := rt
        ELSE
          IntUnary(iABS, x, rt)
        END
    |  Real, LReal: RealUnary(iFABS, x, rt)
    END
  END Abs;

  PROCEDURE Cap* (VAR x: PLL.Item; rt: LONGINT);
  BEGIN SetInterImm(x, CAPmask, rt)
  END Cap;

  PROCEDURE VarShift (rop: LONGINT; VAR x, y: PLL.Item; rt: LONGINT): LONGINT;
    CONST TdopLss=20H;
    VAR s1, s2, t: LONGINT; l: PLL.Label;
  BEGIN
    ASSERT(x.mode = Reg);
    s1 := x.reg; Load(y, -1); MakeReg(y, -1); s2 := y.reg; y.Fjmp := 0;
    Compare(y, zero, TdopLss); PLL.FreeTempR(s1); PLL.FreeTempR(s2); PutCondBranch(y, FALSE);
    t := PLL.GetTempR(); PLL.FreeTempR(t); rt := CheckR(rt);
    PLL.Put(iNEG+t*fRT+s2*fRA); (* absfix *)
    (* PLL.Put(iABS+t*fRT+s2*fRA); *)
    PLL.Put(rop+rt*fRA+s1*fRS+t*fRB); l := 0; PutBranch(l); SetLabel(y.Fjmp);
    PLL.Put(iSL+rt*fRA+s1*fRS+s2*fRB); SetLabel(l);
    RETURN rt
  END VarShift;

  PROCEDURE Ash* (VAR x, y: PLL.Item; rt: LONGINT);
    VAR sh, s, t: LONGINT;
  BEGIN
    Load(x, -1);
    IF y.mode = Con THEN
      sh := y.offset; s := x.reg; PLL.FreeTempR(s);
      IF x.mode = RegSI THEN
        IF sh >= 24 THEN
          sh := sh MOD 32; rt := CheckR(rt); PLL.Put(iRLINM+rt*fRA+s*fRS+sh*fSH+(31-sh)*fME)
        ELSE
          sh := IMIN(24-sh, 31); t := PLL.GetTempR(); PLL.FreeTempR(t);
          PLL.Put(iRLINM+t*fRA+s*fRS+24*fSH+8*fME); rt := CheckR(rt); PLL.Put(iSRAI+rt*fRA+t*fRS+sh*fSH)
        END;
        x.mode := Reg
      ELSE rt := CheckR(rt);
        IF sh < 0 THEN PLL.Put(iSRAI+rt*fRA+s*fRS+((-sh) MOD 32)*fSH)
        ELSE sh := sh MOD 32; PLL.Put(iRLINM+rt*fRA+s*fRS+sh*fSH+(31-sh)*fME)
        END
      END
    ELSE rt := VarShift(iSRA, x, y, rt)
    END;
    x.reg := rt
  END Ash;

  PROCEDURE Times* (VAR x, y: PLL.Item; rt: LONGINT);
  BEGIN
    CASE x.typ^.form OF
      SInt, Int, LInt:
        IF x.mode = Con THEN IntMulImm(y, x, rt); x.mode := y.mode; x.reg := y.reg; x.offset := y.offset
        ELSIF y.mode = Con THEN IntMulImm(x, y, rt)
        ELSE IntBinary(iMULS, x, y, rt)
        END
    |  Real:
        IF powerpc THEN FMulOp(iFMULS, x, y, rt) ELSE FMulOp(iFM, x, y, rt) END
    |  LReal: FMulOp(iFM, x, y, rt)
    |  Set:
        IF x.mode = Con THEN SetInterImm(y, x, rt); x.mode := y.mode; x.reg := y.reg; x.offset := y.offset
        ELSIF y.mode = Con THEN SetInterImm(x, y, rt)
        ELSE SetBinary(iAND, x, y, rt)
        END
    END;
  END Times;

  PROCEDURE Div* (VAR x, y: PLL.Item; rt: LONGINT);
    VAR s1, s2, s3, t: LONGINT; z: PLL.Item; xoptb, xoptc, yopt: BOOLEAN;
  BEGIN
    (* 601
    ASSERT(x.typ^.form IN {SInt, Int, LInt});
    xoptb := x.mode = Con; yopt := y.mode = Con; xoptc := FALSE;
    IF xoptb THEN xoptc := x.offset >= 0 END;
    IF yopt & (y.offset <= 0) THEN PLL.err(301) END;
    Load(x, -1); MakeReg(x, -1); Load(y, -1); MakeReg(y, -1); s1 := x.reg; s2 := y.reg;
    PLL.FreeTempR(s1); PLL.FreeTempR(s2); rt := CheckR(rt);
    IF ~yopt THEN PLL.SetTrap(DivideTrap); PLL.Put(iTI+tSLE*fTO+s2*fRA) END;
    PLL.Put(iDIVS+rt*fRT+s1*fRA+s2*fRB+fREC);
    IF ~xoptb THEN z.mode := Cond; z.reg := -1-bLT; z.Tjmp := 0; PutCondBranch(z, TRUE) END;
    IF ~xoptc THEN PLL.Put(iAI+rt*fRT+rt*fRA+((-1) MOD LowWord)) END;
    IF ~xoptb THEN SetLabel(z.Tjmp) END;
    x.reg := rt
    *)

    (* 604 *)
    ASSERT(x.typ^.form IN {SInt, Int, LInt});
    xoptb := x.mode = Con; yopt := y.mode = Con; xoptc := FALSE;
    IF xoptb THEN xoptc := x.offset >= 0 END;
    IF yopt & (y.offset <= 0) THEN PLL.err(301) END;
    Load(x, -1); MakeReg(x, -1); Load(y, -1); MakeReg(y, -1); s1 := x.reg; s2 := y.reg;
    IF (rt = s2) THEN t := PLL.GetTempR(); MoveReg(t, s2); s2 := t END;
    IF (rt = s1) THEN t := PLL.GetTempR(); MoveReg(t, s1); s1 := t END;
    s3 := PLL.GetTempR(); rt := CheckR(rt); PLL.FreeTempR(s1); PLL.FreeTempR(s2);
    IF ~yopt THEN PLL.SetTrap(DivideTrap); PLL.Put(iTI+tSLE*fTO+s2*fRA) END;
    PLL.Put(iDIVW+rt*fRT+s1*fRA+s2*fRB(*+fREC*));
    PLL.Put(iMULS+s3*fRT+rt*fRA+s2*fRB);
    PLL.Put(iSUB+s3*fRT+s3*fRA+s1*fRB+fREC); PLL.FreeTempR(s3);
    IF ~xoptb THEN z.mode := Cond; z.reg := -1-bLT; z.Tjmp := 0; PutCondBranch(z, TRUE) END;
    IF ~xoptc THEN PLL.Put(iAI+rt*fRT+rt*fRA+((-1) MOD LowWord)) END;
    IF ~xoptb THEN SetLabel(z.Tjmp) END;
    x.reg := rt
  END Div;

  PROCEDURE Slash* (VAR x, y: PLL.Item; rt: LONGINT);
  BEGIN
    CASE x.typ^.form OF
      Real:
        IF powerpc THEN FAddOp(iFDIVS, x, y, rt) ELSE FAddOp(iFD, x, y, rt) END
    |  LReal: FAddOp(iFD, x, y, rt)
    |  Set:
        IF x.mode = Con THEN SetSymImm(iXORIL, y, x, rt); x.mode := y.mode; x.reg := y.reg; x.offset := y.offset
        ELSIF y.mode = Con THEN SetSymImm(iXORIL, x, y, rt)
        ELSE SetBinary(iXOR, x, y, rt)
        END
    END
  END Slash;

  PROCEDURE Mod* (VAR x, y: PLL.Item; rt: LONGINT);
    VAR s1, s2, t, imm: LONGINT; z: PLL.Item; xoptb, xoptc, yopt, ysimm: BOOLEAN;
  BEGIN
    (* 601
    ASSERT(x.typ^.form IN {SInt, Int, LInt});
    xoptb := x.mode = Con; yopt := y.mode = Con; xoptc := FALSE; ysimm := FALSE;
    IF xoptb THEN xoptc := x.offset > 0 END;
    IF yopt THEN imm := y.offset;
      IF imm <= 0 THEN PLL.err(301) ELSE ysimm := imm < 32767 END
    END;
    Load(x, -1); MakeReg(x, -1); Load(y, -1); MakeReg(y, -1); s1 := x.reg; s2 := y.reg; PLL.FreeTempR(s1);
    IF ~yopt THEN PLL.SetTrap(DivideTrap); PLL.Put(iTI+tSLE*fTO+s2*fRA) END;
    PLL.Put(iDIVS+s1*fRA+s2*fRB+fREC); rt := CheckR(rt); PLL.FreeTempR(s2);
    IF ~xoptc & ~ysimm & (rt = s2) THEN
      t := PLL.GetTempR(); MoveReg(t, s2); s2 := t; PLL.FreeTempR(t)
    END;
    PLL.Put(iMFSPR+rt*fRT+spMQ*fSPR);
    IF ~xoptb THEN z.mode := Cond; z.reg := -1-bLT; z.Tjmp := 0; PutCondBranch(z, TRUE) END;
    IF ~xoptc THEN
      IF ysimm THEN PLL.Put(iAI+rt*fRT+rt*fRA+(imm MOD LowWord))
      ELSE PLL.Put(iA+rt*fRT+rt*fRA+s2*fRB)
      END
    END;
    IF ~xoptb THEN SetLabel(z.Tjmp) END;
    x.reg := rt
    *)

    (* 603 *)
    ASSERT(x.typ^.form IN {SInt, Int, LInt});
    xoptb := x.mode = Con; yopt := y.mode = Con; xoptc := FALSE; ysimm := FALSE;
    IF xoptb THEN xoptc := x.offset > 0 END;
    IF yopt THEN imm := y.offset;
      IF imm <= 0 THEN PLL.err(301) ELSE ysimm := imm < 32767 END
    END;
    Load(x, -1); MakeReg(x, -1); Load(y, -1); MakeReg(y, -1); s1 := x.reg; s2 := y.reg;
    IF ~yopt THEN PLL.SetTrap(DivideTrap); PLL.Put(iTI+tSLE*fTO+s2*fRA) END;
    rt := CheckR(rt);
    IF (rt = s2) THEN t := PLL.GetTempR(); MoveReg(t, s2); s2 := t END;
    IF (rt = s1) THEN t := PLL.GetTempR(); MoveReg(t, s1); s1 := t END;
    PLL.Put(iDIVW+rt*fRT+s1*fRA+s2*fRB);
    PLL.Put(iMULS+rt*fRT+rt*fRA+s2*fRB);
    PLL.Put(iSUB+rt*fRT+rt*fRA+s1*fRB+fREC);
    PLL.FreeTempR(s1); PLL.FreeTempR(s2);
    IF ~xoptb THEN z.mode := Cond; z.reg := -1-bLT; z.Tjmp := 0; PutCondBranch(z, TRUE) END;
    IF ~xoptc THEN
      IF ysimm THEN PLL.Put(iAI+rt*fRT+rt*fRA+(imm MOD LowWord))
      ELSE PLL.Put(iA+rt*fRT+rt*fRA+s2*fRB)
      END
    END;
    IF ~xoptb THEN SetLabel(z.Tjmp) END;
    x.reg := rt
  END Mod;

  PROCEDURE Plus* (VAR x, y: PLL.Item; rt: LONGINT);
  BEGIN
    CASE x.typ^.form OF
      SInt, Int, LInt:
        IF x.mode = Con THEN IntAddImm(y, x, rt); x.mode := y.mode; x.reg := y.reg; x.offset := y.offset
        ELSIF y.mode = Con THEN IntAddImm(x, y, rt)
        ELSE IntBinary(iCAX, x, y, rt)
        END
    |  Real:
        IF powerpc THEN FAddOp(iFADDS, x, y, rt) ELSE FAddOp(iFA, x, y, rt) END
    |  LReal: FAddOp(iFA, x, y, rt)
    |  Set:
        IF x.mode = Con THEN SetSymImm(iORIL, y, x, rt); x.mode := y.mode; x.reg := y.reg; x.offset := y.offset
        ELSIF y.mode = Con THEN SetSymImm(iORIL, x, y, rt)
        ELSE SetBinary(iOR, x, y, rt)
        END
    END
  END Plus;

  PROCEDURE Minus* (VAR x, y: PLL.Item; rt: LONGINT);
  BEGIN
    CASE x.typ^.form OF
      SInt, Int, LInt:
        IF x.mode = Con THEN IntSubImm(x, y, rt)
        ELSIF y.mode = Con THEN y.offset := -y.offset; IntAddImm(x, y, rt)
        ELSE IntBinary(iSF, y, x, rt); x.mode := y.mode; x.reg := y.reg; x.offset := y.offset
        END
    |  Real:
        IF powerpc THEN FAddOp(iFSUBS, x, y, rt) ELSE FAddOp(iFS, x, y, rt) END
    |  LReal: FAddOp(iFS, x, y, rt)
    |  Set:
        IF y.mode = Con THEN y.offset := -1-y.offset; SetInterImm(x, y, rt)
        (* if x.mode = Con, an optimization could be to translate to (-y) MASK x, if the number of masks is 1 in x *)
        ELSE SetBinary(iANDC, x, y, rt)
        END
    END
  END Minus;

  PROCEDURE MulAdd* (VAR x, y, z: PLL.Item; rt: LONGINT);
  BEGIN
    IF powerpc & (x.typ^.form = Real) THEN FMulAddOp(iFMADDS, x, y, z, rt)
    ELSE FMulAddOp(iFMA, x, y, z, rt)
    END
  END MulAdd;

  PROCEDURE MulSub* (VAR x, y, z: PLL.Item; rt: LONGINT; invert: BOOLEAN);
  BEGIN
    IF powerpc & (x.typ^.form = Real) THEN
      IF invert THEN FMulAddOp(iFNMSUBS, x, y, z, rt) ELSE FMulAddOp(iFMSUBS, x, y, z, rt) END
    ELSE
      IF invert THEN FMulAddOp(iFNMS, x, y, z, rt) ELSE FMulAddOp(iFMS, x, y, z, rt) END
    END
  END MulSub;

  PROCEDURE In* (VAR x, y: PLL.Item);
    VAR s1, s2, t, crf, ropt: LONGINT;
  BEGIN
    ASSERT((x.typ^.form IN {SInt, Int, LInt}) & (y.typ^.form = Set));
    Load(y, -1); IF y.mode = RegSI THEN y.mode := Reg END;
    s2 := y.reg;
    crf := PLL.GetCRF0();
    IF crf = 0 THEN ropt := fREC ELSE PLL.FreeTempCRBs({crf*4..crf*4+3}); ropt := 0 END;
    IF x.mode = Con THEN
      PLL.FreeTempR(s2); t := PLL.GetTempR();
      PLL.Put(iRLINM+t*fRA+s2*fRS+(x.offset MOD 32)*fSH+ropt)
    ELSE
      Load(x, -1); s1 := x.reg; PLL.FreeTempR(s1); PLL.FreeTempR(s2); t := PLL.GetTempR();
      PLL.Put(iRLNM+t*fRA+s2*fRS+s1*fRB+ropt)
    END;
    IF crf = 0 THEN
      x.mode := Cond; x.reg := -1-bEQ; PLL.FreeTempR(t)
    ELSE
      x.mode := Reg; x.reg := t
    END
  END In;

  PROCEDURE Odd* (VAR x: PLL.Item);
    VAR z: PLL.Item;
  BEGIN Load(x, -1); MakeReg(x, -1);
    z := zero; z.offset := 31; x.typ := PLT.settyp; In(z, x); x.mode := z.mode; x.reg := z.reg; x.offset := z.offset
  END Odd;

  PROCEDURE^ Assign* (VAR x, y: PLL.Item);

  PROCEDURE NewSys* (VAR x, y: PLL.Item; rt: LONGINT);
    VAR saved: PLL.SaveDesc;
  BEGIN
    x.mode := XProc; x.reg := 0; x.typ := PLT.notyp; x.dreg := -1; PLL.SaveRegisters(x, saved, sSize);
    x.mode := Reg; x.reg := 3; x.typ := PLT.linttyp; Assign(x, y);
    x.mode := XProc;
    SYSTEM.GET(SYSTEM.ADR(Kernel.newSys), x.adr);
    PLL.Put(iL+SB*fRT+SB*fRA+(PLL.linkTable MOD LowWord)); PLL.PutXCall(x);
    PLL.Put(iL+SB*fRT+SP*fRA+20);
    x.mode := Reg; x.reg := 3; x.typ := PLT.linttyp; PLL.RestoreRegisters(x, saved, rt)
  END NewSys;

  PROCEDURE NewArr* (VAR x, nofel: PLL.Item; nofdim: LONGINT; typ: PLT.Struct; rt: LONGINT);
    VAR y: PLL.Item; saved: PLL.SaveDesc;
  BEGIN
    PLL.FreePar;
    IF (typ^.form # Pointer) & (typ^.tdadr > -3) THEN (* simple type *)
      y.mode := Con; y.offset := typ^.size; y.typ := PLT.linttyp; y.dreg := -1; PLL.LockParR(3); MulOrShift(nofel, y, 3);
      IF nofel.mode = Con THEN INC(nofel.offset, (nofdim DIV 2)*8+16)
      ELSE y.mode := Con; y.typ := PLT.linttyp; y.offset := (nofdim DIV 2)*8+16;
        Load(nofel, -1); IntAddImm(nofel, y, 3)
      END;
      PLL.FreePar;
      NewSys(x, nofel, rt)
    ELSE
      x.mode := XProc; x.reg := 0; x.typ := PLT.notyp; x.dreg := -1;
      PLL.SaveRegisters(x, saved, sSize);
      x.mode := Reg; x.typ := PLT.linttyp;
      x.reg := 4; PLL.LockParR(4); Assign(x, nofel);
      x.reg := 5; PLL.LockParR(5); y.mode := Con; y.offset := nofdim; y.typ := PLT.linttyp; Assign(x, y);
      x.reg := 3; PLL.LockParR(3);
      IF typ^.form = Pointer THEN y.mode := Con; y.offset := 0; y.typ := PLT.linttyp
      ELSE y.mode := Var;  y.mnolev := 0; (* -PLT.GetTypMno(typ); *) y.offset := typ^.tdadr; y.typ := PLT.linttyp
      END;
      Assign(x, y); PLL.FreePar;
      x.mode := XProc;
      SYSTEM.GET(SYSTEM.ADR(Kernel.newArr), x.adr);
      PLL.Put(iL+SB*fRT+SB*fRA+(PLL.linkTable MOD LowWord)); PLL.PutXCall(x);
      PLL.Put(iL+SB*fRT+SP*fRA+20);
      x.mode := Reg; x.reg := 3; x.typ := PLT.linttyp; PLL.RestoreRegisters(x, saved, rt)
    END
  END NewArr;

  PROCEDURE NewRec* (VAR x: PLL.Item; typ: PLT.Struct; rt: LONGINT);
    VAR y: PLL.Item; saved: PLL.SaveDesc; len: LONGINT; btyp: PLT.Struct;
  BEGIN
    IF typ^.tdadr > -3 THEN (* no type descriptor allocated *)
      IF typ^.comp = Array THEN len := typ^.n; btyp := typ^.BaseTyp;
        WHILE btyp^.comp = Array DO len := len*btyp^.n; btyp := btyp^.BaseTyp END;
        y.mode := Con; y.typ := PLT.linttyp;
        IF (btyp^.comp = Record) OR (btyp^.form = Pointer) THEN y.offset := len; NewArr(x, y, 1, btyp, rt)
        ELSE y.offset := typ^.size; NewSys(x, y, rt)
        END
      ELSE
        y.mode := Con; y.offset := typ^.size; y.typ := PLT.linttyp; NewSys(x, y, rt)
      END
    ELSE
      x.mode := XProc; x.reg := 0; x.typ := PLT.notyp; x.dreg := -1; PLL.SaveRegisters(x, saved, sSize);
      y.mode := Var;  y.mnolev := -PLT.GetTypMno(typ); y.offset := typ^.tdadr; y.typ := PLT.linttyp;
      x.mode := Reg; x.reg := 3; x.typ := PLT.linttyp; Assign(x, y);
      x.mode := XProc;
      SYSTEM.GET(SYSTEM.ADR(Kernel.newRec), x.adr);
      PLL.Put(iL+SB*fRT+SB*fRA+(PLL.linkTable MOD LowWord)); PLL.PutXCall(x);
      PLL.Put(iL+SB*fRT+SP*fRA+20);
      x.mode := Reg; x.reg := 3; x.typ := PLT.linttyp; PLL.RestoreRegisters(x, saved, rt)
    END
  END NewRec;

  PROCEDURE SetDim* (VAR y, len: PLL.Item; typ: PLT.Struct);
    VAR z: PLL.Item;
  BEGIN
    z := y; INC(z.offset, typ^.offset); PLL.UnholdTempR(len.reg); Assign(z, len)
  END SetDim;

  PROCEDURE ArrayLen (VAR x: PLL.Item; rt: LONGINT);
    VAR typ: PLT.Struct;
  BEGIN
    typ := x.typ;
    IF typ^.comp = Array THEN
      x.mode := Con; x.offset := typ^.n
    ELSE ASSERT(typ^.comp = DynArr);
      IF x.dmode = Reg THEN x.mode := Reg; x.reg := x.dreg + typ^.offset DIV 4
      ELSE ASSERT(x.dmode = Based);
        x.mode := Based; x.reg := x.dreg; x.offset := x.adr + typ^.offset
      END
    END;
    x.typ := PLT.linttyp
  END ArrayLen;

  PROCEDURE PPCcopy (VAR x, y: PLL.Item); (* copy y to x, PowerPC sequence *)
    VAR z: PLL.Item; t0, t1, src, dest, cond, h: LONGINT; loop, end0, end1, end: PLL.Label;
  BEGIN
    Base(x, -1); ShortBase(x, -1);
    Base(y, -1); ShortBase(y, -1); PLL.UnholdTempR(y.dreg);
    z := x; ArrayLen(z, -1);
    t0 := PLL.GetTempR(); t1 := PLL.GetTempR(); cond := PLL.GetTempCRF();
    Load(z, -1); PLL.FreeTempR(z.reg); PLL.Put(iMTSPR+z.reg*fRS+spCTR*fSPR);
    dest := x.reg; src := y.reg;
    IF ~(dest IN PLL.TempRegs) THEN
      h := PLL.GetTempR(); PLL.Put(iCAL+h*fRT+dest*fRA+(x.offset MOD LowWord)); x.offset := 0; dest := h
    END;
    IF ~(src IN PLL.TempRegs) THEN
      h := PLL.GetTempR(); PLL.Put(iCAL+h*fRT+src*fRA+(y.offset MOD LowWord)); y.offset := 0; src := h
    END;
    end0 := 0; end1 := 0; end := 0; loop := 0;
    IF y.offset # 0 THEN PLL.Put(iLBZU+t0*fRT+src*fRA+(y.offset MOD LowWord)) ELSE PLL.Put(iLBZ+t0*fRT+src*fRA) END;
    PLL.Put(iCAL);
    PutBranchInstr(iBDZ, end0);
    PLL.Put(iCMPI+cond*fBF+t0*fRA+0);
    PutBranchInstr(iBT+(cond*4+bEQ)*fBI, end0);
    PLL.Put(iLBZU+t1*fRT+src*fRA+1);
    IF x.offset # 0 THEN PLL.Put(iSTBU+t0*fRS+dest*fRA+(x.offset MOD LowWord)) ELSE PLL.Put(iSTB+t0*fRS+dest*fRA) END;
    PutBranchInstr(iBDZ, end1);
    PLL.Put(iCMPI+cond*fBF+t1*fRA+0);
    PutBranchInstr(iBT+(cond*4+bEQ)*fBI, end1);
    SetLabel(loop);
    PLL.Put(iLBZU+t0*fRT+src*fRA+1);
    PLL.Put(iSTBU+t1*fRS+dest*fRA+1);
    PutBranchInstr(iBDZ, end1);
    PLL.Put(iCMPI+cond*fBF+t0*fRA+0);
    PutBranchInstr(iBT+(cond*4+bEQ)*fBI, end1);
    PLL.Put(iLBZU+t1*fRT+src*fRA+1);
    PLL.Put(iSTBU+t0*fRS+dest*fRA+1);
    PutBranchInstr(iBDZ, end1);
    PLL.Put(iCMPI+cond*fBF+t1*fRA+0);
    PutBranchInstr(iBF+(cond*4+bEQ)*fBI, loop);
    SetLabel(end1);
    PLL.Put(iSTB+0*fRS+dest*fRA+1);
    PutBranch(end);
    SetLabel(end0);
    PLL.Put(iSTB+0*fRS+dest*fRA+(x.offset MOD LowWord));
    SetLabel(end);
    PLL.FreeTempR(t0); PLL.FreeTempR(t1); PLL.FreeTempR(src); PLL.FreeTempR(dest); PLL.FreeTempCRBs({cond*4..cond*4+3})
  END PPCcopy;

  PROCEDURE Copy* (VAR x, y: PLL.Item); (* copy y to x *)
    VAR len: PLL.Item;
  BEGIN
    IF (y.typ^.form = String) & (x.typ^.comp = Array) THEN
      len.mode := Con; len.offset := y.adr; len.typ := PLT.linttyp; Move(x, y, len, TRUE)
    ELSE PPCcopy(x, y)
    END
  END Copy;

  PROCEDURE With* (VAR x: PLL.Item);
  BEGIN
    IF x.mode IN {Reg, Based, Indexed} THEN PLL.FreeTempR(x.reg) END;
    IF x.mode = Indexed THEN PLL.FreeTempR(x.offset) END
  END With;

  PROCEDURE Msk* (VAR x, y: PLL.Item; rt: LONGINT);
    VAR s, mb: LONGINT;
  BEGIN y.offset := -1-y.offset;
    ASSERT((y.mode = Con) & (SYSTEM.VAL(SET, y.offset)*SYSTEM.VAL(SET, y.offset+1) = {}));
    Load(x, -1); mb := CNTLZ(y.offset); IF mb < 24 THEN MakeReg(x, -1) END;
    s := x.reg; PLL.FreeTempR(s); rt := CheckR(rt); PLL.Put(iRLINM+rt*fRA+s*fRS+mb*fMB+31*fME);
    x.mode := Reg; x.reg := rt
  END Msk;

  PROCEDURE Compare* (VAR x, y: PLL.Item; subcl: INTEGER);
    VAR f, f1, s1, s2, t1, t2, t3, t4, b, bitNo: LONGINT; pol: BOOLEAN; lstlab, lastlab, endlab: PLL.Label;
  BEGIN subcl:=subcl-TdopEql+eql;
    CASE x.typ^.form OF
      Real, LReal:
        Load(x, -1); Load(y, -1); s1 := x.reg; s2 := y.reg; PLL.FreeTempF(s1); PLL.FreeTempF(s2);
        f := PLL.GetTempCRF(); PLL.Put(iFCMPU+f*fBF+s1*fFRA+s2*fFRB)
    |  Byte, Char, SInt, Int, LInt, Set, Pointer, ProcTyp:
        IF x.typ^.form = ProcTyp THEN x.typ := PLT.linttyp; y.typ := PLT.linttyp END;
        IF x.mode = Con THEN subcl := switch[subcl-eql]; f := IntCmpImm(y, x)
        ELSIF y.mode = Con THEN f := IntCmpImm(x, y)
        ELSE f := IntCmp(x, y)
        END
    |  Bool:
        IF (x.mode = Cond) OR (y.mode = Cond) THEN
          IF x.mode # Cond THEN Load(x, -1); RegToCond(x) END;
          IF y.mode # Cond THEN Load(y, -1); RegToCond(y) END;
          pol := subcl = eql; s1 := x.reg; s2 := y.reg;
          IF s1 < 0 THEN s1 := -1-s1; pol := ~pol END;
          IF s2 < 0 THEN s2 := -1-s2; pol := ~pol END;
          PLL.FreeTempCRBs({s1, s2}); bitNo := PLL.GetTempCRB();
          IF pol THEN f := iCREQV ELSE f := iCRXOR END;
          PLL.Put(f+bitNo*fBT+s1*fBA+s2*fBB);
          x.mode := Cond; x.reg := bitNo; RETURN
        ELSE
          f := IntCmp(x, y)
        END
    |  String, Comp:
      (* new string compare:
          addi  src, src, -1
          addi  dest, dest, -1

        @1
          lbzu  r5,1(src)
          cmpwi  r5, 0
          lbzu  r6,1(dest)
          cmpw  r5, r6
          beq @end
          beq @1
        @end

      *)
          LoadAddr(x, -1); t1 := x.reg;
          IF ~(t1 IN PLL.TempRegs) THEN t1 := PLL.GetTempR(); MoveReg(t1, x.reg) END;
          LoadAddr(y, -1); t2 := y.reg;
          IF ~(t2 IN PLL.TempRegs) THEN t2 := PLL.GetTempR(); MoveReg(t2, y.reg) END;
          PLL.Put(iCAL+t1*fRT+t1*fRA+0FFFFH);
          PLL.Put(iCAL+t2*fRT+t2*fRA+0FFFFH);

          lstlab := 0; endlab := 0; SetLabel(lstlab);
          t3 := PLL.GetTempR(); t4 := PLL.GetTempR();
          f := PLL.GetTempCRF(); f1 := PLL.GetTempCRF();
          PLL.Put(iLBZU+t3*fRT+t1*fRA+1);
          PLL.Put(iLBZU+t4*fRT+t2*fRA+1);
          PLL.Put(iCMPLI+f1*fBF+t3*fRA+0);
          PLL.Put(iCMPL+f*fBF+t3*fRA+t4*fRB);
          PutBranchInstr(iBT+(f1*4+bEQ)*fBI, endlab);
          PutBranchInstr(iBT+(f*4+bEQ)*fBI, lstlab);
          SetLabel(endlab);
          PLL.FreeTempR(t1); PLL.FreeTempR(t2); PLL.FreeTempR(t3); PLL.FreeTempR(t4);
          PLL.FreeTempCRBs({f1*4..f1*4+3});
        (*  POWER instruction sequence
          t1 := PLL.GetTempR(); PLL.Put(iCAL+t1*fRT+4); PLL.Put(iMTSPR+t1*fRS+spXER*fSPR);
          PLL.Put(iCAL);
          s1 := x.reg; s2 := y.reg; t2 := PLL.GetTempR(); f := PLL.GetTempCRF();
          b := PLL.GetCRF0(); IF b # 0 THEN PLL.err(215) END;
          lstlab := 0; SetLabel(lstlab); PLL.Put(iLSCBX+t1*fRT+s1*fRA+fREC); PLL.Put(iLSCBX+t2*fRT+s2*fRA);
          lastlab := 0; PutBranchInstr(iBM, lastlab); PLL.Put(iCMPL+f*fBF+t1*fRA+t2*fRB);
          PLL.Put(iAI+4); endlab := 0; PutBranchInstr(iBF+(f*4+bEQ)*fBI, endlab); PutBranch(lstlab);
          SetLabel(lastlab); PLL.Put(iMFSPR+spXER*fSPR); PLL.Put(iSFI+4);
          PLL.Put(iRLINM+3*fSH+28*fME); PLL.Put(iSR+t1*fRS+t1*fRA); PLL.Put(iSR+t2*fRS+t2*fRA);
          PLL.Put(iCMPL+f*fBF+t1*fRA+t2*fRB); SetLabel(endlab);
          PLL.FreeTempCRBs({b*4..b*4+3}); PLL.FreeTempR(s1); PLL.FreeTempR(s2);
          PLL.FreeTempR(t1); PLL.FreeTempR(t2)
        *)
    END;
    bitNo := CRbit[subcl-eql]; b := bitNo; IF b < 0 THEN b := -1-b END;
    INC(b, f*4); PLL.FreeTempCRBs({f*4..f*4+3}-{b}); IF bitNo < 0 THEN b := -1-b END;
    x.mode := Cond; x.reg := b
  END Compare;

  PROCEDURE Len* (VAR x, y: PLL.Item; rt: LONGINT);
  BEGIN
    ASSERT(x.mode = Based); PLL.FreeTempR(x.reg);
    IF x.dmode = Reg THEN
      x.mode := Reg; x.reg := x.dreg+y.offset+1
    ELSE
      x.mode := x.dmode; x.reg := x.dreg; x.offset := x.adr+y.offset*4+4
    END;
    IF x.dreg # -1 THEN PLL.UnholdTempR(x.dreg); PLL.FreeTempR(x.dreg); x.dreg := -1 END
  END Len;

  PROCEDURE SYSbit* (VAR x, y: PLL.Item);
    VAR z: PLL.Item;
  BEGIN
    Load(x, -1); MakeReg(x, -1); z := x; z.mode := Based; z.offset := 0; z.typ := PLT.settyp;
    x.mode := y.mode; x.reg := y.reg; x.offset := y.offset; x.typ := y.typ; x.dreg := y.dreg; In(x, z)
  END SYSbit;

  PROCEDURE Trap* (type: INTEGER);
  BEGIN PLL.SetTrap(type); PLL.Put(iT+tALWAYS*fTO)
  END Trap;

  PROCEDURE EnterLoop*;
  BEGIN DEC(LoopLevel); LoopStart[LoopLevel] := 0; LoopEnd[LoopLevel] := 0; SetLabel(LoopStart[LoopLevel])
  END EnterLoop;

  PROCEDURE ExitLoop*;
  BEGIN PutBranch(LoopEnd[LoopLevel])
  END ExitLoop;

  PROCEDURE EndLoop*;
  BEGIN PutBranch(LoopStart[LoopLevel]); SetLabel(LoopEnd[LoopLevel]); INC(LoopLevel)
  END EndLoop;

  PROCEDURE Case* (VAR x: PLL.Item; low, high: LONGINT; VAR table: LONGINT);
    VAR y: PLL.Item; c, t1, t2: LONGINT;
  BEGIN
    Load(x, -1); MakeReg(x, -1); x.typ := PLT.linttyp; y.dreg := -1;
    IF low # 0 THEN
      y.mode := Con; y.offset := low; y.typ := PLT.linttyp; Minus(x, y, -1); DEC(high, low)
    END;
    t1 := x.reg; ASSERT(high <= 32767);
    c := PLL.GetTempCRF(); PLL.Put(iCMPLI+c*fBF+t1*fRA+high); c := c*4; PLL.FreeTempCRBs({c..c+3}-{c+bGT});
    y.mode := Cond; y.reg := c+bGT; y.Tjmp := 0; y.Fjmp := 0; y.typ := PLT.booltyp; PutCondBranch(y, TRUE);
    PLL.FreeTempR(t1); t2 := PLL.GetTempR(); PLL.FreeTempR(t2); PLL.Put(iRLINM+t2*fRA+t1*fRS+2*fSH+29*fME);
    PLL.AllocCaseTable(high, table);
    t1 := PLL.GetTempR(); PLL.FreeTempR(t1); PLL.Put(iCAL+t1*fRT+SB*fRA+(table MOD 10000H));
    y.mode := Indexed; y.reg := t1; y.offset := t2; y.typ := PLT.linttyp; Load(y, -1);
    ASSERT(y.mode = Reg);
    t1 := y.reg; PLL.FreeTempR(t1); PLL.Put(iMTSPR+spCTR*fSPR+t1*fRS);
    PLL.SetCaseBranch(table); PLL.Put(iBCC+cALWAYS*fBO);
    SetLabel(y.Tjmp); PLL.FixCase(0, high, table)
  END Case;

  PROCEDURE Call* (VAR x: PLL.Item; outparsize: LONGINT);
    VAR sl, t, offset: LONGINT; y, z: PLL.Item;
  BEGIN
    y.dreg := -1; z.dreg := -1;
    IF outparsize > aopSize+32 THEN aopSize := outparsize-32 END;
    IF (x.mode = LProc) OR ((x.mode = XProc) & (x.mnolev = 0)) THEN
      IF x.mnolev > 0 THEN
        sl := FindFP(PLL.level, x.mnolev, SLpar);
        IF sl # SLpar THEN sl := CheckVFP(sl); PLL.Put(iCAL+SLpar*fRT+sl*fRA) END
      END;
      PLL.PutLCall(x)
    ELSIF x.mode = XProc THEN
      y.mode := Based; y.reg := SB; y.offset := -(x.mnolev*4)+PLL.linkTable; y.typ := PLT.linttyp;
      z.mode := Reg; z.reg := SB; z.typ := PLT.linttyp; Assign(z, y);
      PLL.PutXCall(x);
      PLL.Put(iL+SB*fRT+SP*fRA+20);
    ELSE (* x.mode IN {Var, VarPar, Based, Reg} *)
      IF x.mode # Reg THEN
        Base(*OrInx*)(x, -1); ShortBase(x, -1); t := x.reg; offset := x.offset; PLL.FreeTempR(t);
        PLL.Put(iL+t*fRA+(offset MOD LowWord));
        PLL.Put(iMTSPR+spCTR*fSPR);
        IF nilchk THEN PLL.SetTrap(NilTrap); PLL.Put(iTI+tEQ*fTO+0*fRA) END;
        PLL.Put(iL+SB*fRT+t*fRA+((offset+4) MOD LowWord))
      ELSE
        t := x.reg; PLL.Put(iMTSPR+spCTR*fSPR+t*fRS);
        IF nilchk THEN PLL.SetTrap(NilTrap); PLL.Put(iTI+tEQ*fTO+t*fRA) END;
        MoveReg(SB, t+1)
      END;
      PLL.Put(iBCC+cALWAYS*fBO+fLK); PLL.Put(iL+SB*fRT+SP*fRA+20)
    END
  END Call;

  PROCEDURE GetMethod* (VAR x: PLL.Item; typ: PLT.Struct; deref, super: BOOLEAN);
    VAR tag: PLL.Item;
  BEGIN
    IF super THEN
      IF typ^.form = Pointer THEN typ := typ^.BaseTyp END;
      typ := typ^.BaseTyp;
      tag.mode := Var; tag.mnolev := -PLT.GetTypMno(typ); tag.offset := typ^.tdadr; tag.typ := PLT.linttyp; tag.dreg := -1;
      Load(tag, -1);
      x.mode := Based; x.reg := tag.reg; x.offset := -76-x.offset*8
    ELSE
      IF deref THEN
        tag.mode := Based; tag.reg := 3; tag.offset := -4; tag.typ := PLT.linttyp; tag.dreg := -1;
        Load(tag, -1);
        x.mode := Based; x.reg := tag.reg; x.offset := -76-x.offset*8
      ELSE
        x.mode := Based; x.reg := 4; x.offset := -76-x.offset*8
      END
    END
  END GetMethod;

  PROCEDURE SaveRegisters* (VAR x: PLL.Item; VAR saved: PLL.SaveDesc);
  BEGIN PLL.SaveRegisters(x, saved, sSize)
  END SaveRegisters;

  PROCEDURE RestoreRegisters* (VAR res: PLL.Item; VAR saved: PLL.SaveDesc; rt: LONGINT);
  BEGIN PLL.RestoreRegisters(res, saved, rt)
  END RestoreRegisters;

  PROCEDURE DynArrCopy (p: PLT.Object; leaf, saveCR: BOOLEAN);
    VAR t0, t1, t2, t3, ralloc, rt: LONGINT; x, y, z, h, hd: PLL.Item; typ: PLT.Struct; loop: PLL.Label;
  BEGIN
    (* get source into y, dest into x *)
    typ := p^.typ; ralloc := p^.adr; y.typ := PLT.linttyp; y.dreg := -1;
    IF ralloc < 0 THEN ralloc := -1-ralloc; y.mode := SHORT(SHORT(ralloc DIV 32)); y.reg := ralloc MOD 32
    ELSE y.mode := Based; y.reg := FP; y.offset := (*ralloc*) p^.linkadr
    END;
    y.dmode := y.mode; y.dreg := SHORT(SHORT(y.reg)); y.adr := y.offset;
    ralloc := p^.linkadr; x.typ := PLT.linttyp;
    IF ralloc < 0 THEN ralloc := -1-ralloc; x.mode := SHORT(SHORT(ralloc DIV 32)); rt := ralloc MOD 32; x.reg := rt
    ELSE x.mode := Based; x.reg := FP; x.offset := ralloc; rt := -1
    END;
    x.dmode := x.mode; x.dreg := SHORT(SHORT(x.reg)); x.adr := x.offset;
    (* move len part of descriptor *)
    hd := x; h.typ := PLT.linttyp; h.dreg := -1;
    IF y.dmode = Reg THEN
      t0 := typ^.n; h.mode := Reg; h.reg := y.dreg+1;
      WHILE t0 >= 0 DO
        IF hd.mode = Reg THEN INC(hd.reg) ELSE INC(hd.offset, 4) END;
        Assign(hd, h); INC(h.reg); DEC(t0)
      END
    END;
    (* compute type size into z *)
    Load(y, -1); y.mode := Based; y.offset := 0; y.dmode := x.dmode; y.dreg := x.dreg; y.adr := x.adr; z := y;
    TypeSize(z, typ, -1); Load(z, -1); MakeReg(z, -1); t0 := z.reg;
    (* align to 8 and allocate the space *)
    t1 := PLL.GetTempR(); PLL.Put(iL+t1*fRT+SP*fRA); (* t1 = dynamic link *)
    t2 := PLL.GetTempR(); PLL.Put(iAI+t2*fRT+t0*fRA+7);
    PLL.FreeTempR(t0); t0 := PLL.GetTempR(); PLL.Put(iRLINM+t2*fRS+t0*fRA+28*fME); PLL.FreeTempR(t2);
    (*z.reg := t0; *)PLL.Put(iSF+SP*fRT+t0*fRA+SP*fRB); PLL.Put(iST+t1*fRS+SP*fRA); PLL.FreeTempR(t1);
    IF ~leaf THEN
      PLL.Put(iST+SB*fRS+SP*fRA+20); (*PLL.Put(iST+t4*fRS+SP*fRA+8); PLL.FreeTempR(t4)*)
    END;
    (* this is the assignment of the new pointer *)
    rt := CheckR(rt); PLL.Put(iCAL+rt*fRT+SP*fRA+(FPlink MOD LowWord)); FPlink := SHORT(1-PLL.pc);
    h.mode := Reg; h.reg := rt; h.typ := PLT.linttyp; Assign(x, h);
    (* this is the actual move step *)
    PLL.FreeTempR(t0); t1 := PLL.GetTempR(); PLL.Put(iRLINM+t0*fRS+t1*fRA+29*fSH+3*fMB+31*fME);
    PLL.Put(iMTSPR+t1*fRS+spCTR*fSPR); PLL.FreeTempR(t1);
    DEC(y.offset, 4); LoadAddr(y, -1); t1 := y.reg;
    t0 := PLL.GetTempR(); PLL.Put(iCAL+t0*fRT+SP*fRA+(FPlink4 MOD LowWord)); FPlink4 := SHORT(1-PLL.pc);
    (*t2 := PLL.GetTempRegs(2, {}); t3 := t2+1;*) t2 := PLL.GetTempR(); t3 := PLL.GetTempR();
    loop := 0; SetLabel(loop);
    PLL.Put(iLU+t2*fRT+t1*fRA+4); PLL.Put(iLU+t3*fRT+t1*fRA+4);
    PLL.Put(iSTU+t2*fRS+t0*fRA+4); PLL.Put(iSTU+t3*fRS+t0*fRA+4);
    PutBranchInstr(iBCNTNZ, loop);
    (*PLL.FreeTempRegs(t2, 2); *) PLL.FreeTempR(t2); PLL.FreeTempR(t3); PLL.FreeTempR(t0); PLL.FreeTempR(t1)
  END DynArrCopy;

  PROCEDURE InitPtrs* (proc, locals: PLT.Object);
    CONST MaxPtrs = 16;
    VAR
      reg, ptr: LONGINT; nofptrs: INTEGER;
      ptrTab: ARRAY MaxPtrs+1 OF LONGINT;
      obj, lastobj, firstobj: PLT.Object;
      size, x: PLL.Item;
      loop: PLL.Label;
  BEGIN
    IF initstack THEN
      reg := -1; obj := locals;
      WHILE obj # NIL DO
        IF (obj.linkadr >= 0) & (obj.mode = Var) THEN
          IF (lastobj = NIL) OR (lastobj.linkadr < obj.linkadr) THEN lastobj := obj END;
          IF (firstobj = NIL) OR (firstobj.linkadr > obj.linkadr) THEN firstobj := obj END
        ELSIF (obj.linkadr < 0) & (obj.mode = Var) & (-1-obj.linkadr DIV 32 = Reg) THEN
          reg := (-1-obj^.linkadr) MOD 32; PLL.Put(iCAL+reg*fRT)
        END;
        obj := obj.nxtobj
      END;

      IF lastobj # NIL THEN
        size.mode := Con; size.typ := PLT.linttyp;
        size.offset := lastobj.linkadr + lastobj.typ.size - firstobj.linkadr;
        INC(size.offset, (-size.offset) MOD 4);
        size.offset := size.offset DIV 4;
        Load(size, -1); PLL.Put(iMTSPR+spCTR*fSPR+size.reg*fRS); PLL.FreeTempR(size.reg);
        IF reg < 0 THEN reg := 0; PLL.Put(iCAL) END;
        IF (firstobj.linkadr DIV 4)*4 = 4 THEN
          ptr := PLL.GetTempR(); PLL.Put(iCAL+ptr*fRT+FP*fRA)
        ELSE
          x.mode := Based; x.reg := FP; x.offset := (firstobj.linkadr DIV 4)*4-4; x.typ := PLT.linttyp;
          LoadAddr(x, -1); ptr := x.reg
        END;
        SetLabel(loop); PLL.Put(iSTU+reg*fRS+ptr*fRA+4); PutBranchInstr(iBCNTNZ, loop);
        PLL.FreeTempR(ptr)
      END
    ELSE
      reg := -1; obj := locals; (* proc.par; *) (* local variables *)
      WHILE obj # NIL DO  (* find pointer registers *)
        IF (obj^.linkadr < -1) & (obj^.typ^.form = Pointer) & (obj.mode=Var) THEN
          reg := (-1-obj^.linkadr) MOD 32; PLL.Put(iCAL+reg*fRT)
        END;
        obj := obj.nxtobj;
      END;
      nofptrs := 0; obj := locals;  (* proc.par; *)
      WHILE (obj # NIL) & (nofptrs <= MaxPtrs) DO (* find pointers in memory *)
        IF (obj^.linkadr >= 0) & (obj.mode=Var) THEN PLL.FindPtrs(obj^.typ, obj^.linkadr, ptrTab, nofptrs); lastobj := obj END;
        obj := obj.nxtobj;
      END;
      IF nofptrs > MaxPtrs THEN (* initialize from the first pointer to the end of the frame *)
        obj := lastobj;
        WHILE obj # NIL DO
          IF (obj^.linkadr >= 0) & (obj.mode=Var) THEN lastobj := obj END;
          obj := obj.nxtobj
        END;
        size.mode := Con; size.typ := PLT.linttyp; size.offset := (lastobj^.linkadr + lastobj^.typ^.size - ptrTab[0]) DIV 4;
        Load(size, -1); PLL.Put(iMTSPR+spCTR*fSPR+size.reg*fRS); PLL.FreeTempR(size.reg);
        IF reg < 0 THEN reg := 0; PLL.Put(iCAL) END;
        IF ptrTab[0] = 4 THEN (* address to be loaded would become 0(FP), therefore copy *)
          ptr := PLL.GetTempR(); PLL.Put(iCAL+ptr*fRT+FP*fRA)
        ELSE
          x.mode := Based; x.reg := FP; x.offset := ptrTab[0]-4; x.typ := PLT.linttyp;
          LoadAddr(x, -1); ptr := x.reg
        END;
        SetLabel(loop); PLL.Put(iSTU+reg*fRS+ptr*fRA+4); PutBranchInstr(iBCNTNZ, loop);
        PLL.FreeTempR(ptr)
      ELSIF nofptrs > 0 THEN
        IF reg < 0 THEN reg := 0; PLL.Put(iCAL) END;
        size.typ := PLT.linttyp; size.mode := Reg; size.reg := reg;
        x.typ := PLT.linttyp; x.mode := Based;
        WHILE nofptrs > 0 DO DEC(nofptrs);
          x.reg := FP; x.offset := ptrTab[nofptrs]; Store(x, size)
        END
      END
    END
  END InitPtrs;

  PROCEDURE Enter* (n, locals: PLT.Object);
    VAR l: PLL.Label; x, y: PLL.Item; ralloc, falloc, calloc, fsize: LONGINT; parR, parF: SET;
      p: PLT.Object; typ: PLT.Struct; form, comp, nrReg: LONGINT; rdest, leaf: BOOLEAN;
  BEGIN
    x.dreg := -1; y.dreg := -1;
    IF n # NIL THEN
      IF n^.mode = LProc THEN
        l := SHORT(n^.adr); IF l = -1 THEN l := 0 END;
        SetLabel(l); n^.adr := l
      ELSE
        ralloc := n^.adr MOD LowWord;
        IF PLL.entry[ralloc] = -1 THEN PLL.entry[ralloc] := 0 END;
        SetLabel(PLL.entry[ralloc])
      END;
      IF n.linkadr>=0 THEN PLL.FixupProcAsgn(n.linkadr) END;
      FP := 31;
      fsize := n^.intval2; calloc := n^.ival; ralloc := (calloc DIV 1024) MOD 32;
      falloc := (calloc DIV 32) MOD 32; calloc := calloc MOD 32;
      parR := n^.setval; parF := SYSTEM.ROT(parR, -16)*{1..13}; parR := SYSTEM.LSH(parR, -1)*{3..10};
      leaf := n^.leaf & (falloc = 31); n^.leaf := leaf;
      IF n^.level > 0 THEN INCL(parR, SLpar) END
    ELSE
      ralloc := 30; falloc := 31; calloc := 19; fsize := 8; parR := {}; parF := {}; FP := 31; leaf := FALSE;
      IF PLL.entry[0] = -1 THEN PLL.entry[0] := 0 END;
      SetLabel(PLL.entry[0])
    END;
    PLL.LockTempR(parR); PLL.LockTempF(parF);
    PLL.GenProcEntry(fsize, ralloc, falloc, calloc, FP, leaf, (n # NIL) & (n^.level > 0) );
    IF n # NIL THEN p := n.par;
      WHILE p # NIL DO
        IF p^.adr < 0 THEN
          typ := p^.typ; form := typ^.form;
          IF ((p^.mode # Var)  & (p.mode # Par) ) OR (form # Comp)  THEN
            IF (p^.mode = VarPar) THEN
              IF form = Comp THEN comp := typ^.comp;
                IF comp = DynArr THEN nrReg := typ^.n+2
                ELSIF comp = Record THEN nrReg := 2
                ELSE nrReg := 1
                END
              ELSE nrReg := 1
              END;
              typ := PLT.linttyp
            ELSE
              nrReg := 1
            END;
            ralloc := -1-p^.adr; y.mode := SHORT(SHORT(ralloc DIV 32)); y.reg := ralloc MOD 32;
            (*y.typ := PLT.linttyp;*) y.typ := typ;
            y.Tjmp := 0; y.Fjmp := 0; ralloc := p^.linkadr; rdest := ralloc < 0;
            IF rdest THEN ralloc := -1-ralloc; x.mode := SHORT(SHORT(ralloc DIV 32)); x.reg := ralloc MOD 32
            ELSE x.mode := Based; x.reg := FP; x.offset := ralloc
            END;
            (*x.typ := PLT.linttyp;*) x.typ := typ;
            REPEAT
              Assign(x, y); INC(y.reg); DEC(nrReg);
              IF rdest THEN INC(x.reg, 1) ELSE INC(x.offset, 4) END
            UNTIL nrReg = 0
          END
        END;
        p := p.nxtobj
      END
    END;
    aopSize := 0; sSize := 0; SLsize := 0;
    IF (n # NIL) & (n^.level > 0) THEN
      y.mode := Reg; y.reg := SLpar; y.typ := PLT.linttyp;
      x.mode := Based; x.reg := FP; x.offset := -4; x.typ := PLT.linttyp;
      Assign(x, y); SLsize := 8
    END;
    IF n # NIL THEN p := n.par; FPlink := 0; FPlink4 := 0;
      WHILE p # NIL DO
        typ := p^.typ; form := typ^.form;
        IF ((p^.mode = Var) OR (p.mode=Par)) & (form = Comp) THEN
          comp := typ^.comp;
          IF comp = DynArr THEN DynArrCopy(p, leaf, calloc < 19)
          ELSE
            ralloc := p^.adr; y.typ := PLT.linttyp;
            IF ralloc < 0 THEN y.reg := (-1-ralloc) MOD 32
            ELSE y.mode := Based; y.reg := FP; y.offset := ralloc+fsize; Load(y, -1)
            END;
            y.mode := Based; y.typ := p^.typ; y.offset := 0;
            x.mode := Based; x.reg := FP; x.offset := p^.linkadr; x.typ := p^.typ;
            Assign(x, y)
          END
        END;
        p := p.nxtobj
      END
    END;
    IF (n # NIL) & ptrinit THEN InitPtrs(n, locals) END;
    leaveProc := 0;
  END Enter;

  PROCEDURE Leave* (VAR n: PLT.Object);
    VAR regs, fsize, psize: LONGINT;
  BEGIN
    INC(sSize, sSize MOD 8); psize := aopSize+sSize+SLsize+8*4+6*4; INC(psize, psize MOD 8);
    IF n # NIL THEN
      PLL.FixupFP(FPlink, FPlink4, psize-(sSize+SLsize));
      IF n^.typ^.form # NoTyp THEN
        IF n^.typ^.form IN {Real, LReal} THEN PLL.LockParF(1)
        ELSE
          IF n^.typ^.form = ProcTyp THEN PLL.LockParR(4) END;
          PLL.LockParR(3)
        END;
        PLL.SetTrap(FuncTrap); PLL.Put(iT+cALWAYS*fTO)
      END;
      SetLabel(leaveProc);
      regs := n^.ival; fsize := n^.intval2;
      PLL.GenProcExit(fsize, psize, (regs  DIV 1024) MOD 32, (regs DIV 32) MOD 32, regs MOD 32, FP, n^.leaf);
      PLL.FreePar;
      (* PLL.OutRefPoint(fsize, psize, (regs DIV 1024) MOD 32, (regs DIV 32) MOD 32, regs MOD 32, n^.leaf) *)
    ELSE
      SetLabel(leaveProc);
      PLL.GenProcExit(8, psize, 30, 31, 19, FP, FALSE);
      (* PLL.OutRefPoint(8, psize, 30, 31, 19, FALSE) *)
    END;
    IF n # NIL THEN n.lim := PLL.pc END
  END Leave;

  PROCEDURE Return* (VAR x: PLL.Item);
  BEGIN
    IF x.mode = FReg THEN PLL.FreeTempF(x.reg)
    ELSIF x.mode = Reg THEN PLL.FreeTempR(x.reg);
      IF x.typ^.form = ProcTyp THEN PLL.FreeTempR(x.reg+1) END
    END;
    PutBranch(leaveProc)
  END Return;

  PROCEDURE Assign* (VAR x, y: PLL.Item);
    VAR rt, t: LONGINT; z: PLL.Item;
  BEGIN
    IF y.typ^.form = Comp THEN
      z.mode := Con; z.typ := PLT.linttyp; z.offset := x.typ^.size; Move(x, y, z, FALSE)
    ELSIF x.typ^.form = ProcTyp THEN
      IF y.mode = XProc THEN
        rt := -1; IF x.mode = Reg THEN rt := x.reg END;
        z := y; PLL.LoadProcAddr(z, rt); x.typ := PLT.linttyp; Assign(x, z);
        IF y.mnolev = 0 THEN y.mode := Reg ELSE y.mode := Based; y.offset := -(y.mnolev*4)+PLL.linkTable END;
        y.reg := SB; y.typ := PLT.linttyp;
        IF x.mode = Reg THEN INC(x.reg) ELSE INC(x.offset, 4) END;
        Assign(x, y)
      ELSIF y.mode = Con THEN ASSERT(y.typ^.form = NilTyp);
        IF x.mode # Reg THEN Base(x, -1) END;
        x.typ := PLT.linttyp; z := zero; Assign(x, z);
        IF x.mode = Reg THEN INC(x.reg) ELSE INC(x.offset, 4) END;
        Assign(x, z)
      ELSE
        IF x.mode # Reg THEN Base(x, -1) END;
        IF y.mode # Reg THEN Base(y, -1) END;
        x.typ := PLT.linttyp; y.typ := PLT.linttyp;
        z := y; Assign(x, y);
        IF x.mode = Reg THEN INC(x.reg) ELSE INC(x.offset, 4) END;
        IF z.mode = Reg THEN INC(z.reg) ELSE INC(z.offset, 4) END;
        Assign(x, z)
      END
    ELSIF y.typ^.form = String THEN
      Copy(x, y)
    ELSIF (y.typ^.form = Bool) & (y.mode = Con) & (x.mode = Cond) THEN
      rt := x.reg; ASSERT((0 <= rt) & (rt <= 31));
      IF y.offset = 0 THEN PLL.Put(iCRXOR+rt*fBT) ELSE PLL.Put(iCREQV+rt*fBT) END
    ELSE t := -1; rt := -1;
      IF x.mode = Reg THEN
        rt := x.reg; IF (y.typ^.form # SInt) OR (y.mode = Con) THEN t := rt END
      ELSIF x.mode = FReg THEN
        rt := x.reg; IF y.typ^.form IN {Real, LReal} THEN t := x.reg END
      END;
      Load(y, t); Convert(y, x.typ, rt, x.mode = FReg); Store(x, y)
    END
  END Assign;

  PROCEDURE Increment* (VAR x, y: PLL.Item; inc: BOOLEAN);
    VAR z: PLL.Item; regs: SET; rt: LONGINT;
  BEGIN
    IF x.mode = Reg THEN
      IF inc THEN Plus(x, y, x.reg) ELSE Minus(x, y, x.reg) END
    ELSE
      BaseOrInx(x, -1);
      IF x.mode = Based THEN ShortBase(x, -1) END;
      z := x;
      IF x.mode = Indexed THEN rt := PLL.GetTempR(); MoveReg(rt, x.reg); z.reg := rt; PLL.FreeTempR(rt) END;
      IF inc THEN Plus(x, y, -1) ELSE Minus(x, y, -1) END;
      Store(z, x);
    END
  END Increment;

  PROCEDURE Include* (VAR x, y: PLL.Item);
    VAR z: PLL.Item;
  BEGIN
    IF y.mode = Con THEN
      y.offset := SYSTEM.VAL(LONGINT, {y.offset});
      y.typ := PLT.settyp
    ELSE SetElem(y, -1)
    END;
    IF x.mode = Reg THEN Plus(x, y, x.reg)
    ELSE BaseOrInx(x, -1);
      IF x.mode = Based THEN ShortBase(x, -1) END;
      z := x; Plus(x, y, -1); Store(z, x)
    END
  END Include;

  PROCEDURE Exclude* (VAR x, y: PLL.Item);
    VAR ycon: BOOLEAN; bit, s, t: LONGINT; z: PLL.Item;
  BEGIN
    ycon := y.mode = Con;
    IF ycon THEN bit := y.offset ELSE SetElem(y, -1) END;
    IF x.mode = Reg THEN
      IF ycon THEN PLL.Put(iRLINM+x.reg*fRA+x.reg*fRS+((bit+1) MOD 32)*fMB+((bit-1) MOD 32)*fME)
      ELSE Minus(x, y, x.reg)
      END
    ELSE BaseOrInx(x, -1);
      IF x.mode = Based THEN ShortBase(x, -1) END;
      z := x;
      IF ycon THEN Load(x, -1); s := x.reg; PLL.FreeTempR(s); t := PLL.GetTempR(); PLL.FreeTempR(t);
        PLL.Put(iRLINM+t*fRA+s*fRS+((bit+1) MOD 32)*fMB+((bit-1) MOD 32)*fME); x.reg := t
      ELSE Minus(x, y, -1)
      END;
      Store(z, x)
    END
  END Exclude;

  PROCEDURE Init*;
  BEGIN
    IntToRealAddr := 0; LoopLevel := 16;
    scratch := -1; RealToIntAddr := 0
  END Init;

BEGIN
  BLI[Undef] := -1; BLI[Byte] := iLBZ; BLI[Bool] := iLBZ; BLI[Char] := iLBZ; BLI[SInt] := iLBZ; BLI[Int] := iLHA;
  BLI[LInt] := iL; BLI[Real] := iLFS; BLI[LReal] := iLFD; BLI[Set] := iL; BLI[String] := -1; BLI[NilTyp] := iL;
  BLI[NoTyp] := -1; BLI[Pointer] := iL; XLI[Undef] := -1; XLI[Byte] := iLBZX; XLI[Bool] := iLBZX; XLI[Char] := iLBZX;
  XLI[SInt] := iLBZX; XLI[Int] := iLHAX; XLI[LInt] := iLX; XLI[Real] := iLFSX; XLI[LReal] := iLFDX; XLI[Set] := iLX;
  XLI[String] := -1; XLI[NilTyp] := iLX; XLI[NoTyp] := -1; XLI[Pointer] := iLX;
  BSI[Undef] := -1; BSI[Byte] := iSTB; BSI[Bool] := iSTB; BSI[Char] := iSTB; BSI[SInt] := iSTB; BSI[Int] := iSTH;
  BSI[LInt] := iST; BSI[Real] := iSTFS; BSI[LReal] := iSTFD; BSI[Set] := iST; BSI[String] := -1; BSI[NilTyp] := iST;
  BSI[NoTyp] := -1; BSI[Pointer] := iST; XSI[Undef] := -1; XSI[Byte] := iSTBX; XSI[Bool] := iSTBX; XSI[Char] := iSTBX;
  XSI[SInt] := iSTBX; XSI[Int] := iSTHX; XSI[LInt] := iSTX; XSI[Real] := iSTFSX; XSI[LReal] := iSTFDX; XSI[Set] := iSTX;
  XSI[String] := -1; XSI[NilTyp] := iSTX; XSI[NoTyp] := -1; XSI[Pointer] := iSTX;
  IntToRealBlock[0] := 43X; IntToRealBlock[1] := 30X; IntToRealBlock[2] := 0X; IntToRealBlock[3] := 0X;
  IntToRealBlock[4] := 80X; IntToRealBlock[5] := 0X; IntToRealBlock[6] := 0X; IntToRealBlock[7] := 0X;
  IntToRealBlock[8] := 43X; IntToRealBlock[9] := 30X; IntToRealBlock[10] := 0X; IntToRealBlock[11] := 0X;
  IntToRealBlock[12] := 0X; IntToRealBlock[13] := 0X; IntToRealBlock[14] := 0X; IntToRealBlock[15] := 0X;
  RealToIntBlock[0] := 43X; RealToIntBlock[1] := 30X; RealToIntBlock[2] := 0X; RealToIntBlock[3] := 1X;
  RealToIntBlock[4] := 0X; RealToIntBlock[5] := 0X; RealToIntBlock[6] := 0X; RealToIntBlock[7] := 0X;
  zero.mode := Con; zero.offset := 0; zero.typ := PLT.linttyp; zero.dreg := -1;
  CAPmask.mode := Con; CAPmask.offset := 5FH; CAPmask.typ := PLT.settyp; CAPmask.dreg := -1;
  CRbit[eql-eql] := bEQ; CRbit[neq-eql] := -1-bEQ; CRbit[lss-eql] := bLT; CRbit[leq-eql] := -1-bGT;
  CRbit[gtr-eql] := bGT; CRbit[geq-eql] := -1-bLT;
  switch[eql-eql] := eql; switch[neq-eql] := neq; switch[lss-eql] := gtr; switch[leq-eql] := geq;
  switch[gtr-eql] := lss; switch[geq-eql] := leq;
  ptrinit:=TRUE; initstack := TRUE
END OPLC.
