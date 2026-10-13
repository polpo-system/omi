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

MODULE OPLC;  (*mf 7.11.94 / tk 1.7.96*)

  (* 1.7.96 Method support (mfix) *)
  (* 29.10.96 DynArrBind change *)

IMPORT
  SYS:=SYSTEM, PLT:=OPLT, PLL:=OPLL;

CONST
  TmopNot=0DH; TmopMinus=0EH; TmopAbs=0FH; TmopCap=10H; TmopOdd=11H; UmopConvSet=4AH;
  TdopAnd=12H; TdopOr=13H; TdopTimes=14H; TdopSlash=15H; TdopDiv=16H; TdopMod=17H;
  TdopPlus=18H; TdopMinus=19H; TdopMsk=1AH; TdopAsh=1BH; TdopLen=1CH; TdopIn=1DH;
  TdopEql=1EH; TdopNeq=1FH; TdopLss=20H; TdopLeq=21H; TdopGtr=22H; TdopGeq=23H;
  TasgnIncfn=28H; TasgnDecfn=29H; TasgnInclfn=2AH; TasgnExclfn=2BH; TasgnCopyfn=2CH;
  Tderef=0BH; UvarparIndirect=43H;

  VarPar=3; (*****object modes are different from OP2*****)
  Undef=0; Bool=2; Char=3; SInt=4; Int=5; LInt=6; Real=7; LReal=8; Set=9; String=10; NilTyp=11; TProc = 14;
  NoTyp=12; Pointer=13; ProcTyp=14; Comp=15; Basic=1; Array=2; DynArr=3; Record=4;

  (*PLL Constant Values*) false=0; true=-1;
  (*PLL Register Types*)  Dreg=0; Areg=1; FPR=6;
  (*PLL Data Sizes*)  Half=0; Word=1; Long=2; Double=3; Other=4;
  (*PLL Item Modes*)  Dn=14; An=15; Fn=16; RegInd=17; MemInd=18; Indexed=19; Pop=20; Absolute=21; AbsRef=22; Imm=23; CCR=24;
  (*PLL Opx Modifiers*) opSZ=4000H; opKS=2000H; opRD=1000H; opLS=800H; opXLS=400H; opLD=100H; opXLD=80H;
  (*PLL Op1 Formats*) opNOP1=5; opRx=6; opRxLong=7; opRy=8; opRyLong=9; opEa=10;
  (*PLL Op1 Formats*) opEaLong=11; opRwLong=12; opRzRz=13; opRzRzLong=14;
  (*PLL Op2 Formats*) opNOP2=16; opRyRx=17; opRxRy=18; opEaRn=19; opRnEa=20; opImmEa=21; opEaRwLong=22; opRwEaLong=23;
  (*OPL Type Descriptor*) TprocOffset=4+16*4+64; (* size, 7 extensions, module, name *)

  (*Condition Codes*) ccT=0; ccF=1; ccHI=2; ccLS=3; ccCC=4; ccCS=5; ccNE=6; ccEQ=7;
  (*Condition Codes*) ccGE=12; ccLT=13; ccGT=14; ccLE=15;
  (*Coprocessor Conditions*)  ccfEQ=-1; ccfNE=-14; ccfGT=-18; ccfGE=-19; ccfLT=-20;
  (*Coprocessor Conditions*)  ccfLE=-21;

  intSet={SInt, Int, LInt}; realSet={Real, LReal};

  MaxSInt=7FH;
  MaxInt=7FFFH;



VAR
  D0, F0: PLL.Item;
  cmpCC, cmpCCX, cmpCCF, swapRel, invRel: ARRAY TdopGeq+1 OF INTEGER;
  newSmall, newLarge, newSys: LONGINT;
  inxchk*, typchk*, nilchk*, ptrinit*, dbginfo*: BOOLEAN;


(*Boolean Expressions*)

  PROCEDURE LoadCC(VAR x: PLL.Item);
  BEGIN
    IF  x.mode#CCR  THEN
      IF  x.mode=Imm  THEN
        IF  x.adr=false THEN  PLL.SetCC(x, ccF) ELSE  PLL.SetCC(x, ccT) END
      ELSE  PLL.LoadCC(x) END
    END
  END LoadCC;

  PROCEDURE And(VAR x, y: PLL.Item);
  BEGIN LoadCC(y);
    IF  y.beta#0  THEN  x.beta:=PLL.MergedLinks(x.beta, y.beta) END;  (*Merge Fjmp*)
    x.code:=y.code; x.alpha:=y.alpha  (*Tjmp*)
  END And;

  PROCEDURE Or(VAR x, y: PLL.Item);
  BEGIN LoadCC(y);
    IF  y.alpha#0 THEN  x.alpha:=PLL.MergedLinks(x.alpha, y.alpha)  END;  (*Merge Tjmp*)
    x.code:=y.code; x.beta:=y.beta  (*Fjmp*)
  END Or;

  PROCEDURE CondAnd*(VAR x: PLL.Item);
  BEGIN
    IF  x.mode=CCR  THEN
      IF  x.code#ccT  THEN  PLL.BccLink(PLL.InvertCC(x.code), x.beta) END;  (*B~cond Fjmp*)
      PLL.FixLink(x.alpha)  (*Tjmp here*)
    ELSE  PLL.LoadCC(x); PLL.BccLink(ccEQ, x.beta)  END (*BEQ Fjmp*)
  END CondAnd;

  PROCEDURE CondOr*(VAR x: PLL.Item);
  BEGIN
    IF  x.mode=CCR  THEN
      IF  x.code#ccF  THEN  PLL.BccLink(x.code, x.alpha)  END;  (*Bcond Tjmp*)
      PLL.FixLink(x.beta) (*Fjmp here*)
    ELSE  PLL.LoadCC(x); PLL.BccLink(ccNE, x.alpha) END (*BNE Tjmp*)
  END CondOr;

  PROCEDURE Relation*(VAR x: PLL.Item);
    VAR y: PLL.Item;
  BEGIN
    IF  x.mode=CCR  THEN  y:=x; PLL.GetD(x); PLL.ResolveCC(y, x)  END
  END Relation;


(*Integer Arithmetic*)

  PROCEDURE Increment(VAR x, y: PLL.Item);
    VAR n: LONGINT;
  BEGIN
    IF  y.mode=Imm  THEN  n:=y.adr;
      IF  (n>=-8)&(n<=8)  THEN
        IF  n=0 THEN  PLL.Release(x)
        ELSIF n<0 THEN  PLL.Op1(opEa+opSZ+opRD, 5100H+((-n) MOD 8)*200H, x) (*SUBQ #-y, x*)
        ELSE  PLL.Op1(opEa+opSZ+opRD, 5000H+(n MOD 8)*200H, x)  END (*ADDQ #y, x*)
      ELSE  PLL.Op2(opImmEa+opSZ+opRD, 600H, y, x)  END (*ADDI #y, x*)
    ELSE  PLL.Op2(opLS+opRnEa+opSZ+opRD, 0D100H, y, x)  END (*ADD Dy, x*)
  END Increment;

  PROCEDURE Decrement(VAR x, y: PLL.Item);
    VAR n: LONGINT;
  BEGIN
    IF  y.mode=Imm  THEN  n:=y.adr;
      IF  (n>=-8)&(n<=8)  THEN
        IF  n=0 THEN  PLL.Release(x)
        ELSIF n<0 THEN  PLL.Op1(opEa+opSZ+opRD, 5000H+((-n) MOD 8)*200H, x) (*ADDQ #-y, x*)
        ELSE  PLL.Op1(opEa+opSZ+opRD, 5100H+(n MOD 8)*200H, x)  END (*SUBQ #y, x*)
      ELSE  PLL.Op2(opImmEa+opSZ+opRD, 400H, y, x)  END (*SUBI #y, x*)
    ELSE  PLL.Op2(opLS+opRnEa+opSZ+opRD, 9100H, y, x) END (*SUB Dy, x*)
  END Decrement;

  PROCEDURE Add(VAR x, y: PLL.Item);
    VAR n: LONGINT;
  BEGIN n:=y.adr;
    IF  (y.mode=Imm)&(n>=-8)&(n<=8) THEN
      IF  n#0 THEN
        IF  n< 0  THEN  PLL.Op1(opLD+opRx+opSZ, 5100H+((-n) MOD 8)*200H, x) (*SUBQ #-y, Dx*)
        ELSE  PLL.Op1(opLD+opRx+opSZ, 5000H+(n MOD 8)*200H, x)  END (*ADDQ #y, Dx*)
      END
    ELSE  PLL.Op2(opLD+opEaRn+opSZ, 0D000H, y, x) END (*ADD y, Dx*)
  END Add;

  PROCEDURE Sub(VAR x, y: PLL.Item);
    VAR n: LONGINT;
  BEGIN n:=y.adr;
    IF  (y.mode=Imm)&(n>=-8)&(n<=8) THEN
      IF  n#0 THEN
        IF  n< 0  THEN  PLL.Op1(opLD+opRx+opSZ, 5000H+((-n) MOD 8)*200H, x) (*ADDQ #-y, Dx*)
        ELSE  PLL.Op1(opLD+opRx+opSZ, 5100H+(n MOD 8)*200H, x)  END (*SUBQ #y, Dx*)
      END
    ELSE  PLL.Op2(opLD+opEaRn+opSZ, 9000H, y, x)  END (*SUB y, Dx*)
  END Sub;

  PROCEDURE Mul(VAR x, y: PLL.Item);
  BEGIN
    IF  x.typ=PLT.linttyp THEN  PLL.Op2(opLD+opEaRwLong, 4C000800H, y, x) (*MULS.L y, Dx*)
    ELSIF x.typ=PLT.inttyp  THEN  PLL.Op2(opLD+opEaRn, 0C1C0H, y, x)  (*MULS.W y, Dx*)
    ELSIF y.mode=Imm  THEN  PLL.Op2(opXLD+opEaRn, 0C1C0H, y, x) (*MULS.W y, Dzx*)
    ELSE  PLL.Op2(opXLS+opXLD+opRxRy, 0C1C0H, y, x) END (*MULS.W Dzy, Dzx*)
  END Mul;

  PROCEDURE Div(VAR x, y: PLL.Item);
    VAR rem: PLL.Item;
  BEGIN
    IF  x.typ=PLT.linttyp THEN  PLL.GetD(rem); PLL.Op2(opLD+opEaRwLong, 4C400800H+rem.adr, y, x); (*DIVS.L y, Dx*)
      PLL.Op1(opRx+opRD, 4A80H, rem); PLL.OpW(6C02H); PLL.Op1(opRx, 5380H, x) (*TST.L Drem; BGE +2; SUBQ.L #1, Dx*)
    ELSE
      IF  x.typ=PLT.sinttyp THEN  PLL.Op2(opXLS+opXLD+opRxRy, 81C0H, y, x)  (*DIVS.W XDy, XDx*)
      ELSE  PLL.Op2(opXLD+opEaRn, 81C0H, y, x)  END;  (*DIVS.W y, XDx*)
      PLL.Op1(opRxLong+opKS, 0800001FH, x); PLL.OpW(6702H); PLL.Op1(opRx, 5340H, x) (*BTST #31, Dx; BEQ +2; SUBQ.W #1, Dx*)
    END
  END Div;

  PROCEDURE Mod(VAR x, y: PLL.Item);
    VAR rem: PLL.Item;
  BEGIN
    IF  x.typ=PLT.linttyp THEN  PLL.GetD(rem);
      PLL.Op2(opLS+opXLD+opEaRwLong+opRD, 4C400800H+rem.adr, y, x); x.adr:=rem.adr; (*DIVS.L y, Dx*)
      PLL.Op1(opRx, 4A80H, x); PLL.OpW(6C02H); PLL.Op1(opRy, 0D080H+y.adr, x) (*TST.L Drem; BGE +2; ADD.L Dy, Drem*)
    ELSE
      IF  x.typ=PLT.sinttyp THEN  PLL.Op2(opXLS+opXLD+opRxRy+opKS, 81C0H, y, x) (*DIVS.W XDy, XDx*)
      ELSE  PLL.Op2(opLS+opXLD+opRxRy+opKS, 81C0H, y, x)  END;  (*DIVS.W Dy, XDx*)
      PLL.Op1(opRx, 4840H, x); PLL.Op1(opRx, 4A40H, x); PLL.OpW(6C02H);
      PLL.Op2(opRxRy, 0D040H, y, x) (*SWAP rq; TST.W r; BGE+2; ADD.W Dy, Dx*)
    END
  END Mod;

  PROCEDURE Compare(VAR x, y: PLL.Item; optag: LONGINT);
    VAR f: INTEGER; z: PLL.Item;
  BEGIN f:=x.typ.form;
    IF  (x.mode=Imm)OR((x.mode#Dn)&(y.mode=Dn)) THEN  z:=x; x:=y; y:=z; optag:=swapRel[optag] END;
    IF  f IN {Char..LInt, Set, NilTyp, Pointer, ProcTyp}  THEN
      IF  (y.mode=Imm)&(x.mode#An)  THEN
        IF  y.adr=0 THEN  PLL.Op1(opEa+opSZ, 4A00H, x)  (*TST*)
        ELSE  PLL.Op2(opImmEa+opSZ, 0C00H, y, x)  END (*CMPI*)
      ELSE  PLL.Op2(opLD+opEaRn+opSZ, 0B000H, y, x) END (*CMP y, Dx*)
    ELSIF f=Bool  THEN
      IF  y.mode=Imm  THEN  PLL.Op1(opEa, 4A00H, x);  (*TST.B x*)
        IF  y.adr=true  THEN  optag:=invRel[optag]  END
      ELSE
        IF  y.mode=CCR  THEN  z:=y; y:=x; PLL.GetD(x); PLL.ResolveCC(z, x)  END;
        PLL.Op2(opLD+opEaRn, 0B000H, y, x)  (*CMP.B y, Dx*)
      END
    ELSE  z:=x; PLL.Ref(z); PLL.Ref(y); PLL.GetD(x);  (*Strings*)
      PLL.Op2(opRxRy, 1018H, z, x); PLL.OpW(6706H); (*MOVE.B (Ax)+, Dx; BEQ +6*)
      PLL.Op2(opRxRy+opKS, 0B018H, y, x); PLL.OpL(67F86002H); (*CMP.B (Ay)+, Dx; BEQ -8; BRA +2*)
      PLL.Op2(opRxRy, 0B018H, y, x) (*CMP.B (Ay)+, Dx*)
    END;
    IF  ((f IN {Char, String}) OR (x.typ.comp IN {Array, DynArr}))  THEN  PLL.SetCC(x, cmpCCX[optag])
    ELSE  PLL.SetCC(x, cmpCC[optag])  END
  END Compare;


(*Miscellaneous Functions*)

  PROCEDURE Convert*(VAR x: PLL.Item; f, g: LONGINT);
    VAR y, cr: PLL.Item;
  BEGIN
    IF  g IN realSet  THEN
      IF  f=Char  THEN  PLL.Op1(opLD+opRxLong, 24000FFH, x); x.typ:=PLT.inttyp  END;
      PLL.LoadF(x)
    ELSIF f IN intSet THEN
      IF  g IN intSet THEN
        IF  f < g THEN  PLL.LoadX(x)  (*LONG*)  ELSE  PLL.LoadD(x)  (*SHORT*) END
      ELSIF f # SInt  THEN  PLL.LoadD(x)  END
    ELSIF f IN realSet  THEN  PLL.LoadF(x); y:=x; PLL.GetD(x); x.typ:=PLT.linttyp; PLL.GetD(cr);
      PLL.Op1(opRxLong, 0F200B000H, cr);  (*FMOVE control, Dcr*)
      PLL.Op2(opRxRy+opKS, 2000H, cr, x); (*MOVE.L Dcr, Dx*)
      PLL.Op1(opRxLong, 08800004H, x);  (*BCLR #4, Dx*)
      PLL.Op1(opRxLong, 08C00005H, x);  (*BSET #5, Dx*)
      PLL.Op1(opRxLong, 0F2009000H, x); (*FMOVE Dx, control*)
      PLL.FMove(y, x);
      PLL.Op1(opRxLong+opRD, 0F2009000H, cr)  (*FMOVE Dcr, control*)
    ELSIF f=Char  THEN
      IF  g=LInt  THEN  PLL.Op1(opLD+opRx, 280H, x); PLL.OpL(0FFH)  (*ANDI.L #0FFH, Dx*)
      ELSIF g=Int THEN  PLL.Op1(opLD+opRxLong, 24000FFH, x) END (*ANDI.W #0FFH, Dx*)
    END
  END Convert;

  PROCEDURE ShiftOp(VAR x, y: PLL.Item; op: INTEGER);
    VAR dir, n: LONGINT;
  BEGIN
    IF  y.mode=Imm  THEN  n:=y.adr;
      IF  n#0 THEN
        IF  n>0 THEN  dir:=100H ELSE  dir:=0; n:=-n; y.adr:=n END;
        IF  n<=8  THEN  PLL.Op1(opLD+opRx+opSZ, 0E000H+(n MOD 8)*200H+dir+op*8H, x) (*SH #y, Dx*)
        ELSE  PLL.Op2(opLS+opLD+opRyRx+opSZ, 0E020H+dir+op*8H, y, x)  END (*SH Dy, Dx*)
      END
    ELSE  PLL.LoadD(x);
      IF  y.mode=Dn THEN  PLL.Op1(opRx+opSZ, 4A00H, y)  ELSE  PLL.LoadD(y)  END;  (*TST Dy*)
      PLL.OpW(6B04H); PLL.Op2(opRyRx+opSZ+opKS, 0E120H+op*8H, y, x); PLL.OpW(6004H);  (*BMI +4; LEFT Dy, Dx; BRA +4*)
      PLL.Op1(opRx+opSZ, 4400H, y); PLL.Op2(opRyRx+opSZ, 0E020H+op*8H, y, x)  (*NEG Dy; RIGHT Dy, Dx*)
    END
  END ShiftOp;

  PROCEDURE SetRange*(VAR x, y, z: PLL.Item); (*x:={y .. z}*)
  BEGIN PLL.GetD(x); x.typ:=PLT.settyp;
    IF  (y.mode=Pop)&(z.mode=Pop) THEN  PLL.LoadD(z); PLL.LoadD(y)  END;  (*!*)
    IF  (y.mode=Imm)&(y.adr=0)  THEN  (*MOVQ #-2, Dx; LSL.L z, Dx; NOT.L Dx*)
      PLL.Op1(opRy, 70FEH, x); PLL.Op2(opLS+opRyRx, 0E1A8H, z, x); PLL.Op1(opRx, 4680H, x)
    ELSE
      IF  y.mode=Imm  THEN  y.adr:=SYS.LSH(LONG(LONG(-1)), y.adr); PLL.Move(y, x, LInt)
      ELSE  PLL.Op1(opRy, 70FFH, x); PLL.Op2(opLS+opRyRx, 0E1A8H, y, x) END;  (*MOVQ #-1, Dx; LSL.L Dy, Dx*)
      IF  z.mode=Imm  THEN
        IF  z.adr#31  THEN  z.adr:=-SYS.LSH(LONG(LONG(-1)), z.adr)-1; z.typ:=PLT.linttyp; PLL.Op2(opEaRn, 0C080H, z, x) END (*AND.L #~(2^z), Dx*)
      ELSE  PLL.GetD(y);  (*MOVQ #-2, Dy; LSL.L Dz, Dy; NOT.L Dy; AND.L Dy, Dx*)
        PLL.Op1(opRy, 70FEH, y); PLL.Op2(opLS+opRyRx, 0E1A8H, z, y); PLL.Op1(opRx, 4680H, y); PLL.Op2(opRxRy, 0C080H, y, x)
      END
    END
  END SetRange;

  PROCEDURE New*(VAR x: PLL.Item);
    VAR td: PLL.Item; typ: PLT.Struct; size: LONGINT;
  BEGIN typ:=x.typ; typ:=typ.BaseTyp; PLL.RefToA1(x);
    IF  typ.comp=Record THEN  td.mode:=AbsRef; td.adr:=typ.tdadr; PLL.Op1(opEa+opRD, 2440H, td); PLL.OpW(4EB9H);  (*MOVEA.L td, A2; JSR ().L*)
      IF  typ.size+4 <= 128 THEN  PLL.OpL(newSmall) ELSE  PLL.OpL(newLarge) END
    ELSE  size:=typ.size;
      IF  size<80H  THEN  PLL.OpW(7000H+SHORT(size))  ELSE  PLL.OpW(203CH); PLL.OpL(size) END;  (*MOVE/Q #size, D0*)
      PLL.OpW(4EB9H); PLL.OpL(newSys) (*JSR newSys*)
    END
  END New;

  PROCEDURE Copy*(VAR x, y: PLL.Item);  (*x:=y*)
    VAR s: PLL.Item;
  BEGIN PLL.Ref(y); PLL.Ref(x);
    IF  x.typ.comp=DynArr THEN  PLL.LocalVar(s, x.alpha, x.descr+4, FALSE); PLL.Op1(opEa+opRD, 2000H, s)  (*MOVE.L s, D0*)
    ELSE  s.mode:=Imm; s.adr:=x.typ.size-1; PLL.Move(s, D0, Int)  END;
    PLL.Op2(opRxRy+opRD, 10D8H, y, x); PLL.OpL(57C8FFFCH) (*MOVE.B (Ay)+, (Ax)+; DBEQ.W D0, -4*)
  END Copy;

  PROCEDURE Trap*(n: LONGINT);
  BEGIN PLL.OpL(50FA0000H+n)  (*TPT.W #n*)
  END Trap;

(*Operations*)

  PROCEDURE MOp*(VAR x: PLL.Item; optag: LONGINT);
    VAR f, link: INTEGER; i: PLL.Item;
  BEGIN
    CASE  optag OF
    | UmopConvSet:  (*Set Element*) i:=x; PLL.GetD(x); PLL.Op1(opRx, 4280H, x); (*CLR.L Dx*)
        IF  i.mode=Imm  THEN  PLL.Op1(opRxLong, 8C00000H+i.adr, x)  (*BSET #i, Ds*)
        ELSE  PLL.Op2(opLS+opRyRx, 1C0H, i, x)  END (*BSET Di, Ds*)
    | TmopNot:
        IF  x.mode#CCR  THEN  PLL.LoadCC(x); x.code:=ccEQ
        ELSE  x.code:=PLL.InvertCC(x.code); link:=x.alpha; x.alpha:=x.beta; x.beta:=link  END
    | TmopMinus:  f:=x.typ.form;
        IF  f IN intSet THEN  PLL.Op1(opLD+opRx+opSZ, 4400H, x) (*NEG Dx*)
        ELSIF f IN realSet  THEN  PLL.FOp1(0F200001AH, x) (*FNEG*)
        ELSE  (*f=Set*) PLL.Op1(opLD+opRx, 4680H, x)  END (*NOT.L Dx*)
    | TmopAbs:
        IF  x.typ.form IN realSet THEN  PLL.FOp1(0F2000018H, x) (*FABS*)
        ELSE  PLL.Op1(opLD+opRx+opSZ, 4A00H, x); PLL.OpW(6C02H); PLL.Op1(opRx+opSZ, 4400H, x) END (*TST Dx; BGE+2; NEG Dx*)
    | TmopCap:  PLL.Op1(opLD+opRxLong, 200005FH, x) (*ANDI #5FH, Dx*)
    | TmopOdd:  PLL.Op1(opLD+opRx, 0E208H, x); PLL.SetCC(x, ccCS) (*LSR.B #1, Dx*)
    END
  END MOp;

  PROCEDURE DOp*(VAR x, y: PLL.Item; optag: LONGINT);
    VAR z: PLL.Item; f: INTEGER;
  BEGIN f:=x.typ.form;
    IF  (x.mode=Pop)&(y.mode=Pop) THEN  PLL.LoadD(y); PLL.LoadD(x)  END;  (*!*)
    CASE  optag OF
    | TdopTimes:
        IF  (x.mode=Imm)OR((~(x.mode IN {Dn, Fn}))&(y.mode IN {Dn, Fn}))  THEN  z:=x; x:=y; y:=z  END;
        IF  f IN realSet  THEN  PLL.FOp2(0F2000023H, y, x)  (*FMUL*)
        ELSIF f=Set THEN  PLL.Op2(opLD+opEaRn, 0C080H, y, x)  (*AND.L y, Dx*)
        ELSE  Mul(x, y) END
    | TdopSlash:
        IF  f IN realSet  THEN  PLL.FOp2(0F2000020H, y, x)  (*FDIV*)
        ELSE  (*Set*) PLL.Op2(opLS+opLD+opRyRx, 0B180H, y, x) END (*EOR.L Dy, Dx*)
    | TdopPlus:
        IF  (x.mode=Imm)OR((~(x.mode IN {Dn, Fn}))&(y.mode IN {Dn, Fn}))  THEN  z:=x; x:=y; y:=z  END;
        IF  f IN realSet  THEN  PLL.FOp2(0F2000022H, y, x)  (*FADD*)
        ELSIF f=Set THEN  PLL.Op2(opLD+opEaRn, 8080H, y, x) (*OR.L y, Dx*)
        ELSE  Add(x, y) END
    | TdopMinus:
        IF  f IN realSet  THEN  PLL.FOp2(0F2000028H, y, x)  (*FSUB*)
        ELSIF f=Set THEN
          IF  y.mode=Imm  THEN  y.adr:=-y.adr-1; PLL.Op2(opLD+opEaRn+opSZ, 0C000H, y, x)  (*AND y, Dx*)
          ELSE  PLL.Op1(opLD+opRx, 4680H, y); PLL.Op2(opEaRn, 0C080H, x, y); x:=y END (*NOT.L Dy; AND.L x, Dy*)
        ELSE  Sub(x, y) END
    | TdopDiv:  Div(x, y)
    | TdopMod:  Mod(x, y)
    | TdopAnd:  And(x, y)
    | TdopOr: Or(x, y)
    | TdopEql..TdopGeq:
        IF  f IN realSet  THEN  PLL.FOp2(0F2000038H, y, x); PLL.SetCC(x, cmpCCF[optag]) (*FCMP*)
        ELSE  Compare(x, y, optag)  END
    | TdopIn:
        IF  x.mode=Imm  THEN  PLL.Op1(opLD+opRxLong+opRD, 8000000H+x.adr, y)  (*BTST #x, Dy*)
        ELSE  PLL.Op2(opLS+opLD+opRyRx+opRD, 100H, x, y)  END;  (*BTST Dx, Dy*)
        x.mode:=CCR; x.code:=ccNE; x.alpha:=0; x.beta:=0
    | TdopAsh:
        IF  (y.mode=Imm)&(y.adr=1)  THEN  PLL.Op1(opLD+opRzRz+opSZ, 0D000H, x)  (*ADD Dx, Dx*)
        ELSE  ShiftOp(x, y, 0)  END
    | TdopMsk:  (*y.mode=Imm*)  y.adr:=-y.adr-1; PLL.Op2(opLD+opEaRn+opSZ, 0C000H, y, x)  (*AND y, Dx*)
    | TdopLen:  (*x.mode=MemInd*) x.mode:=RegInd; x.disp:=x.descr+(x.typ.n-y.adr)*8+4; x.typ:=PLT.linttyp; PLL.Op1(opLD+opRx, 5280H, x) (*ADDQ.L #1, Dx*)
    END
  END DOp;

  PROCEDURE AStat*(VAR x, y: PLL.Item; optag: LONGINT);
    VAR s: PLL.Item;
  BEGIN
    CASE  optag OF
    | TasgnIncfn: Increment(x, y)
    | TasgnDecfn: Decrement(x, y)
    | TasgnInclfn:
        IF  y.mode=Imm  THEN  y.adr:=ASH(1, y.adr); y.typ:=PLT.linttyp; PLL.Op2(opImmEa+opRD, 80H, y, x)  (*ORI.L #2^y, x*)
        ELSE  s:=x; PLL.MultiRef(x); PLL.Op2(opLS+opLD+opRyRx, 1C0H, y, s); PLL.Move(s, x, Set); PLL.Release(x) END (*BSET*)
    | TasgnExclfn:
        IF  y.mode=Imm  THEN  y.adr:=-ASH(1, y.adr)-1; y.typ:=PLT.linttyp; PLL.Op2(opImmEa+opRD, 280H, y, x)  (*ANDI.L #~(2^y), x*)
        ELSE  s:=x; PLL.MultiRef(x); PLL.Op2(opLS+opLD+opRyRx, 180H, y, s); PLL.Move(s, x, Set); PLL.Release(x) END (*BCLR*)
    | TasgnCopyfn:  Copy(x, y)
    END
  END AStat;

  PROCEDURE NewArrMul(VAR x, y: PLL.Item);
  BEGIN
    IF  (x.mode=Imm)&(y.mode=Imm) THEN  x.adr:=x.adr*y.adr;
      IF  x.adr<=MaxSInt  THEN  x.typ:=PLT.sinttyp
      ELSIF x.adr<=MaxInt THEN  x.typ:=PLT.inttyp
      ELSE  x.typ:=PLT.linttyp  END
    ELSE  Mul(x, y)
    END
  END NewArrMul;

  PROCEDURE NewArrAdd(VAR x, y: PLL.Item);
  BEGIN
    IF  (x.mode=Imm)&(y.mode=Imm) THEN  x.adr:=x.adr+y.adr;
      IF  x.adr<=MaxSInt  THEN  x.typ:=PLT.sinttyp
      ELSIF x.adr<=MaxInt THEN  x.typ:=PLT.inttyp
      ELSE  x.typ:=PLT.linttyp  END
    ELSE  Add(x, y) END
  END NewArrAdd;

  PROCEDURE NewArrMulLen*(VAR y, len: PLL.Item; typ, typ0: PLT.Struct);
  BEGIN
    IF  len.mode=Pop  THEN  PLL.LoadD(len)
    ELSIF len.typ.form#LInt THEN  PLL.LoadD(len); PLL.OpW(48C0H+SHORT(len.adr)); len.typ:=PLT.linttyp END;
    PLL.MultiRef(len);
    IF  typ=typ0  THEN  y:=len;
      IF  y.mode=Dn THEN  PLL.GetD(y); PLL.Move(len, y, len.typ.form) END
    ELSE  NewArrMul(y, len) END
  END NewArrMulLen;

  PROCEDURE NewArr*(VAR x, y: PLL.Item; typ, typ0: PLT.Struct);
    VAR t, dummy: PLL.Item; regs: PLL.RegSet;
  BEGIN
    t.mode:=Imm; t.adr:=typ.BaseTyp.size; t.typ := PLT.linttyp; NewArrMul(y, t);
    t.adr:=typ0.n*8+4; NewArrAdd(y, t); PLL.Release(y);
    t:=x;
    PLL.SaveReg(regs);

    PLL.RefToA1(t);
    IF  (y.mode#Dn) OR (y.adr#0) OR (y.typ#PLT.linttyp) THEN  PLL.Move(y, D0, y.typ.form);
      IF  y.typ=PLT.sinttyp THEN  PLL.OpW(49C0H)  (*EXTB.L*)
      ELSIF y.typ=PLT.inttyp  THEN    PLL.OpW(48C0H)  (*EXT.L*) END
    END;
    PLL.OpL(206DFFF4H); PLL.OpW(4E90H); (*MOVEA.L -12(A5), A0; JSR (A0)*);

    dummy.typ:=PLT.notyp; PLL.RestoreReg(regs, dummy);
    PLL.LoadA(x); PLL.DeRef(x); y.mode:=Imm; y.adr:=typ.BaseTyp.size
  END NewArr;

  PROCEDURE NewArrSetLen*(VAR x, y, len: PLL.Item; typ, typ0: PLT.Struct);
    VAR t, len1: PLL.Item; disp: LONGINT;
  BEGIN
    disp:=typ.n*8-4;
    IF  disp>=0 THEN  x.disp:=disp; PLL.MultiRef(y); t:=y; PLL.Move(t, x, LInt) END;
    x.disp:=disp+4; PLL.MultiRef(len); t:=len;
    IF  t.mode=Dn THEN  PLL.GetD(len1); len1.typ:=t.typ; PLL.Move(t, len1, t.typ.form)  ELSE  len1:=t END;
    t.mode:=Imm; t.adr:=-1; t.typ:=PLT.linttyp; NewArrAdd(len1, t); PLL.Move(len1, x, LInt);
    IF  typ#typ0  THEN  NewArrMul(y, len) END
  END NewArrSetLen;



(*Addressing*)

  PROCEDURE Len(VAR x, len: PLL.Item; typ: PLT.Struct); (*len:=LEN(x, typ^.n)*)
  BEGIN len.typ:=PLT.linttyp; (* x.typ.comp=DynArr *)
    IF  (x.adr=FPR)OR(x.disp=0) THEN  PLL.LocalVar(len, x.alpha, x.descr+typ.tdadr, FALSE)
    ELSE  len:=x; len.mode:=RegInd; len.disp:=x.descr+typ.tdadr; PLL.MultiRef(len)  END
  END Len;

  PROCEDURE Size(VAR x, size: PLL.Item; typ: PLT.Struct); (*size:=SIZE(x), x of type typ*)
  BEGIN size.typ:=PLT.linttyp;
    IF  typ.comp#DynArr THEN  size.mode:=Imm; size.adr:=typ.size
    ELSIF (x.adr=FPR)OR(x.disp=0) THEN  PLL.LocalVar(size, x.alpha, x.descr+typ.tdadr+4, FALSE)
    ELSE  size:=x; size.mode:=RegInd; size.disp:=x.descr+typ.tdadr+4; PLL.MultiRef(size)  END
  END Size;

  PROCEDURE Field*(VAR x: PLL.Item; offset: LONGINT);
  BEGIN INC(x.disp, offset)
  END Field;

  PROCEDURE DeRef*(VAR x: PLL.Item);
    VAR btyp: PLT.Struct;
  BEGIN PLL.DeRef(x);
    IF  nilchk  THEN  PLL.Op1(opRx, 4A88H, x); PLL.OpL(57FA0002H) END;  (*TST.L Ax; TRAPEQ.W #2*)
    btyp:=x.typ.BaseTyp;
    IF  btyp.comp=DynArr  THEN  x.disp:=btyp.n*8+4; x.descr:=-4 END
  END DeRef;

  PROCEDURE Index*(VAR x, y: PLL.Item);
    VAR len, size: PLL.Item; artyp, eltyp: PLT.Struct; inxform, scale: INTEGER; arsize, elsize, nofel, inxreg: LONGINT; dynamic: BOOLEAN;

    PROCEDURE FindScale;
      VAR exp: INTEGER; log: LONGINT;
    BEGIN
      IF  (elsize=0) OR (elsize=1)  THEN  scale:=Half (*asl 0*)
      ELSIF elsize=2  THEN  scale:=Word (*asl 1*)
      ELSIF elsize=4  THEN  scale:=Long (*asl 2*)
      ELSIF elsize=8  THEN  scale:=Double (*asl 3*)
      ELSE  log:=elsize; exp:=0;
        WHILE ~ODD(log) DO  log:=log DIV 2; INC(exp)  END;
        IF  (log=1)&(exp<=11) THEN  scale:=-exp (*asl 4..11*) ELSE  scale:=Other (*mul*)  END
      END
    END FindScale;

    PROCEDURE MulSizeStatic;
      VAR expop: INTEGER;
    BEGIN
      IF  scale<0 THEN
        IF  scale=-11 THEN  x.beta:=Double; expop:=0
        ELSIF scale=-10 THEN  x.beta:=Long; expop:=0
        ELSIF scale=-9  THEN  x.beta:=Word; expop:=0
        ELSE  x.beta:=Half; expop:=((-scale) MOD 8)*200H  END;
        IF  (inxform=Int)&(arsize<8000H)  THEN  PLL.OpW(SHORT(inxreg+0E140H)+expop) (*ASL.W*)
        ELSE  PLL.OpW(SHORT(inxreg+0E180H)+expop) END (*ASL.L #exp, Dinxreg*)
      ELSIF scale=Other THEN  x.beta:=Half;
        IF  (nofel<8000H)&(elsize<8000H)  THEN  PLL.OpL(0C0FC0000H+inxreg*2000000H+(elsize MOD 10000H)) (*MULU WxW*)
        ELSE  PLL.OpL(4C3C0000H+inxreg*1000H); PLL.OpL(elsize)  END (*MULU.L #es, Dy*)
      ELSE  x.beta:=scale END
    END MulSizeStatic;

  BEGIN artyp:=x.typ; arsize:=artyp.size; nofel:=artyp.n; eltyp:=artyp.BaseTyp; elsize:=eltyp.size; inxform:=y.typ.form;
    IF  artyp.comp=Array  THEN
      IF  y.mode=Imm  THEN  INC(x.disp, y.adr*elsize)
      ELSE  FindScale;
        IF  (inxform=SInt) OR (inxform=Int)&((scale<0)&(arsize>=8000H)OR(elsize>=8000H))  THEN  PLL.LoadX(y)
        ELSE  PLL.LoadD(y)  END;
        inxreg:=y.adr;
        IF  inxchk  THEN
          IF  inxform#LInt  THEN
            IF  nofel >= 8000H  THEN  PLL.OpL(41BC7FFFH+inxreg*2000000H)  (*CHK.W #7FFFH*)
            ELSE  PLL.OpL(41BC0000H-1+inxreg*2000000H+nofel)  END (*CHK.W #bound, Dy*)
          ELSE  PLL.OpW(413CH+SHORT(inxreg)*200H); PLL.OpL(nofel-1) END (*CHK.L #bound, Dy*)
        END;
        IF  x.mode#RegInd THEN  PLL.Ref(x)  END;
        x.mode:=Indexed; x.inxreg:=SHORT(inxreg); MulSizeStatic;
        IF  (inxform#Int) OR (scale<0)&(arsize>=8000H) OR (scale=Other) THEN  x.code:=800H  ELSE  x.code:=0 END
      END
    ELSIF (y.mode#Imm)OR(y.adr#0) THEN
      IF  eltyp.comp#DynArr THEN  dynamic:=FALSE; FindScale ELSE  dynamic:=TRUE END;
      IF  dynamic OR inxchk OR (inxform=SInt) OR (inxform=Int)&((scale<0)OR(elsize>=8000H)) THEN  PLL.LoadX(y); y.typ:=PLT.linttyp
      ELSE  PLL.LoadD(y)  END;
      inxreg:=y.adr;
      IF  inxchk  THEN  Len(x, len, x.typ); PLL.Op2(opEaRn, 4100H, len, y)  (*CHK.L bounds, Dy*)  END;
      IF  x.mode#RegInd THEN  PLL.Ref(x)  END;
      x.mode:=Indexed; x.inxreg:=SHORT(inxreg);
      IF  dynamic THEN  Size(x, size, eltyp);
        PLL.Op2(opXLD+opEaRwLong, 4C000000H, size, y);  (*MULU.L size, Dy*)
        x.beta:=Half; x.code:=800H
      ELSE  MulSizeStatic;
        IF  (inxform#Int) OR (scale<0) OR (scale=Other) THEN  x.code:=800H  ELSE  x.code:=0 END
      END
    END
  END Index;


  PROCEDURE TypTest*(VAR x: PLL.Item; testtyp: PLT.Struct; guard, equal: BOOLEAN);
    VAR tag, tdes: PLL.Item;
  BEGIN
    IF  typchk OR ~guard  THEN
      IF  guard&equal THEN  tag.mode:=RegInd; tag.adr:=x.adr;
        IF  x.mode=MemInd THEN  tag.disp:=x.descr+4 ELSE  tag.disp:=-4  END;
        tdes.mode:=AbsRef; tdes.adr:=testtyp.tdadr;
        PLL.Op2(opImmEa, 0C80H, tdes, tag); PLL.OpL(56FA0013H)  (*CMPI.L #tdes, tag; TRAPNE.W #19*)
      ELSE
        IF  testtyp.comp=Record THEN  tag.mode:=RegInd; tag.adr:=x.adr; INC(PLL.register[Areg, tag.adr]); tag.disp:=x.descr+4
        ELSE  testtyp:=testtyp.BaseTyp; tag:=x; PLL.MultiRef(x); PLL.LoadA(tag);
          IF  nilchk  THEN  PLL.Op1(opRx, 4A88H, tag); PLL.OpL(57FA0002H) END;  (*TST.L Aptr; TRAPEQ.W #2*)
          tag.mode:=RegInd; tag.disp:=-4
        END;
        tdes.mode:=AbsRef; tdes.adr:=testtyp.tdadr;
        PLL.LoadA(tag); tag.mode:=RegInd; tag.disp:=4*testtyp.extlev+4; PLL.Op2(opImmEa+opRD, 0C80H, tdes, tag);  (*CMPI #tdes, tag*)
        IF  guard THEN  PLL.OpL(56FA0012H) (*TRAPNE.W #18*) ELSE  PLL.SetCC(x, ccEQ)  END
      END
    END
  END TypTest;


(*Statements*)

  PROCEDURE DynArrBnd(ap: PLL.Item; fp: PLT.Object);  (*Move Dynamic Array Size and Bound onto Stack*)
    VAR size, len: PLL.Item; ftyp, atyp: PLT.Struct;
  BEGIN ftyp:=fp.typ; atyp:=ap.typ;
    WHILE ftyp.comp=DynArr  DO  (* atyp.shape=Array, DynArr *)
      IF  (ftyp.BaseTyp=PLT.chartyp) & (atyp.comp#Array) & (atyp.comp#DynArr) THEN  len.typ:=PLT.linttyp; (*innermost dimension only*)
        IF  atyp.comp#DynArr  THEN  len.mode:=Imm; len.adr:=atyp.size-1
        ELSE
          (* PLL.LocalVar(len, ap.alpha, ap.descr+atyp.tdadr, FALSE); *)
          len.mode := RegInd; len.disp := ap.descr+atyp.tdadr; len.adr := ap.adr;
          IF  (atyp.BaseTyp.comp=DynArr)OR(atyp.BaseTyp.size#1) THEN
            PLL.Op1(opLD+opRx, 5280H, len); (* ADDQ #1, Dlen *)
            Size(ap, size, atyp.BaseTyp);
            PLL.Op2(opEaRwLong, 4C000000H, size, len);  (* MULU.L elsize, Dlen *)
            PLL.Op1(opRx, 5380H, len) (* SUBQ #1, Dlen *)
          END
        END;
        PLL.Push(len, LInt)
      ELSE  (* atyp.comp=Array, DynArr *)
        IF  atyp.comp=Array THEN  len.mode:=Imm; len.adr:=atyp.n-1
        ELSE  Len(ap, len, atyp)  END;
        PLL.Push(len, LInt);    (* Bound *)
        IF  ftyp.n > 0  THEN  Size(ap, size, atyp.BaseTyp); PLL.Push(size, LInt)  END
      END;
      ftyp:=ftyp.BaseTyp; atyp:=atyp.BaseTyp
    END
  END DynArrBnd;


  PROCEDURE Assign*(VAR x, y: PLL.Item);  (*Assign 'y' to 'x'*)
    VAR f, g: INTEGER;
  BEGIN g:=x.typ.form; f:=y.typ.form;
    IF  (f#g)&(g<=LReal)&(y.mode#Imm) THEN  Convert(y, f, g)  END;
    CASE  g OF
    | Bool: IF  y.mode=CCR  THEN  PLL.ResolveCC(y, x) ELSE  PLL.Move(y, x, Bool)  END
    | Char, SInt, Int, LInt, Set, NilTyp, Pointer, ProcTyp: PLL.Move(y, x, g)
    | Real, LReal:  PLL.FMove(y, x)
    | Comp: IF  f=String  THEN  PLL.BlkMove(y, x, y.beta) ELSIF x.typ.size>0 THEN PLL.BlkMove(y, x, x.typ.size) END
    END;
    PLL.Release(x)
  END Assign;

  PROCEDURE Param*(VAR ap: PLL.Item; fp: PLT.Object; class: LONGINT);
    VAR f, g: INTEGER; s: LONGINT; tag: PLL.Item;
  BEGIN f:=fp.typ.comp;
    IF  fp.mode=VarPar  THEN
      IF  f=DynArr  THEN  DynArrBnd(ap, fp)
      ELSIF f=Record  THEN
        IF  class=UvarparIndirect THEN  tag.mode:=RegInd; tag.adr:=ap.adr; tag.disp:=ap.descr+4; INC(PLL.register[Areg, ap.adr])
        ELSIF class=Tderef  THEN  tag.mode:=RegInd; tag.adr:=ap.adr; tag.disp:=-4; INC(PLL.register[Areg, ap.adr])  (*ap=p^, ap.mode=RegInd, ap.disp=0*)
        ELSE  tag.mode:=AbsRef; tag.adr:=ap.typ.tdadr END;
        PLL.Push(tag, LInt);
      END;
      PLL.RefToStk(ap)
    ELSIF f=DynArr  THEN
      IF  ap.typ.form=String  THEN  tag.mode:=Imm; tag.adr:=ap.beta-1; PLL.Push(tag, LInt)  ELSE  DynArrBnd(ap, fp) END;
      PLL.RefToStk(ap)
    ELSIF (fp.typ.size> 4)&(fp.typ.form#LReal)  THEN  PLL.RefToStk(ap)
    ELSE  g:=fp.typ.form; f:=ap.typ.form;
      IF  (ap.mode#Pop) OR (f#g)  THEN
        IF  (f#g)&(g<=LReal)&(fp.mode#Imm)  THEN  Convert(ap, f, g) END;
        CASE  g OF
        | Bool, Char, SInt, Int, LInt, Set, NilTyp, Pointer, ProcTyp: PLL.Push(ap, g)
        | Real, LReal:  PLL.FPush(ap, g)
        | Comp: s:=fp.typ.size;
            IF  s#0 THEN
              IF  s=1 THEN  PLL.Push(ap, SInt)  ELSIF s=2 THEN  PLL.Push(ap, Int) ELSE  PLL.Push(ap, LInt)  END
            END
        END
      END
    END
  END Param;


  PROCEDURE CopyDynArray*(adr: LONGINT; typ: PLT.Struct); (*D0, A0, A1*)
    VAR len, size: PLL.Item; baseTyp: PLT.Struct;
  BEGIN baseTyp:=typ.BaseTyp; PLL.LocalVar(len, PLL.level, adr+typ.tdadr, FALSE); PLL.Op1(opEa+opRD, 2000H, len); (*MOVE.L len, D0*)
    IF  (baseTyp.comp=DynArr)OR(baseTyp.size#1) THEN  PLL.OpW(5280H); (*ADDQ #1, D0*)
      IF  baseTyp.comp#DynArr THEN  size.mode:=Imm; size.adr:=baseTyp.size
      ELSE  PLL.LocalVar(size, PLL.level, adr+baseTyp.tdadr+4, FALSE) END;
      size.typ:=PLT.linttyp; PLL.Op1(opEaLong+opRD, 4C000000H, size); (*MULU.L elsize, D0*)
      PLL.OpW(5680H)  (* ADDQ.L #3, D0 *)
    ELSE  PLL.OpW(5880H)  (* ADDQ.L #4, D0 *) END;
    IF  inxchk  THEN  PLL.OpW(0C80H); PLL.OpL(7FFH); PLL.OpL(5AFA0018H) (*CMPI , TRAPPL #24*) END;
    PLL.OpL(024007FCH); PLL.OpW(0FFFF9EC0H); PLL.OpL(0E4485340H); (*ANDI.W #07FC, D0; SUBA.W D0, A7; LSR.W #2, D0; SUBQ.W #1, D0 *)
    PLL.OpL(206E0000H+adr); PLL.OpL(2D4F0000H+adr); PLL.OpW(224FH); (*MOVEA.L adr(A6), A0; MOVE.L A7, adr(A6); MOVEA.L A7, A1*)
    PLL.OpW(22D8H); PLL.OpL(51C8FFFCH)  (*MOVE.L (A0)+, (A1)+;  DBF.W D0, -4*)
  END CopyDynArray;

  PROCEDURE CopyPar*(adr: LONGINT; size: INTEGER);  (*D0, A0, A1*)
  BEGIN INC(size, (-size) MOD 4); PLL.ADDA(-size, 7);
    PLL.OpL(206E0000H+adr); PLL.OpL(2D4F0000H+adr); PLL.OpW(224FH); (*MOVEA.L adr(A6), A0; MOVE.L A7, adr(A6); MOVEA.L A7, A1*)
    IF  size<4*81H  THEN  PLL.OpW(7000H-1+(size DIV 4)) ELSE  PLL.OpL(303C0000H-1+(size DIV 4)) END;  (*MOVEQ/MOVE #size, D0*)
    PLL.OpW(22D8H); PLL.OpL(51C8FFFCH)  (*MOVE.L (A0)+, (A1)+;  DBF.W D0, -4*)
  END CopyPar;


(*Procedures*)

  PROCEDURE PrepTprocCall*(VAR ap: PLL.Item; class: LONGINT; VAR x: PLL.Item; super: BOOLEAN);
    VAR tag: PLL.Item; typ: PLT.Struct;
  BEGIN tag:=ap; PLL.MultiRef(ap);
    IF  super THEN  typ:=tag.typ.BaseTyp;
      IF  tag.typ.form=Pointer  THEN  typ:=typ.BaseTyp  END;
      PLL.Release(tag); tag.mode:=AbsRef; tag.adr:=typ.tdadr; tag.alpha:=typ.mno
    ELSIF ap.typ.form=Pointer THEN  DeRef(tag); DEC(tag.disp, 4)
    ELSIF class=Tderef  THEN  DEC(tag.disp, 4)
    ELSIF class=UvarparIndirect THEN  tag.mode:=RegInd; tag.disp:=tag.descr+4
    ELSE  PLL.Release(tag); tag.mode:=AbsRef; tag.adr:=tag.typ.tdadr; tag.alpha:=tag.typ.mno
    END;
    tag.typ := x.typ; PLL.LoadA(tag); tag.mode:=RegInd; tag.disp:=TprocOffset+x.adr*4; PLL.LoadA(tag); x := tag;
  END PrepTprocCall;

  PROCEDURE CallXProc*(VAR x: PLL.Item; proc: PLT.Object);
  BEGIN
    IF proc.mode=TProc THEN PLL.OpW(4E90H+SHORT(x.adr)); PLL.Release(x) (* JSR (Ax) *)
    ELSE PLL.OpW(4EB9H); PLL.OpL(proc.adr)  (*JSR (#absadr).L*)
    END
  END CallXProc;

  PROCEDURE CallLProc*(VAR x: PLL.Item; proc: PLT.Object);
  BEGIN
    IF proc.mode=TProc THEN PLL.OpW(4E90H+SHORT(x.adr)); PLL.Release(x) (* JSR (Ax) *)
    ELSE
      IF  proc.level>0  THEN  PLL.StaticLink(proc.level)  END;
      IF  proc.inited THEN  PLL.BsrBack(proc.fixlink) ELSE  PLL.BsrLink(proc.fixlink) END
    END
  END CallLProc;

  PROCEDURE CallPV*(VAR x: PLL.Item);
  BEGIN PLL.LoadA(x);
    IF  nilchk  THEN  PLL.Op1(opRx, 4A88H, x); PLL.OpL(57FA0002H) END;  (*TST.L Ax; TRAPEQ.W #2*)
    PLL.Op1(opRx+opRD, 4E90H, x); x.typ:=x.typ.BaseTyp  (*JSR (Ax)*)
  END CallPV;

  PROCEDURE EnterProc*(proc: PLT.Object);
    VAR dsize: LONGINT;
  BEGIN proc.inited:=TRUE; PLL.FixProc(proc.fixlink); dsize:=proc.dsize;  (*always a multiple of 4*)
    IF proc.mode # TProc THEN proc.adr:=PLL.codeBase+2*LONG(PLL.pc)
    ELSE proc.ival:=LONG(PLL.pc)
    END;
    PLL.OpL(4E560000H+((-dsize) MOD 10000H)); (*LINK.W A6, #dsize*)
    IF  ptrinit & (dsize > 0) THEN
      IF  dsize<4*81H THEN  PLL.OpW(7000H-1+SHORT(dsize DIV 4)) ELSE  PLL.OpL(303C0000H-1+(dsize DIV 4))  END;  (*MOVEQ/MOVE #k-1, D0*)
      PLL.OpL(204F4298H); PLL.OpL(51C8FFFCH)  (*MOVEA.L A7, A0; CLR.L (A0)+; DBF.W D0, -4*)
    END
  END EnterProc;

  PROCEDURE ReturnFromProc*(proc: PLT.Object; result: BOOLEAN; VAR res: PLL.Item);
    VAR x: PLL.Item; f: INTEGER; s: LONGINT;
  BEGIN
    IF  result  THEN  f:=proc.typ.form;
      IF  f IN realSet  THEN
        IF  (res.mode=Fn)&(res.adr=0) THEN  PLL.Release(res)  ELSE  PLL.FMove(res, F0)  END
      ELSE  x:=res; PLL.LocalVar(res, PLL.level, proc.psize, FALSE); res.typ:=proc.typ; Assign(res, x)  END
    END;
    PLL.OpW(4E5EH); (*UNLK A6*)
    IF  proc.psize=8  THEN  PLL.OpW(4E75H)  ELSE  PLL.OpL(4E740000H-8+proc.psize) END (*RTS/RTD*);

    IF  dbginfo THEN
      SYS.MOVE(SYS.ADR(proc.name[0]), SYS.ADR(s), 4); PLL.OpL(s);
      SYS.MOVE(SYS.ADR(proc.name[4]), SYS.ADR(s), 4); PLL.OpL(s)
    END;
    proc.lim:=PLL.codeBase+2*LONG(PLL.pc)
  END ReturnFromProc;

  PROCEDURE ReturnFromMod*;
  BEGIN PLL.OpW(4E75H)
  END ReturnFromMod;


  PROCEDURE Case*(VAR x: PLL.Item; VAR low: LONGINT; high: LONGINT; VAR tab: INTEGER; VAR Lb: PLL.Label);
    VAR f: INTEGER; y: PLL.Item; Lelse: PLL.Label;
  BEGIN f:=x.typ.form;
    IF  f IN {SInt, Char} THEN  PLL.LoadX(x); x.typ:=PLT.inttyp END;
    y.mode:=Imm; y.typ:=x.typ; Lelse:=0;
    IF  (low>=0)&(low<=14)  THEN  low:=0;
      IF  ~(f IN {SInt, Char})  THEN
        IF  x.mode IN {Absolute, RegInd, MemInd, Indexed} THEN  PLL.LoadD(x)
        ELSE  PLL.Op1(opLD+opRx+opSZ, 4A00H, x) END (*TST x*)
      END
    ELSE  y.adr:=low; PLL.Op2(opLD+opEaRn+opSZ, 9000H, y, x)  END;  (*SUB low, Dx*)
    IF  (f#Char)OR(low#0) THEN  PLL.BccLink(ccLT, Lelse)  END;  (*BLT else*)
    y.adr:=high-low; PLL.Op2(opLD+opImmEa+opSZ, 0C00H, y, x); PLL.BccLink(ccGT, Lelse); (*CMP diff, Dx; BGT else*)
    (*-8*)  PLL.Op1(opRwLong+opRD, 303B020AH, x); (*MOVE.W (CaseTable=10, PC, Dx.W*2), D0*)
    (*-4*)  PLL.OpL(4EFB0202H); (*JMP (CaseTable=2, PC, D0.W*2)*)
    (*-0*)  Lb:=PLL.pc; PLL.OpL(0FFFF0001H+high-low); (*Dummy Case Table Opcode*)
    PLL.AllocCaseTab(SHORT(high-low+1), tab); PLL.FixLink(Lelse); PLL.CaseJump(Lb, tab, 0, SHORT(high-low))
  END Case;

BEGIN D0.mode:=Dn; F0.mode:=Fn;
  cmpCC[TdopEql]:=ccEQ; cmpCC[TdopNeq]:=ccNE; cmpCC[TdopLss]:=ccLT; cmpCC[TdopLeq]:=ccLE; cmpCC[TdopGtr]:=ccGT; cmpCC[TdopGeq]:=ccGE;
  cmpCCX[TdopEql]:=ccEQ; cmpCCX[TdopNeq]:=ccNE; cmpCCX[TdopLss]:=ccCS; cmpCCX[TdopLeq]:=ccLS; cmpCCX[TdopGtr]:=ccHI; cmpCCX[TdopGeq]:=ccCC;
  cmpCCF[TdopEql]:=ccfEQ; cmpCCF[TdopNeq]:=ccfNE; cmpCCF[TdopLss]:=ccfLT; cmpCCF[TdopLeq]:=ccfLE; cmpCCF[TdopGtr]:=ccfGT; cmpCCF[TdopGeq]:=ccfGE;
  swapRel[TdopEql]:=TdopEql; swapRel[TdopNeq]:=TdopNeq; swapRel[TdopLss]:=TdopGtr; swapRel[TdopLeq]:=TdopGeq;
  swapRel[TdopGtr]:=TdopLss; swapRel[TdopGeq]:=TdopLeq; invRel[TdopEql]:=TdopNeq; invRel[TdopNeq]:=TdopEql;
  SYS.GETREG(13, newSys); SYS.GET(newSys-4, newSmall); SYS.GET(newSys-8, newLarge); SYS.GET(newSys-12, newSys)
END OPLC.