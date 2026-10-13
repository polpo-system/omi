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

MODULE OPLL;  (*mf 4.11.94 / tk object model 1.7.96 *)

  (* 1.7.96 Method support (mfix) *)

IMPORT
  SYS:=SYSTEM, Kernel, PLT:=OPLT;

CONST
  Var=1; Par=2; VarPar=3; Fld=5; LProc=6; XProc=7; TypDynArr=8; TypArray=9; TypPointer=10; TypRecord=11; TypProcTyp=12;
  TProc=14;
  Undef=0; Byte=1; Bool=2; Char=3; SInt=4; Int=5; LInt=6; Real=7; LReal=8; Set=9; String=10; NilTyp=11;
  Pointer=13; ProcTyp=14; Comp=15; Array=2; DynArr=3; Record=4;

  (*Data Sizes*)  Half=0; Word=1; Long=2; Double=3;
  (*Register Types*)  Dreg=0; Areg=1; Freg=2; FPR=6;
  (*Constant Values*) false=0; true=-1;
  (*Condition Codes*) ccT=0; ccNE=6; ccEQ=7; ccfGT=-18;
  (*Item Modes*)  Dn=14; An=15; Fn=16; RegInd=17; MemInd=18; Indexed=19; Pop=20; Absolute=21; AbsRef=22; Imm=23; CCR=24; Inval=0;
  (*OPx Modifiers*) bitSZ=14; bitKS=13; bitRD=12; bitLS=11; bitXLS=10; bitLD=8; bitXLD=7;
  (*Op1 Formats*) opNOP1=5; opRx=6; opRxLong=7; opRy=8; opRyLong=9; opEa=10;
  (*Op1 Formats*) opEaLong=11; opRwLong=12; opRzRz=13; opRzRzLong=14;
  (*Op2 Formats*) opNOP2=16; opRyRx=17; opRxRy=18; opEaRn=19; opRnEa=20; opImmEa=21; opEaRwLong=22; opRwEaLong=23;
  (*Implementation Restriction*)  MaxExts=16;
  (*OPL Type Descriptor*) TprocOffset=4+MaxExts*4+64; (* size, 16 extensions, module, name *)


TYPE
  Label*=INTEGER;

  Item*=RECORD
    mode*, inxreg*: INTEGER;
    typ*: PLT.Struct; adr*, disp*, descr*: LONGINT;
    alpha*, beta*, code*: INTEGER
  END;

  RegSet*=ARRAY 3 OF ARRAY 8 OF SHORTINT;
  BlkPtr=POINTER- TO ARRAY 32767 OF INTEGER;


VAR
  (*Backend Globals*) level*: SHORTINT; mRg: LONGINT; register*: RegSet;
  (*Code Array and Program Counter*)  code, data: BlkPtr; codeBase*: LONGINT; pc*, cp*, copied*: INTEGER;
  (*Fixup of Procedure Assignments*)  fixProc*: PLT.Object;
  (*Data Size Code by Form*)  sizeCode: ARRAY 16 OF INTEGER;
  (*Instruction Lookup by Form*)  mvInstr, fmtInstr, szInstr: ARRAY 16 OF INTEGER; szInstrL: ARRAY 16 OF LONGINT;
  nofrecs: INTEGER; recs: ARRAY 256 OF PLT.Struct;

(*Addressing*)

  PROCEDURE ^ AllocParam(proc: PLT.Object);

  PROCEDURE TypSize*(typ: PLT.Struct);
    VAR f, c, nofptr: INTEGER; btyp: PLT.Struct; fld: PLT.Object; offset, size: LONGINT;
  BEGIN
    IF  typ.size<0  THEN  f:=typ.form; c:=typ.comp; btyp:=typ.BaseTyp;
      IF  c=Record  THEN  fld:=typ.dsc;
        IF  btyp=NIL  THEN  nofptr:=0; offset:=0
        ELSE  TypSize(btyp); typ.extlev:=btyp.extlev+1; nofptr:=btyp.nofptr; offset:=btyp.size  END;
        typ.size := 0;
        WHILE (fld#NIL) & (fld.mode=Fld)  DO  btyp:=fld.typ; TypSize(btyp); size:=btyp.size;
          IF  size>1  THEN  INC(offset, offset MOD 2) END;
          fld.adr:=offset; INC(offset, size); INC(nofptr, btyp.nofptr); fld:=fld.nxtobj
        END;
        WHILE fld#NIL DO  (* Methods / mfix *)
          AllocParam(fld);
          fld := fld.nxtobj;
        END;
        INC(offset, offset MOD 2); typ.size:=offset; typ.nofptr:=nofptr
      ELSIF f=Pointer THEN  typ.size:=4; typ.nofptr:=1
      ELSIF c=Array THEN  TypSize(btyp); typ.size:=typ.n*btyp.size; typ.nofptr:=SHORT(typ.n*btyp.nofptr)
      ELSIF f=ProcTyp THEN  typ.size:=4
      ELSE  (*c=DynArr*)
        IF  btyp.comp=DynArr  THEN  typ.n:=btyp.n+1 END;
        typ.size:=8*typ.n+8; typ.tdadr:=8*typ.n+4;
      END
    END
  END TypSize;

  PROCEDURE AllocTypDesc(typ: PLT.Struct);
    VAR fld: PLT.Object; btyp: PLT.Struct; W, copy, s: LONGINT; i: INTEGER;

    PROCEDURE FindPtrs(typ: PLT.Struct; adr: LONGINT);
      VAR fld: PLT.Object; btyp: PLT.Struct; i, n: LONGINT;
    BEGIN
      IF  typ.nofptr > 0  THEN
        IF  typ.form=Pointer  THEN  SYS.PUT(W, adr); INC(W, 4)
        ELSIF typ.comp=Record THEN  btyp:=typ.BaseTyp; fld:=typ.dsc;
          IF  btyp#NIL  THEN  FindPtrs(btyp, adr) END;
          WHILE (fld#NIL) & (fld.mode#TProc)  DO  FindPtrs(fld.typ, fld.adr+adr); fld:=fld.nxtobj END
        ELSIF typ.comp=Array  THEN  btyp:=typ.BaseTyp; n:=typ.n; i:=0;
          WHILE i < n DO  FindPtrs(btyp, adr); INC(adr, btyp.size); INC(i)  END
        END
      END
    END FindPtrs;

  BEGIN
    IF  typ.tdadr=0 THEN  btyp:=typ.BaseTyp; fld:=typ.dsc;
      IF  btyp#NIL  THEN  AllocTypDesc(btyp)  END;  (*never a cycle*)
      recs[nofrecs] := typ; INC(nofrecs);
      IF  ODD(cp) THEN  INC(cp) END;
      W:=SYS.ADR(data[cp]);
      SYS.PUT(W, LONG(-4*typ.nofptr-4)); INC(W, 4);
      IF  (btyp#NIL)&(btyp.nofptr>0)  THEN  copy:=btyp.nofptr*4; SYS.MOVE(btyp.tdadr-copy, W, copy); INC(W, copy) END;
      WHILE (fld#NIL) & (fld.mode#TProc)  DO  FindPtrs(fld.typ, fld.adr); fld:=fld.nxtobj END;
      typ.tdadr:=W; s:=typ.size+4;
      IF  s <=128 THEN  INC(s, (-s) MOD 16); s:=s DIV 4 ELSE  INC(s, ((-s) MOD 4)+4)  END;
      SYS.PUT(W, s); INC(W, 4);
      IF  btyp=NIL  THEN  SYS.PUT(W, typ.tdadr); INC(W, 4); i:=MaxExts;
        WHILE i > 0 DO  SYS.PUT(W-4+4*i, LONG(LONG(0))); DEC(i) END
      ELSE  SYS.MOVE(btyp.tdadr+4, W, 4*(MaxExts+1)); SYS.PUT(W+4*typ.extlev, typ.tdadr)  END;
      INC(W, 4*(MaxExts+1));  (* mfix *)
      INC(W, 64); (* modulename, typename *)
      i := SHORT(typ.n); WHILE i > 0 DO SYS.PUT(W, LONG(LONG(0))); INC(W, 4); DEC(i) END;
      INC(cp, 2+typ.nofptr*2+2+(MaxExts+1)*2+32+SHORT(typ.n)*2);
    END
  END AllocTypDesc;

  PROCEDURE AllocGlobalVar*(globals: PLT.Object; VAR dadr: LONGINT);
    VAR adr, size, base, dsize: LONGINT; nofptr: INTEGER; obj, var, list: PLT.Object; desc: PLT.Struct;
  BEGIN adr:=0; nofptr:=0; obj:=globals; list:=NIL;
    WHILE obj#NIL DO
      IF  obj.mode=Var  THEN  size:=obj.typ.size; INC(nofptr, obj.typ.nofptr);
        IF  size>=4 THEN  INC(adr, (-adr) MOD 4)  ELSIF size=2  THEN  INC(adr, adr MOD 2) END;
        NEW(var); var.adr:=adr; var.typ:=obj.typ; var.nxtobj:=list; list:=var;
        obj.adr:=adr; INC(adr, size)
      END;
      obj:=obj.nxtobj
    END;
    INC(adr, adr MOD 4); dsize:=adr;
    NEW(desc); desc.form:=Comp; desc.comp:=Record; desc.nofptr:=nofptr; desc.size:=dsize; desc.dsc:=list; AllocTypDesc(desc);
    Kernel.AllocBlock(base, -(adr+4)); SYS.PUT(base, desc.tdadr+1); (*pretend marked*) INC(base, 4); dadr:=base;
    obj:=globals;
    WHILE obj#NIL DO
      IF  obj.mode=Var  THEN  INC(obj.adr, base)  END;
      obj:=obj.nxtobj
    END
  END AllocGlobalVar;

  PROCEDURE AllocLocalVar*(var, proc: PLT.Object);
    VAR adr, size: LONGINT;
  BEGIN adr:=0;
    WHILE var#NIL DO
      IF  (var.mode=Var)  THEN  size:=var.typ.size;
        IF  size > 2  THEN  DEC(adr, adr MOD 4) ELSIF size=2  THEN  DEC(adr, adr MOD 2) END;
        DEC(adr, size); var.adr:=adr; var.level:=proc.level+1
      END;
      var:=var.nxtobj
    END;
    DEC(adr, adr MOD 4); proc.dsize:=-adr
  END AllocLocalVar;

  PROCEDURE AllocParam(proc: PLT.Object);
    VAR par: PLT.Object; typ: PLT.Struct; adr, size: LONGINT;
  BEGIN adr:=0; par:=proc.par;
    WHILE par#NIL DO  typ:=par.typ;
      TypSize(typ);
      IF  typ.comp=DynArr THEN  size:=typ.size
      ELSIF par.mode=VarPar THEN
        IF  typ.comp=Record THEN  size:=8 ELSE  size:=4 END
      ELSE  size:=typ.size;
        IF  typ.form=LReal  THEN  size:=8 ELSIF size > 4  THEN  size:=4 ELSIF size=1  THEN  size:=2 END
      END;
      INC(adr, size); par.adr:=adr; par.level:=proc.level+1; par:=par.nxtobj
    END;
    IF  proc.level > 0  THEN  proc.psize:=adr+12  ELSE  proc.psize:=adr+8 END;
    par:=proc.par;
    WHILE par#NIL DO  par.adr:=proc.psize-par.adr; par:=par.nxtobj  END
  END AllocParam;

  PROCEDURE Traverse*(obj: PLT.Object);
    VAR typ: PLT.Struct; tobj: PLT.Object;
  BEGIN tobj:=obj;
    (* calculate type sizes *)
    WHILE tobj#NIL  DO
      IF  tobj.mode IN {TypDynArr, TypArray, TypProcTyp, TypPointer, TypRecord, TypProcTyp} THEN  TypSize(tobj.typ) END;
      tobj:=tobj.nxtobj
    END;
    (* calculate addresses *)
    WHILE obj#NIL DO  typ:=obj.typ;
      CASE  obj.mode  OF
      | TypDynArr:  typ.tdadr:=8*typ.n+4
      | TypRecord:  AllocTypDesc(typ)
      | LProc, XProc: AllocParam(obj)
      ELSE
      END;
      obj:=obj.nxtobj
    END
  END Traverse;


(*Byte Arrays and Entry Numbers*)

  PROCEDURE OpW*(w: INTEGER);
  BEGIN code[pc]:=w; INC(pc)
  END OpW;

  PROCEDURE OpL*(l: LONGINT);
  BEGIN SYS.PUT(SYS.ADR(code[pc]), l); INC(pc, 2)
  END OpL;

  PROCEDURE CopyCode*(from, to: Label);
    VAR n: INTEGER;
  BEGIN n:=2*(to-from);
    IF  n>0 THEN  SYS.MOVE(SYS.ADR(code[from]), SYS.ADR(code[pc]), n); INC(pc, n DIV 2); INC(copied, n) END
  END CopyCode;

  PROCEDURE AllocCaseTab*(n: INTEGER; VAR tab: INTEGER);
  BEGIN tab:=pc; INC(pc, n)
  END AllocCaseTab;

  PROCEDURE CaseJump*(L: Label; tab, from, to: INTEGER);  (*jump table in word offsets*)
    VAR i, j: LONGINT; jump: INTEGER;
  BEGIN i:=tab+from; j:=tab+to; jump:=pc-L;
    WHILE i<=j  DO  code[i]:=jump; INC(i) END
  END CaseJump;

  PROCEDURE AllocString*(VAR s: ARRAY OF CHAR; len: INTEGER; VAR adr: LONGINT);
  BEGIN adr:=SYS.ADR(data[cp]); SYS.MOVE(SYS.ADR(s[0]), adr, len); INC(cp, (len+1) DIV 2)
  END AllocString;


(*Relative Branches*)

  PROCEDURE Fixup*(loc: Label);
  BEGIN code[loc]:=2*(pc-loc)
  END Fixup;

  PROCEDURE FixLink*(loc: Label);
    VAR tmp: INTEGER;
  BEGIN WHILE loc#0 DO  tmp:=code[loc]; code[loc]:=2*(pc-loc); loc:=tmp END
  END FixLink;

  PROCEDURE FixLinkWith(loc, withloc: Label);
    VAR tmp: INTEGER;
  BEGIN WHILE loc#0 DO  tmp:=code[loc]; code[loc]:=2*(withloc-loc); loc:=tmp  END
  END FixLinkWith;

  PROCEDURE MergedLinks*(loc0, loc1: Label): Label;
    VAR loc2, adr: INTEGER;
  BEGIN
    IF  loc0#0  THEN  loc2:=loc0;
      LOOP  adr:=code[loc2];
        IF  adr=0 THEN  EXIT  ELSE  loc2:=adr END
      END;
      code[loc2]:=loc1; RETURN loc0
    ELSE  RETURN loc1 END
  END MergedLinks;


(*Condition Codes*)

  PROCEDURE ^ MRG(VAR x: Item);
  PROCEDURE ^ XTN(VAR x: Item);
  PROCEDURE ^ MultiRef*(VAR x: Item);
  PROCEDURE ^ Release*(VAR x: Item);
  PROCEDURE ^ Op1*(fmt: INTEGER; op: LONGINT; VAR dest: Item);
  PROCEDURE ^ Op2*(fmt: INTEGER; op: LONGINT; VAR src, dest: Item);

  PROCEDURE BccLink*(cond: INTEGER; VAR L: Label);
  BEGIN
    IF  cond < 0  THEN  OpL(-0D800000H-cond*10000H+L) ELSE  OpL(60000000H+cond*1000000H+L)  END;
    L:=pc-1
  END BccLink;

  PROCEDURE BccBack(cond: INTEGER; L: Label);
    VAR disp: INTEGER;
  BEGIN disp:=2*(L-pc-1);
    IF  cond < 0  THEN  OpL(-0D800000H-cond*10000H+(disp MOD 10000H))
    ELSIF disp>=-127  THEN  OpW(6000H+cond*100H+(disp MOD 100H))
    ELSE  OpL(60000000H+cond*1000000H+(disp MOD 10000H))  END
  END BccBack;

  PROCEDURE InvertCC*(cond: INTEGER): INTEGER;
  BEGIN
    IF  cond < 0  THEN
      IF  cond > ccfGT  THEN  RETURN-15-cond  ELSE  RETURN-47-cond  END
    ELSIF ODD(cond) THEN  RETURN cond-1 ELSE  RETURN cond+1 END
  END InvertCC;

  PROCEDURE SetCC*(VAR x: Item; cond: INTEGER);
  BEGIN Release(x); x.typ:=PLT.booltyp; x.mode:=CCR; x.code:=cond; x.alpha:=0; x.beta:=0
  END SetCC;

  PROCEDURE LoadCC*(VAR x: Item); (*Load into CCR*)
  BEGIN MRG(x); OpW(4A00H+SHORT(mRg)); XTN(x); Release(x); x.mode:=CCR; x.code:=ccNE; x.alpha:=0; x.beta:=0 (*TST.B*)
  END LoadCC;

  PROCEDURE ResolveCC*(VAR cnd, dest: Item);  (*Move CCR into Destination*)
    VAR L: Label; dest2: Item;
  BEGIN
    IF  (cnd.alpha=0)&(cnd.beta=0)  THEN  (*No Tjmp or Fjmp Pending*)
      IF  cnd.code < 0  THEN  Op1(opEaLong, 0F2400000H-cnd.code, dest)  (*FScc.B cond, dest*)
      ELSE  MRG(dest); OpW(50C0H+SHORT(mRg+cnd.code*100H)); XTN(dest) END (*Scc.B cond, dest*)
    ELSE  dest2:=dest; MultiRef(dest);
      IF  cnd.code#ccT  THEN  BccLink(InvertCC(cnd.code), cnd.beta) END;  (*B~cond Fjmp*)
      FixLink(cnd.alpha); MRG(dest); OpW(50C0H+SHORT(mRg)); XTN(dest);
      L:=0; BccLink(ccT, L); FixLink(cnd.beta); (*Tjmp: ST.B dest; BRA continue*)
      MRG(dest2); OpW(4200H+SHORT(mRg)); XTN(dest2); Release(dest2);  (*Fjmp: CLR.B dest2*)
      Fixup(L)  (*Continue Here*)
    END
  END ResolveCC;

  PROCEDURE TrapCC*(VAR cnd: Item; n: LONGINT); (*Assert Trap*)
  BEGIN
    IF  (cnd.alpha=0)&(cnd.beta=0)&(cnd.code>=0)  THEN  OpL(50FA0000H+LONG(cnd.code)*1000000H+n)  (*TPcc.W #n*)
    ELSE
      IF  cnd.code#ccT  THEN  BccLink(InvertCC(cnd.code), cnd.beta) END;  (*B~cond Fjmp*)
      FixLink(cnd.alpha); OpL(50FA0000H+n); FixLink(cnd.beta) (*Tjmp: ST.B dest; TPT.W #n; Fjmp: Continue*)
    END
  END TrapCC;


(*Control*)

  PROCEDURE FJ*(VAR loc: Label);
  BEGIN OpL(60000000H+loc); loc:=pc-1
  END FJ;

  PROCEDURE BJ*(loc: Label);
    VAR disp: INTEGER;
  BEGIN disp:=2*(loc-pc-1);
    IF  disp>=-127  THEN  OpW(6000H+(disp MOD 100H))  ELSE  OpL(60000000H+(disp MOD 10000H))  END
  END BJ;

  PROCEDURE CFJ*(VAR x: Item; VAR loc: Label);  (*On False - used in IF and WHILE*)
  BEGIN
    IF  x.mode=CCR  THEN  (*No Branch Necessary on True*)
      IF  x.code=ccT  THEN  loc:=0  ELSE  loc:=x.beta; BccLink(InvertCC(x.code), loc) (*B~cond Fjmp*) END;
      FixLink(x.alpha)  (*Tjmp here*)
    ELSIF x.mode=Imm  THEN  loc:=0;
      IF  x.adr=false THEN  BccLink(ccT, loc) (*BRA Fjmp*)  END
    ELSE  (*form=Bool, expr=varRef*)  LoadCC(x); loc:=0; BccLink(ccEQ, loc) END (*BEQ Fjmp*)
  END CFJ;

  PROCEDURE CBJ*(VAR x: Item; loc: Label);  (*On False - used in REPEAT*)
  BEGIN
    IF  x.mode=CCR  THEN  (*No Branch Necessary on True*)
      IF  x.code#ccT  THEN  BccBack(InvertCC(x.code), loc)  END;  (*B~cond loc*)
      FixLinkWith(x.beta, loc); FixLink(x.alpha)  (*Fjmp loc, Tjmp here*)
    ELSIF x.mode#Imm  THEN  LoadCC(x); BccBack(ccEQ, loc) (*form=Bool, expr=varRef*)
    ELSIF x.adr=false THEN  BccBack(ccT, loc) END (*BRA loc*)
  END CBJ;


(*Procedures*)

  PROCEDURE ^ AllocA(VAR n: LONGINT);

  PROCEDURE StaticLink*(lev: SHORTINT);
    VAR areg: LONGINT; ldiff: SHORTINT;
  BEGIN ldiff:=level-lev;
    IF  ldiff=0 THEN  OpW(2F0EH)  (*MOVE.L FP, -(A7)*)
    ELSIF ldiff=1 THEN  OpL(2F2E0008H)  (*MOVE.L (d16=SLadr, FP), -(A7)*)
    ELSE  AllocA(areg); OpL(206E0008H+areg*2000000H); (*MOVEA.L (lnk, FP), Ax*)
      WHILE ldiff>2 DO  DEC(ldiff); OpL(20680008H+areg*2000000H+areg*10000H)  END;  (*MOVEA.L (lnk, Ax), Ax*)
      OpL(2F280008H+areg*10000H); DEC(register[Areg, areg]) (*MOVE.L (lnk, Ax), -(A7)*)
    END
  END StaticLink;

  PROCEDURE BsrBack*(L: Label);
    VAR disp: INTEGER;
  BEGIN disp:=L-pc-1; (*in words*)
    IF  disp>-64  THEN  OpW(6100H+((2*disp) MOD 100H))
    ELSIF disp>=-16384  THEN  OpL(61000000H+((2*LONG(disp)) MOD 10000H))
    ELSE  OpW(61FFH); OpL(2*LONG(disp)) END
  END BsrBack;

  PROCEDURE BsrLink*(VAR L: Label);
  BEGIN OpL(61FF0000H); OpW(L); L:=pc-2 (*BSR.L*)
  END BsrLink;

  PROCEDURE AbsLink(VAR L: Label);
  BEGIN OpW(0001H); OpW(L); L:=pc-2
  END AbsLink;

  PROCEDURE FixProc*(VAR adr: Label);
    VAR loc, tmp, type: INTEGER; absAdr: LONGINT;
  BEGIN loc:=adr; adr:=pc;
    WHILE loc#0 DO
      type:=code[loc]; tmp:=code[loc+1];
      IF  type=0  THEN  code[loc+1]:=2*(pc-loc)
      ELSE  absAdr:=codeBase+2*LONG(pc); code[loc]:=SHORT(absAdr DIV 10000H); code[loc+1]:=SHORT(absAdr MOD 10000H)
      END;
      loc:=tmp
    END;  (*!*)
  END FixProc;

(*Register Reservation*)

  PROCEDURE AllocA(VAR n: LONGINT);
    VAR i: INTEGER;
  BEGIN i:=4;
    LOOP
      IF  register[Areg, i]=0 THEN  n:=i; register[Areg, i]:=1; RETURN  ELSE  DEC(i)  END
    END
  END AllocA;

  PROCEDURE GetA(VAR x: Item);
  BEGIN x.mode:=An; AllocA(x.adr)
  END GetA;

  PROCEDURE GetD*(VAR x: Item);
    VAR i: INTEGER;
  BEGIN x.mode:=Dn; i:=7;
    LOOP
      IF  register[Dreg, i]=0 THEN  x.adr:=i; register[Dreg, i]:=1; RETURN  ELSE  DEC(i)  END
    END
  END GetD;

  PROCEDURE GetF(VAR x: Item);
    VAR i: INTEGER;
  BEGIN x.mode:=Fn; i:=7;
    LOOP
      IF  register[Freg, i]=0 THEN  x.adr:=i; register[Freg, i]:=1; RETURN  ELSE  DEC(i)  END
    END
  END GetF;

  PROCEDURE MultiRef*(VAR x: Item);
  BEGIN
    IF  x.mode=Dn THEN  INC(register[Dreg, x.adr])
    ELSIF x.mode IN {An, RegInd, MemInd, Indexed} THEN  INC(register[Areg, x.adr]);
      IF  x.mode=Indexed  THEN  INC(register[Dreg, x.inxreg]) END
    ELSIF x.mode=Fn THEN  INC(register[Freg, x.adr])  END
  END MultiRef;

  PROCEDURE Release*(VAR x: Item);
  BEGIN
    IF  x.mode=Dn THEN  DEC(register[Dreg, x.adr])
    ELSIF x.mode IN {An, RegInd, MemInd, Indexed} THEN  DEC(register[Areg, x.adr]);
      IF  x.mode=Indexed  THEN  DEC(register[Dreg, x.inxreg]) END
    ELSIF x.mode=Fn THEN  DEC(register[Freg, x.adr])  END
  END Release;

  PROCEDURE RefTProc*(VAR x: Item; tadr: Label);
    VAR disp: LONGINT;
  BEGIN GetA(x); disp:=2*LONG(tadr-pc-1); OpL(41FB0170H+x.adr*2000000H); OpL(disp)
  END RefTProc;

(*Address Generation*)

  PROCEDURE MRG(VAR x: Item); (*Mode-Register-Code*)
    VAR reg, adr, disp: LONGINT;
  BEGIN adr:=x.adr;
    CASE  x.mode  OF
    | Dn: mRg:=adr
    | An: mRg:=8H+adr
    | RegInd: disp:=x.disp; (*disp>=-8000H*)
        IF  disp=0  THEN  mRg:=10H+adr  ELSIF disp<8000H  THEN  mRg:=28H+adr  ELSE  mRg:=30H+adr  END
    | MemInd: disp:=x.disp; DEC(register[Areg, adr]); AllocA(reg); x.mode:=RegInd; x.adr:=reg;  (*disp>-8000H*)
        OpL(20680000H+reg*2000000H+adr*10000H+(x.descr MOD 10000H));  (*MOVEA.L adr(Ax), Areg*)
        IF  disp=0  THEN  mRg:=10H+reg  ELSIF disp<8000H  THEN  mRg:=28H+reg  ELSE  mRg:=30H+reg  END
    | Indexed:  mRg:=30H+adr; (*x.disp>=-8000H*)
    | Absolute: mRg:=39H
    | AbsRef, Imm:  mRg:=3CH
    | Pop:  mRg:=1FH
    END
  END MRG;

  PROCEDURE XTN(VAR x: Item); (*Address Extension*)
    VAR inx: INTEGER; disp: LONGINT;
  BEGIN
    CASE  x.mode  OF
    | Dn, An, Pop:
    | RegInd: disp:=x.disp;
        IF  disp#0  THEN
          IF  disp<8000H  THEN  OpW(SHORT(disp))  ELSE  OpW(170H); OpL(disp)  END
        END
    | Indexed:  disp:=x.disp; inx:=x.inxreg*1000H+x.beta*200H+x.code;
        IF  (disp>=-80H)&(disp<80H) THEN  OpW(inx+SHORT(disp) MOD 100H)
        ELSIF disp<8000H  THEN  OpL(1200000H+inx*10000H+(disp MOD 10000H))
        ELSE  OpW(inx+130H); OpL(disp)
        END
    | Absolute: OpL(x.adr+x.disp)
    | AbsRef: OpL(x.adr)
    | Imm:
        CASE  x.typ.form  OF
        | NilTyp: OpL(0)
        | Byte, Bool, Char, SInt, Int, String, Comp:  OpW(SHORT(x.adr))
        | LInt, Real, Set, ProcTyp, Pointer:  OpL(x.adr)
        | LReal:  OpL(x.adr); OpL(x.disp)
        END
    END
  END XTN;


(*Primitives*)

  PROCEDURE ^ Ref*(VAR x: Item);

  PROCEDURE Move*(VAR src, dest: Item; f: INTEGER);
    VAR val, dmRg: LONGINT;
  BEGIN
    IF  src.mode=Imm  THEN  val:=src.adr;
      IF  val=0 THEN
        IF  dest.mode=An  THEN  OpW(SHORT(91C8H+dest.adr*200H+dest.adr))  (*SUBA.L*)
        ELSE  MRG(dest); OpW(4200H+SHORT(mRg)+szInstr[f]); XTN(dest)  END (*CLR*)
      ELSIF (dest.mode=Dn)&(val>=-80H)&(val<80H)  THEN  OpW(7000H+SHORT(dest.adr)*200H+(SHORT(val) MOD 100H)) (*MOVEQ.L*)
      ELSIF (val=true)&(f=Bool) THEN  MRG(dest); OpW(50C0H+SHORT(mRg)); XTN(dest) (*ST.B*)
      ELSE  MRG(dest); OpW((SHORT(mRg) MOD 8)*200H+(SHORT(mRg) DIV 8)*40H+3CH+mvInstr[f]);
        CASE  f OF
        | Byte, Bool, Char, SInt, Int:  OpW(SHORT(val))
        | LInt, Real, Set, ProcTyp, Pointer:  OpL(val)
        END;
        XTN(dest)
      END
    ELSE
      MRG(dest); dmRg:=mRg; MRG(src);
      OpW(mvInstr[f]+SHORT(mRg+(dmRg MOD 8)*200H+(dmRg DIV 8)*40H));
      IF  (f=ProcTyp)&(src.adr=0)&(src.mode=AbsRef) THEN  AbsLink(fixProc.fixlink); fixProc:=NIL;
      ELSE  XTN(src)
      END;
      XTN(dest); Release(src);
    END
  END Move;

  PROCEDURE nMove*(rMMr: INTEGER; n: LONGINT);
    VAR k: LONGINT;
  BEGIN
    IF  n<=16 THEN
      WHILE n>3 DO  OpW(20D8H+rMMr); DEC(n, 4)  END (*MOVE.L (As)+, (Ad)+*)
    ELSE  k:=n DIV 4;
      IF  k<10000H  THEN
        IF  k<81H THEN  OpW(7000H-1+SHORT(k)) ELSE  OpL(303C0000H-1+k)  END;  (*MOVEQ/MOVE #k-1, D0*)
        OpW(20D8H+rMMr); OpL(51C8FFFCH) (*MOVE.L (As)+, (Ad)+;  DBF.W D0, -4*)
      ELSE  OpW(203CH); OpL(k); OpW(20D8H+rMMr); OpL(538066FAH) (*MOVE.L #k, D0; MOVE.L (As)+, (Ad)+;  SUBQ #1, D0;  BNE -6*)
      END
    END;
    IF  (n MOD 4)#0 THEN
      IF  (n MOD 4)=1 THEN  OpW(1090H+rMMr) (*MOVE.B (As), (Ad)*)
      ELSIF (n MOD 4)=2 THEN  OpW(3090H+rMMr) (*MOVE.W (As), (Ad)*)
      ELSE  OpL(30D81090H+rMMr*10000H+rMMr) END (*MOVE.W (As)+, (Ad)+;  MOVE.B (As), (Ad)*)
    END
  END nMove;

  PROCEDURE BlkMove*(VAR src, dest: Item; n: LONGINT);
    VAR rMMr, dmRg: INTEGER;
  BEGIN (*n>0*)
    IF  (n<=4)&(n#3)  THEN  MRG(dest); dmRg:=SHORT(mRg); MRG(src); rMMr:=SHORT(mRg)+(dmRg MOD 8)*200H+(dmRg DIV 8)*40H;
      IF  n=4 THEN  OpW(2000H+rMMr) ELSIF n=2 THEN  OpW(3000H+rMMr) ELSE  OpW(1000H+rMMr) END;
      XTN(src); XTN(dest); Release(src)
    ELSE  Ref(src); Ref(dest); nMove(SHORT(dest.adr*200H+src.adr), n); Release(src) END
  END BlkMove;

  PROCEDURE FMove*(VAR src, dest: Item);
    VAR dMrg: INTEGER;
  BEGIN
    IF  dest.mode=Fn  THEN
      IF  src.mode=Fn THEN  OpL(0F2000000H+src.adr*400H+dest.adr*80H); Release(src)
      ELSE  MRG(src); OpL(0F2004000H+mRg*10000H+fmtInstr[src.typ.form]+dest.adr*80H); XTN(src); Release(src)  END
    ELSIF src.mode=Fn THEN  MRG(dest); OpL(mRg*10000H+0F2006000H+fmtInstr[dest.typ.form]+src.adr*80H); XTN(dest); Release(src)
    ELSIF dest.typ=PLT.realtyp  THEN  Move(src, dest, Real)
    ELSE  Ref(dest); dMrg:=SHORT(dest.adr*200H);
      IF  src.mode=Imm  THEN  OpW(20FCH+dMrg); OpL(src.adr); OpW(20FCH+dMrg); OpL(src.disp) (*MOVE.L #hi lo, (Adest)+*)
      ELSE  Ref(src); OpW(SHORT(src.adr)+20D8H+dMrg); OpW(SHORT(src.adr)+2090H+dMrg); Release(src)  END (*MOVE.L (Asrc)+, (Adest)+*)
    END
  END FMove;


  PROCEDURE Push*(VAR src: Item; f: INTEGER);
    VAR val: LONGINT;
  BEGIN
    IF  src.mode=Imm  THEN  val:=src.adr;
      IF  val=0 THEN  OpW(4227H+szInstr[f])
      ELSIF (val=true)&(f=Bool) THEN  OpW(50E7H)
      ELSE  OpW(mvInstr[f]+0F3CH);
        CASE  f OF  Byte, Bool, Char, SInt, Int:  OpW(SHORT(val))
        | LInt, Real, Set, ProcTyp, Pointer:  OpL(val)  END;
      END
    ELSIF src.mode=CCR  THEN
      IF  (src.alpha=0)&(src.beta=0)  THEN  (*No Tjmp or Fjmp Pending*)
        IF  src.code<0  THEN  OpL(0F2670000H-src.code)  ELSE  OpW(50E7H+src.code*100H)  END (*F/Scc.B cond, dest*)
      ELSE
        IF  src.code#ccT  THEN  BccLink(InvertCC(src.code), src.beta) END;  (*B~cond Fjmp*)
        FixLink(src.alpha); OpL(50E76002H); FixLink(src.beta); OpW(4227H) (*Tjmp: ST; BRA +2; Fjmp: CLR*)
      END
    ELSE  MRG(src); OpW(SHORT(mRg)+mvInstr[f]+0F00H);
      IF  (f=ProcTyp)&(src.adr=0)&(src.mode=AbsRef) THEN  AbsLink(fixProc.fixlink); fixProc:=NIL
      ELSE  XTN(src)  END;
      Release(src)
    END
  END Push;

  PROCEDURE FPush*(VAR src: Item; f: INTEGER);
  BEGIN
    IF  src.mode=Fn (*no VFn!*) THEN  OpL(0F2276000H+fmtInstr[f]+src.adr*80H)
    ELSIF f=Real  THEN  MRG(src); OpW(2F00H+SHORT(mRg)); XTN(src)
    ELSIF src.mode=Imm  THEN  OpW(2F3CH); OpL(src.disp); OpW(2F3CH); OpL(src.adr)
    ELSE  Ref(src); OpL(src.adr*10000H+2F280004H); OpW(2F10H+SHORT(src.adr))  END;  (*MOVE.L 4(As), -(A7); MOVE.L (As), -A7*)
    Release(src)
  END FPush;


  PROCEDURE SaveReg*(VAR rs: RegSet);
    VAR i: INTEGER; fr, fm, gr, gm: LONGINT;
  BEGIN rs:=register; fr:=1; fm:=0; gr:=8; gm:=0;
    i:=4; WHILE i>=0  DO  IF register[Areg, i]#0 THEN INC(gm, gr) END; DEC(i); INC(gr, gr)  END;  (*Mask:  d0d1..a6a7*)
    i:=7; WHILE i>=0  DO  IF register[Dreg, i]#0 THEN INC(gm, gr) END; DEC(i); INC(gr, gr)  END;  (*Mask:  d0d1..a6a7*)
    i:=0; WHILE i<=7  DO  IF register[Freg, i]#0 THEN INC(fm, fr) END; INC(i); INC(fr, fr)  END;  (*Mask:  f7..f0*)
    IF  gm#0  THEN  OpL(48E70000H+gm) END;  (*MOVEM regs, -(A7)*)
    IF  fm#0  THEN  OpL(0F227E000H+fm)  END (*FMOVEM fregs, -(A7)*)
  END SaveReg;

  PROCEDURE RestoreReg*(rs: RegSet; VAR x: Item);
    VAR i: INTEGER; fr, fm, gr, gm: LONGINT; y: Item;
  BEGIN register:=rs; fr:=1; fm:=0; gr:=1; gm:=0;
    IF  x.typ.form IN {Real, LReal} THEN  x.mode:=Fn; x.adr:=0;
      IF  rs[Freg, 0]#0 THEN  GetF(y); FMove(x, y); x.adr:=y.adr  END;  register[Freg, 0]:=1
    ELSIF x.typ#PLT.notyp THEN  x.mode:=Pop ELSE  x.mode:=Inval END;
    i:=7; WHILE i >=0 DO  IF rs[Freg, i]#0 THEN INC(fm, fr) END; DEC(i); INC(fr, fr)  END;  (*Mask:  f0..f7*)
    i:=0; WHILE i <=7 DO  IF rs[Dreg, i]#0 THEN INC(gm, gr) END; INC(i); INC(gr, gr)  END;  (*Mask:  a7a6..d1d0*)
    i:=0; WHILE i <=4 DO  IF rs[Areg, i]#0 THEN INC(gm, gr) END; INC(i); INC(gr, gr)  END;  (*Mask:  a7a6..d1d0*)
    IF  (x.mode=Pop) & ((fm#0)OR(gm#0)) THEN  y:=x; GetD(x); Move(y, x, x.typ.form) END;  (*No REAL Results on Stack*)
    IF  fm#0  THEN  OpL(0F21FD000H+fm)  END;  (*FMOVEM (A7)+, fregs*)
    IF  gm#0  THEN  OpL(4CDF0000H+gm) END (*MOVEM (A7)+, regs*)
  END RestoreReg;


(*Register Moves*)

  PROCEDURE LoadA*(VAR x: Item);
    VAR y: Item;
  BEGIN IF  x.mode#An THEN  y:=x; GetA(x); Move(y, x, LInt) END
  END LoadA;

  PROCEDURE LoadD*(VAR x: Item);
    VAR y: Item;
  BEGIN IF  x.mode#Dn THEN  y:=x; GetD(x); Move(y, x, x.typ.form) END
  END LoadD;

  PROCEDURE LoadF*(VAR x: Item);
    VAR y: Item;
  BEGIN IF  x.mode#Fn THEN  y:=x; GetF(x); FMove(y, x); x.typ:=PLT.lrltyp END
  END LoadF;

  PROCEDURE LoadX*(VAR x: Item);  (*Load Sign Extended*)
    VAR y: Item; f, mode: INTEGER;
  BEGIN f:=x.typ.form; mode:=x.mode;
    IF  f=Char  THEN  y:=x; GetD(x); OpW(4280H+SHORT(x.adr)); Move(y, x, Char)  (*CLR.L Dx; MOVE*)
    ELSE
      IF  mode=Imm  THEN  f:=LInt END;
      IF  mode#Dn THEN  y:=x; GetD(x); Move(y, x, f)  END;
      IF  mode#Imm  THEN
        IF  sizeCode[f]=Half  THEN  OpW(SHORT(49C0H+x.adr)) (*EXTB.L Dx*)
        ELSIF sizeCode[f]=Word  THEN  OpW(SHORT(48C0H+x.adr)) (*EXT.L Dx*)  END
      END
    END
  END LoadX;


(*Instruction Formats*)

  PROCEDURE Op1*(fmt: INTEGER; op: LONGINT; VAR dest: Item);
    VAR v: SET;
  BEGIN v:=SYS.VAL(SET, LONG(fmt));
    IF  bitSZ IN v  THEN  INC(op, szInstrL[dest.typ.form])  END;
    IF  (bitLD IN v)&(dest.mode#Dn) THEN  LoadD(dest) ELSIF bitXLD IN v THEN  LoadX(dest) END;
    CASE  (fmt MOD 32)  OF
    | opNOP1:
    | opRx: OpW(SHORT(op+dest.adr))
    | opRxLong: OpL(op+dest.adr*10000H)
    | opRy: OpW(SHORT(op+dest.adr*200H))
    | opRyLong: OpL(op+dest.adr*2000000H)
    | opEa: MRG(dest); OpW(SHORT(op+mRg)); XTN(dest)
    | opEaLong: MRG(dest); OpL(op+mRg*10000H); XTN(dest)
    | opRwLong: OpL(op+dest.adr*1000H)
    | opRzRz: OpW(SHORT(op+dest.adr*200H+dest.adr))
    | opRzRzLong: OpL(op+dest.adr*2000000H+dest.adr*10000H)
    END;
    IF  bitRD IN v  THEN  Release(dest) END
  END Op1;

  PROCEDURE Op2*(fmt: INTEGER; op: LONGINT; VAR src, dest: Item);
    VAR v: SET;
  BEGIN v:=SYS.VAL(SET, LONG(fmt));
    IF  bitSZ IN v  THEN  INC(op, szInstrL[dest.typ.form])  END;
    IF  (bitLS IN v)&(src.mode#Dn)  THEN  LoadD(src)  ELSIF bitXLS IN v THEN  LoadX(src)  END;
    IF  (bitLD IN v)&(dest.mode#Dn) THEN  LoadD(dest) ELSIF bitXLD IN v THEN  LoadX(dest) END;
    CASE  (fmt MOD 32)  OF
    | opNOP2:
    | opRyRx: OpW(SHORT(op+src.adr*200H+dest.adr))
    | opRxRy: OpW(SHORT(op+dest.adr*200H+src.adr))
    | opEaRn: MRG(src); OpW(SHORT(op+mRg+dest.adr*200H)); XTN(src)
    | opRnEa: MRG(dest); OpW(SHORT(op+mRg+src.adr*200H)); XTN(dest)
    | opImmEa:  MRG(dest); OpW(SHORT(op+mRg)); XTN(src); XTN(dest)
    | opEaRwLong: MRG(src); OpL(op+mRg*10000H+dest.adr*1000H); XTN(src)
    | opRwEaLong: MRG(dest); OpL(op+mRg*10000H+src.adr*1000H); XTN(dest)
    END;
    IF  ~(bitKS IN v) THEN  Release(src)  END;
    IF  bitRD IN v  THEN  Release(dest) END
  END Op2;

  PROCEDURE FOp1*(op: LONGINT; VAR dest: Item); (*Force Result to Fn*)
    VAR src: Item;
  BEGIN
    IF  dest.mode=Fn  THEN  OpL(op+dest.adr*400H+dest.adr*80H)
    ELSE  src:=dest; GetF(dest); MRG(src); OpL(op+mRg*10000H+4000H+fmtInstr[src.typ.form]+dest.adr*80H); XTN(src); Release(src) END
  END FOp1;

  PROCEDURE FOp2*(op: LONGINT; VAR src, dest: Item);  (*Force Result to Fn*)
    VAR aux: Item;
  BEGIN
    IF  dest.mode#Fn  THEN  aux:=dest; GetF(dest); FMove(aux, dest) END;
    IF  src.mode=Fn THEN  OpL(op+src.adr*400H+dest.adr*80H)
    ELSE  MRG(src); OpL(mRg*10000H+op+4000H+fmtInstr[src.typ.form]+dest.adr*80H); XTN(src)  END;
    Release(src)
  END FOp2;



(*Auxiliary*)

  PROCEDURE ADDA*(val, reg: LONGINT); (*Add Longword Constant to Address Register*)
  BEGIN
    IF  val#0 THEN
      IF  (val>0)&(val<=8)  THEN  OpW(5088H+SHORT((val MOD 8)*200H+reg))  (*ADDQ.L #val, Ar*)
      ELSIF (val<0)&(val>=-8) THEN  OpW(5188H+SHORT(((-val) MOD 8)*200H+reg)) (*SUBQ.L #val, Ar*)
      ELSIF (val>=-8000H)&(val<8000H) THEN  OpL((41E8H+reg*200H+reg)*10000H+(val MOD 10000H)) (*LEA val(Ar), Ar*)
      ELSE  OpW(SHORT(0D1FCH+reg*200H)); OpL(val) END (*ADDA.L val, Ar*)
    END
  END ADDA;


(*Addressing*)

  PROCEDURE Ref*(VAR x: Item);  (*Reference*)
    VAR mode: INTEGER; adr, reg, disp: LONGINT;
  BEGIN mode:=x.mode; adr:=x.adr; disp:=x.disp;
    IF  (mode=RegInd)&(adr#FPR) THEN  ADDA(disp, adr)
    ELSIF (mode=Indexed)&(adr#FPR)&(disp=0)&(x.beta=Half) THEN  DEC(register[Dreg, x.inxreg]);
      IF  x.code=0  THEN  OpW(SHORT(0D0C0H+adr*200H+x.inxreg))  (*ADDA.W Dinxreg, Aadr*)
      ELSE  OpW(SHORT(0D1C0H+adr*200H+x.inxreg))  END (*ADDA.L Dinxreg, Aadr*)
    ELSE  AllocA(reg);
      IF  mode=MemInd THEN  DEC(register[Areg, adr]);
        OpL(20680000H+reg*2000000H+adr*10000H+(x.descr MOD 10000H)); ADDA(disp, reg)  (*MOVEA.L d(Ax), Areg*)
      ELSE  MRG(x); OpW(41C0H+SHORT(mRg+reg*200H)); XTN(x); Release(x)  END;  (*LEA x, Areg*)
      x.adr:=reg
    END;
    x.mode:=RegInd; x.disp:=0
  END Ref;

  PROCEDURE RefToA1*(VAR x: Item);  (*Move Address to A1*)
  BEGIN
    IF  x.mode=MemInd THEN  OpL(22680000H+x.adr*10000H+(x.descr MOD 10000H)); ADDA(x.disp, 1) (*MOVEA.L d(Ax), A1*)
    ELSE  MRG(x); OpW(43C0H+SHORT(mRg)); XTN(x) END;  (*LEA x, A1*)
    Release(x)
  END RefToA1;

  PROCEDURE RefToStk*(VAR x: Item); (*Push Address*)
  BEGIN
    IF  (x.mode=MemInd)&(x.disp=0)  THEN  OpL(2F280000H+x.adr*10000H+(x.descr MOD 10000H))  (*MOVE.L d(Ax), -(SP)*)
    ELSE  MRG(x); OpW(4840H+SHORT(mRg)); XTN(x) END;  (*PEA x*)
    Release(x)
  END RefToStk;

  PROCEDURE DeRef*(VAR x: Item);  (*Dereference*)
    VAR reg: LONGINT;
  BEGIN
    IF  x.mode#An THEN  AllocA(reg);
      MRG(x); OpW(2040H+SHORT(mRg+reg*200H)); XTN(x); Release(x); x.adr:=reg  (*MOVEA.L x, Areg*)
    END;
    x.mode:=RegInd; x.disp:=0
  END DeRef;

  PROCEDURE InitTypDescs*();  (* mfix *)
    VAR adr, i: INTEGER; src, dst: Item; typ, btyp: PLT.Struct;

    PROCEDURE InitTproc(fld: PLT.Object): BOOLEAN;
      VAR src: Item; res: BOOLEAN;
    BEGIN
      res := FALSE;
      WHILE fld # NIL DO
        IF (fld.mode = TProc) & (fld.adr = adr) THEN
          RefTProc(src, SHORT(fld.ival)); dst.disp:=TprocOffset+fld.adr*4; Move(src, dst, LInt);
          res := TRUE
        END;
        fld := fld.nxtobj
      END;
      RETURN res;
    END InitTproc;

  BEGIN
    i := 0; WHILE i < nofrecs-1 DO
      typ := recs[i];
      IF  typ.n>0 THEN  btyp:=typ.BaseTyp;
        dst.mode:=AbsRef; dst.adr:=typ.tdadr; dst.alpha:=typ.mno; LoadA(dst); dst.mode:=RegInd;
        IF  btyp#NIL  THEN  src.mode:=AbsRef; src.adr:=btyp.tdadr; src.alpha:=btyp.mno  ELSE  src.mode:=Undef END;
        adr:=0;
        WHILE adr<typ.n DO
          IF  ~InitTproc(typ.dsc) THEN
            IF  src.mode=AbsRef THEN  LoadA(src); src.mode:=RegInd  END;
            src.disp:=TprocOffset+adr*4; MultiRef(src);
            dst.disp:=TprocOffset+adr*4; Move(src, dst, LInt)
          END;
          INC(adr)
        END;
        Release(src); Release(dst)
      END;
      INC(i)
    END
  END InitTypDescs;

(*Designators*)

  PROCEDURE LocalVar*(VAR x: Item; lev: INTEGER; adr: LONGINT; indirect: BOOLEAN);
    VAR reg: LONGINT; ldiff: INTEGER;
  BEGIN ldiff:=level-lev;
    IF  ldiff=0 THEN  INC(register[Areg, FPR]); x.adr:=FPR
    ELSE  AllocA(reg); x.adr:=reg; OpL(206E0008H+reg*2000000H); (*MOVEA.L (lnk, FP), Ax*)
      WHILE ldiff>1 DO  DEC(ldiff); OpL(20680008H+reg*2000000H+reg*10000H)  END (*MOVEA.L (lnk, Ax), Ax*)
    END;
    IF  indirect  THEN  x.mode:=MemInd; x.disp:=0; x.descr:=adr; x.alpha:=lev ELSE  x.mode:=RegInd; x.disp:=adr END
  END LocalVar;

  PROCEDURE Open*(VAR block: LONGINT);
    VAR i, j: INTEGER;
  BEGIN level:=0; copied:=0; nofrecs := 0;
    Kernel.AllocBlock(block, 32*1024-2); data:=SYS.VAL(BlkPtr, block); cp:=0;
    Kernel.AllocBlock(block, 64*1024-2); codeBase:=block; code:=SYS.VAL(BlkPtr, block); pc:=0;
    i:=0;   WHILE i < 3 DO j:=0; WHILE j < 8 DO register[i, j]:=0; INC(j) END; INC(i) END
  END Open;

  PROCEDURE Close*(VAR block: LONGINT);
  BEGIN
    Kernel.AdjustBlock(block, LONG(pc)*2);
    Kernel.AdjustBlock(SYS.VAL(LONGINT, data), LONG(cp)*2);
  END Close;

BEGIN
  mvInstr[Byte]:=1000H; mvInstr[Bool]:=1000H; mvInstr[Char]:=1000H; mvInstr[SInt]:=1000H; mvInstr[Int]:=3000H; mvInstr[LInt]:=2000H;
  mvInstr[Real]:=2000H; mvInstr[Set]:=2000H; mvInstr[NilTyp]:=2000H; mvInstr[ProcTyp]:=2000H; mvInstr[Pointer]:=2000H;
  szInstr[Int]:=40H; szInstr[LInt]:=80H; szInstr[Real]:=80H; szInstr[Set]:=80H; szInstr[NilTyp]:=80H; szInstr[ProcTyp]:=80H; szInstr[Pointer]:=80H;
  szInstrL[Int]:=40H; szInstrL[LInt]:=80H; szInstrL[Real]:=80H; szInstrL[Set]:=80H; szInstrL[NilTyp]:=80H; szInstrL[ProcTyp]:=80H; szInstrL[Pointer]:=80H;
  fmtInstr[SInt]:=6*400H; fmtInstr[Int]:=4*400H; fmtInstr[Real]:=400H; fmtInstr[LReal]:=5*400H;
  sizeCode[Int]:=Word; sizeCode[LInt]:=Long; sizeCode[Real]:=Long; sizeCode[LReal]:=Double; sizeCode[Set]:=Long;
  sizeCode[NilTyp]:=Long; sizeCode[ProcTyp]:=Long; sizeCode[Pointer]:=Long;
  PLT.typSize:=TypSize;
END OPLL.