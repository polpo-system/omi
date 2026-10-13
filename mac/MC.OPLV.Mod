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

MODULE OPLV;  (*mf 15.5.94 / tk object model 1.7.96 *)

  (* 30.7.96  Method support (mfix) / WITH correction *)

  IMPORT
    TB, SYS:=SYSTEM, Kernel, Modules, PLT:=OPLT, PLL:=OPLL, PLC:=OPLC;

  CONST
    MaxAbove=3072;  (* 16384 *)
    MaxBelow=768; (* 4096 *)

    Var=1; Par=2; VarPar=3; Con=4; Fld=5; LProc=6; XProc=7; TProc = 14; TypDynArr=8; TypArray=9; TypPointer=10;
    TypRecord=11; TypProcTyp=12;
    Bool=2; Char=3; SInt=4; Int=5; LInt=6; Real=7; LReal=8; Set=9; String=10; NilTyp=11;
    NoTyp=12; Pointer=13; ProcTyp=14; Comp=15; Basic=1; Array=2; DynArr=3; Record=4;

    Tend=00H; Telsif=01H; Telse=02H; Twend=03H; Tcastrap=04H; Tcaslbl1=05H; Tcasrng1=06H; Tcaslbl2=07H; Tcasrng2=08H;
    Tbegin=09H; TconstNil=00H; TconstFalse=01H; TconstTrue=02H; TconstChar=03H;
    TconstSInt=04H; TconstInt=05H; TconstLInt=06H; TconstSet=07H; TconstReal=08H; TconstLReal=09H; TconstString=0AH;
    Tderef=0BH; Tindex=0CH; TmopNot=0DH; TmopMinus=0EH; TmopAbs=0FH; TmopCap=10H; TmopOdd=11H;
    TdopAnd=12H; TdopOr=13H; TdopTimes=14H; TdopSlash=15H; TdopDiv=16H; TdopMod=17H;
    TdopPlus=18H; TdopMinus=19H; TdopMsk=1AH; TdopAsh=1BH; TdopLen=1CH; TdopIn=1DH;
    TdopEql=1EH; TdopNeq=1FH; TdopLss=20H; TdopLeq=21H; TdopGtr=22H; TdopGeq=23H; Tupto=24H;
    Tcall=25H; TasgnNewfn=26H; TasgnAssign=27H; TasgnIncfn=28H; TasgnDecfn=29H; TasgnInclfn=2AH; TasgnExclfn=2BH;
    TasgnCopyfn=2CH; Tassert=2DH; Tif=2EH; Tcase=2FH; Twhile=30H; Trepeat=31H; Tloop=32H; Texit=33H; Twith=34H; Ttrap=35H;

    UvarGlobal=40H; UvarDirect=41H; UvarIndirect=42H; UvarparIndirect=43H; Uproc=44H; Ufield=45H;
    Uguard=46H; Ueguard=47H; UmopIs=48H; UmopConv=49H; UmopConvSet=4AH;
    Uenter=4BH; Ureturn0=4CH; Ureturn1=4DH;
    UcallXPrc=4EH; UcallXFnc=UcallXPrc+1; UcallXRFnc=UcallXPrc+2;
    UcallLPrc=51H; UcallLFnc=UcallLPrc+1; UcallLRFnc=UcallLPrc+2;
    UcallPrcV=54H; UcallFncV=UcallPrcV+1; UcallRFncV=UcallPrcV+2;
    UasgnAssignBool=57H; UasgnAssignOther=58H;

    Absolute=21; AbsRef=22; Imm=23; TDProc=29;
    flgOK=0; flgNoLeft=-1; flgNoRight=-2; flgEnter=-3; Local=FALSE; Global=TRUE; Internal=FALSE; External=TRUE;
    internal=0; external=1;

  (*Export/Use Section*)
    EUEnd = 0;  EURecord = 1; EUobjScope = 0;   EUrecScope = 1; EUerrScope = -1;

  TYPE
    Node=POINTER TO NodeDesc;
    NodeDesc=RECORD
      left, right: Node;
      tag: LONGINT; flag, subflg: SHORTINT;
      typ: PLT.Struct; obj: PLT.Object;
      safe, global, super: BOOLEAN; from, to: PLL.Label;
      filler: LONGINT
    END;


  VAR
    assert, refs: BOOLEAN;
    body*: Modules.Command;
    TAG: LONGINT; B: Kernel.Buffer; M: Modules.Module;
    nilNode, falseNode, trueNode: Node; ExitChain: PLL.Label;
    astk, bstk: ARRAY 64 OF LONGINT; dsp: INTEGER;  (*node dictionary stack*)
    NNN, N, above, below: LONGINT;  (*node memory*)
    constNodeOT: ARRAY NilTyp+1 OF SHORTINT;  (*node tags by form*)
    contyp: ARRAY- TconstSet+1 OF PLT.Struct; (*constant types by tag*)

(*Dictionary*)

  PROCEDURE PushDict;
  BEGIN bstk[dsp]:=below; INC(dsp)
  END PushDict;

  PROCEDURE PopDict;
  BEGIN DEC(dsp); below:=bstk[dsp]
  END PopDict;


(*Node Creation*)

  PROCEDURE NNode(VAR p: Node; tag: LONGINT; typ: PLT.Struct; obj: PLT.Object; left, right: Node; global: BOOLEAN);
    VAR n: Node;
  BEGIN
    IF  global  THEN  n:=SYS.VAL(Node, N+above*SIZE(NodeDesc)); INC(above)
    ELSE  n:=SYS.VAL(Node, N+below*SIZE(NodeDesc)); DEC(below)  END;
    n.tag:=tag; n.flag:=0; n.subflg:=0; n.typ:=typ; n.obj:=obj; n.left:=left; n.right:=right; n.safe:=FALSE; n.global:=global;
    n.super:=FALSE; p:=n
  END NNode;

  PROCEDURE UNodeO(tag: LONGINT; flag: SHORTINT; typ: PLT.Struct; obj: PLT.Object; global: BOOLEAN);
    VAR n: Node;
  BEGIN
    IF  global  THEN  n:=SYS.VAL(Node, N+above*SIZE(NodeDesc)); INC(above)
    ELSE  n:=SYS.VAL(Node, N+below*SIZE(NodeDesc)); DEC(below)  END;
    n.tag:=tag; n.flag:=flag; n.subflg:=0; n.typ:=typ; n.obj:=obj; n.safe:=FALSE; n.global:=global
  END UNodeO;

  PROCEDURE UNodeLR(tag: LONGINT; flag: SHORTINT; typ: PLT.Struct; left, right: Node; global: BOOLEAN);
    VAR n: Node;
  BEGIN
    IF  global  THEN  n:=SYS.VAL(Node, N+above*SIZE(NodeDesc)); INC(above)
    ELSE  n:=SYS.VAL(Node, N+below*SIZE(NodeDesc)); DEC(below)  END;
    n.tag:=tag; n.flag:=flag; n.subflg:=0; n.typ:=typ; n.left:=left; n.right:=right; n.safe:=FALSE; n.global:=global
  END UNodeLR;

  PROCEDURE PNode(VAR p: Node; remain, match: SHORTINT; par: Node; global: BOOLEAN);
    VAR n: Node;  (*p.typ=result type, p.obj=formal parameter*)
  BEGIN
    IF  global  THEN  n:=SYS.VAL(Node, N+above*SIZE(NodeDesc)); INC(above)
    ELSE  n:=SYS.VAL(Node, N+below*SIZE(NodeDesc)); DEC(below)  END;
    n.tag:=p.tag; n.flag:=remain; n.subflg:=match; n.typ:=p.typ; n.left:=p; n.right:=par; n.safe:=FALSE; n.global:=global;
    IF  match=1 THEN  n.obj:=p.obj.par  ELSE  n.obj:=p.obj.nxtobj END;
    p:=n
  END PNode;


  PROCEDURE CallNode(VAR n: Node; tag: LONGINT; nofpar: INTEGER; typ: PLT.Struct; obj: PLT.Object; left: Node; global: BOOLEAN);
  BEGIN
    IF  typ=PLT.notyp THEN  NNode(n, tag, NIL, obj, left, NIL, global)
    ELSIF typ.form IN {Real, LReal} THEN  NNode(n, tag+2, typ, obj, left, NIL, global)
    ELSE  NNode(n, tag+1, typ, obj, left, NIL, global)  END;
    n.flag:=SHORT(nofpar)
  END CallNode;

  PROCEDURE VarNodes(n: Node; typ: PLT.Struct; global: BOOLEAN);
  BEGIN
    IF  typ=PLT.booltyp THEN
      UNodeLR(UasgnAssignBool, flgNoLeft, NIL, NIL, n, global);
      UNodeLR(UasgnAssignBool, flgNoRight, NIL, n, NIL, global);
    ELSE
      UNodeLR(UasgnAssignOther, flgNoLeft, NIL, NIL, n, global);
      UNodeLR(UasgnAssignOther, flgNoRight, NIL, n, NIL, global);
    END;
    IF  typ.form=Pointer  THEN
      NNode(n, Tderef, typ.BaseTyp, NIL, n, NIL, global)
    ELSIF (typ.comp=Array) OR (typ.comp=DynArr) THEN
      UNodeLR(Tindex, flgNoRight, typ.BaseTyp, n, NIL, global)
    END
  END VarNodes;

  PROCEDURE GenNode(obj: PLT.Object; typ: PLT.Struct; mode: INTEGER; external, global: BOOLEAN);
    VAR n, dum: Node; fld: PLT.Object;
  BEGIN
    CASE  mode  OF
    | Var:
        IF  obj.level=0 THEN  NNode(n, UvarGlobal, typ, obj, NIL, NIL, global)
        ELSE  NNode(n, UvarDirect, typ, obj, NIL, NIL, global)  END;
        IF  ~external THEN  VarNodes(n, typ, global)  END
    | Par:
        IF  (typ.comp=DynArr)OR((typ.size>4)&(typ.form#LReal))  THEN  NNode(n, UvarIndirect, typ, obj, NIL, NIL, global)
        ELSE  NNode(n, UvarDirect, typ, obj, NIL, NIL, global)  END;
        IF  ~external THEN  VarNodes(n, typ, global)  END
    | VarPar:
        NNode(n, UvarparIndirect, typ, obj, NIL, NIL, global);
        IF  ~external THEN  VarNodes(n, typ, global)  END
    | TypPointer:
        UNodeO(Uguard, flgNoLeft, typ, NIL, global);
        UNodeO(Ueguard, flgNoLeft, typ, NIL, global);
        UNodeO(UmopIs, flgNoLeft, PLT.booltyp, obj, global)
    | TypRecord:
        UNodeO(Uguard, flgNoLeft, typ, NIL, global);
        UNodeO(Ueguard, flgNoLeft, typ, NIL, global);
        UNodeO(UmopIs, flgNoLeft, PLT.booltyp, obj, global);
        fld:=typ.dsc; WHILE fld#NIL DO  (* mfix *)
          IF fld.mode = Fld THEN
            UNodeO(Ufield, flgNoLeft, fld.typ, fld, global)
          ELSE
            NNode(n, Uproc, fld.typ, fld, NIL, NIL, global);
            IF external THEN
              CallNode(n, UcallXPrc, fld.nofpar, fld.typ, fld, NIL, global);
              CallNode(n, UcallXPrc, fld.nofpar, fld.typ, fld, NIL, global); n.super := TRUE;
            ELSE
              CallNode(n, UcallLPrc, fld.nofpar, fld.typ, fld, NIL, global);
              CallNode(n, UcallLPrc, fld.nofpar, fld.typ, fld, NIL, global); n.super := TRUE;
              UNodeO(Uenter, flgEnter, fld.typ, fld, global)
            END;
          END;
          fld:=fld.nxtobj
        END
    | LProc, XProc:
        NNode(n, Uproc, typ, obj, NIL, NIL, global);
        IF  external  THEN  CallNode(n, UcallXPrc, obj.nofpar, typ, obj, NIL, global)
        ELSE  CallNode(n, UcallLPrc, obj.nofpar, typ, obj, NIL, global); UNodeO(Uenter, flgEnter, typ, obj, global) END
    | Con:
        IF  typ.form#Bool THEN  NNode(n, constNodeOT[typ.form], typ, obj, NIL, NIL, Global) END
    ELSE END;
  END GenNode;

  PROCEDURE GenNodes(obj: PLT.Object; external, global: BOOLEAN);
  BEGIN
    WHILE obj#NIL DO GenNode(obj, obj.typ, obj.mode, external, global); obj:=obj.nxtobj END;
  END GenNodes;

(*code generation*)

  PROCEDURE ^ Statement;
  PROCEDURE ^ Compile(n: Node; VAR x: PLL.Item);

  PROCEDURE Call(n: Node; VAR tproc: PLL.Item);
    VAR tag: LONGINT; left, right, proc: Node; ap: PLL.Item; s: LONGINT;
  BEGIN (* Passing of parameters is safe iff each parameter is safe; complete procedure call is safe only if called procedure is external *)
    IF  n.safe  THEN  PLL.CopyCode(n.from, n.to)
    ELSE  tag:=n.tag; left:=n.left; right:=n.right;
      n.from:=PLL.pc;
      IF  n.subflg=0  THEN
        IF  (tag=UcallXFnc) OR (tag=UcallLFnc) OR (tag=UcallFncV) THEN  s:=n.typ.size; INC(s, s MOD 2); PLL.ADDA(-s, 7) END
      ELSE
        Call(left, tproc); Compile(right, ap);
        IF  n.obj.typ.form=ProcTyp  THEN  PLL.fixProc:=right.obj  END;
        IF n.subflg = 1 THEN
          proc := n; WHILE  proc.subflg > 0 DO  proc:=proc.left END;
          IF proc.obj.mode = TProc THEN
            tproc.typ := proc.obj.typ; tproc.adr := proc.obj.adr;  tproc.mode := TDProc;
            PLC.PrepTprocCall(ap, right.tag, tproc, proc.super);
          END
        END;
        PLC.Param(ap, n.obj, right.tag);
        IF  n.subflg=1  THEN  n.safe:=right.safe&(proc.obj.mode # TProc)  ELSE  n.safe:=left.safe&right.safe  END
      END;

      IF  n.flag=0  THEN  proc:=n;  (*outermost parameter*)
        WHILE proc.subflg > 0 DO  proc:=proc.left END;
        CASE  n.tag OF
        | UcallXPrc, UcallXFnc, UcallXRFnc: PLC.CallXProc(tproc, proc.obj)
        | UcallLPrc, UcallLFnc, UcallLRFnc: PLC.CallLProc(tproc, proc.obj); n.safe:=FALSE
        | UcallPrcV, UcallFncV, UcallRFncV: Compile(proc.left, ap); PLC.CallPV(ap);
        END
      END;
      n.to:=PLL.pc;
    END
  END Call;

  PROCEDURE NewArr(VAR x, y: PLL.Item; e: Node; typ, typ0: PLT.Struct);
    VAR len: PLL.Item;
  BEGIN
    Compile(e.left, len);
    PLC.NewArrMulLen(y, len, typ, typ0);  (* y:=nofelems *)
    IF  e.right=NIL THEN  PLC.NewArr(x, y, typ, typ0) ELSE  NewArr(x, y, e.right, typ.BaseTyp, typ0)  END;  (*y :=base type size *)
    PLC.NewArrSetLen(x, y, len, typ, typ0); (* y:=dimension*base typ size *)
    IF  typ=typ0  THEN  PLL.Release(x); PLL.Release(y); PLL.Release(len)  END
  END NewArr;

  PROCEDURE Compile(n: Node; VAR x: PLL.Item);
    VAR tag: LONGINT; left, right: Node; obj: PLT.Object; y, z: PLL.Item; rs: PLL.RegSet;
  BEGIN tag:=n.tag; left:=n.left; right:=n.right; obj:=n.obj;
    CASE  tag OF  (*for expressions, the type of Node parameter is guaranteed to be the correct result type*)
    | TconstNil..TconstReal:  x.mode:=Imm; x.adr:=obj.ival; n.safe:=TRUE
    | TconstLReal:  x.mode:=Imm; SYS.PUT(SYS.ADR(x.adr), obj.rval); n.safe:=TRUE
    | TconstString:
        IF  obj.adr=0 THEN  PLL.AllocString(obj.xval^, SHORT(obj.ival), obj.adr)  END;
        x.mode:=Absolute; x.adr:=obj.adr; x.disp:=0; x.beta:=SHORT(obj.ival); n.safe:=TRUE
    | UvarGlobal: x.mode:=Absolute; x.adr:=obj.adr; x.disp:=0; n.safe:=TRUE
    | UvarDirect: PLL.LocalVar(x, obj.level, obj.adr, FALSE); n.safe:=TRUE
    | UvarIndirect, UvarparIndirect:  PLL.LocalVar(x, obj.level, obj.adr, TRUE); n.safe:=TRUE
    | Ufield: Compile(left, x); PLC.Field(x, obj.adr); n.safe:=left.safe
    | Tderef: Compile(left, x); PLC.DeRef(x); n.safe:=left.safe
    | Tindex: Compile(left, x); Compile(right, y); PLC.Index(x, y); n.safe:=left.safe&right.safe
    | Uguard: Compile(left, x); PLC.TypTest(x, n.typ, TRUE, FALSE); n.safe:=left.safe
    | Ueguard:  Compile(left, x); PLC.TypTest(x, n.typ, TRUE, TRUE); n.safe:=left.safe
    | Uproc:  x.mode:=AbsRef; x.adr:=obj.adr; n.safe:=TRUE; (*Implementation Restriction 800 Guaranteed*)
    | UmopIs: Compile(left, x); PLC.TypTest(x, obj.typ, FALSE, FALSE); n.safe:=left.safe
    | UmopConv: Compile(left, x); PLC.Convert(x, x.typ.form, n.typ.form); n.safe:=left.safe
    | UmopConvSet, TmopNot..TmopOdd:  Compile(left, x); PLC.MOp(x, tag); n.safe:=left.safe
    | TdopTimes..TdopIn:  Compile(left, x); Compile(right, y); PLC.DOp(x, y, tag); n.safe:=left.safe&right.safe
    | TdopAnd:  Compile(left, x); PLC.CondAnd(x); Compile(right, y); PLC.DOp(x, y, TdopAnd); n.safe:=left.safe&right.safe
    | TdopOr: Compile(left, x); PLC.CondOr(x); Compile(right, y); PLC.DOp(x, y, TdopOr); n.safe:=left.safe&right.safe
    | TdopEql..TdopGeq: Compile(left, x); PLC.Relation(x); Compile(right, y); PLC.DOp(x, y, tag); n.safe:=left.safe&right.safe
    | Tupto:  Compile(left, y); Compile(right, z); PLC.SetRange(x, y, z); n.safe:=left.safe&right.safe
    | TasgnNewfn: Compile(left, x);
      IF  right=NIL THEN  PLC.New(x); n.safe:=left.safe (*e.g. NEW(a[F(i)])*)
      ELSE  NewArr(x, z, right, x.typ.BaseTyp, x.typ.BaseTyp) END
    | UasgnAssignBool:  Compile(left, x); Compile(right, y); PLC.Assign(x, y); n.safe:=left.safe&right.safe
    | UasgnAssignOther: Compile(right, y); PLL.fixProc:=right.obj; Compile(left, x); PLC.Assign(x, y); n.safe:=left.safe&right.safe
    | TasgnIncfn..TasgnCopyfn:  Compile(left, x); Compile(right, y); PLC.AStat(x, y, tag); n.safe:=left.safe&right.safe
    | Uenter: (*do nothing*)
    | UcallXPrc, UcallLPrc, UcallPrcV:  Call(n, y)
    | UcallXFnc, UcallLFnc, UcallFncV, UcallXRFnc, UcallLRFnc, UcallRFncV:  PLL.SaveReg(rs); Call(n, y); x.typ:=n.typ; PLL.RestoreReg(rs, x)
    | Ureturn0: PLC.ReturnFromProc(obj, FALSE, x); n.safe:=TRUE
    | Ureturn1: Compile(left, x); PLC.ReturnFromProc(obj, TRUE, x); n.safe:=left.safe
    END;
    x.typ:=n.typ
  END Compile;


  PROCEDURE Enter(n: Node);
    VAR proc, locals, par: PLT.Object; dum: Node; typ: PLT.Struct; x: PLL.Item;
  BEGIN proc:=n.obj; typ:=proc.typ;
    PushDict;
      IF  typ=PLT.notyp THEN  NNode(dum, Ureturn0, NIL, proc, NIL, NIL, Local)
      ELSE  UNodeO(Ureturn1, flgNoLeft, typ, proc, Local) END;
      locals:=proc.par; PLT.ReadScope(B, M, PLL.level, locals, Local);
      PLL.Traverse(locals); PLL.AllocLocalVar(locals, proc); GenNodes(locals, Internal, Local);
      IF  refs  THEN  proc.locals:=locals ELSE  proc.locals:=proc.par END;
      INC(PLL.level); Kernel.BufRNum(B, TAG); WHILE TAG#Tbegin  DO  Statement END;  DEC(PLL.level); (*nested*)
      PLC.EnterProc(proc);
      par:=proc.par;
      WHILE par#NIL DO
        IF  par.mode=Par  THEN
          IF  par.typ.comp=DynArr THEN  PLC.CopyDynArray(par.adr, par.typ)
          ELSIF (par.typ.size>4)&(par.typ.form#LReal) THEN  PLC.CopyPar(par.adr, SHORT(par.typ.size)) END
        END;
        par:=par.nxtobj
      END;
      Kernel.BufRNum(B, TAG); WHILE TAG#Tend  DO  Statement END;  (*body*)
      Kernel.BufRNum(B, TAG);
      IF  proc.typ#PLT.notyp  THEN  PLC.Trap(17)  ELSE  PLC.ReturnFromProc(proc, FALSE, x)  END;
    PopDict;
  END Enter;


  PROCEDURE RString(VAR b: Kernel.Buffer; VAR string: ARRAY OF CHAR; VAR len: LONGINT);
    VAR i: INTEGER;
  BEGIN Kernel.BufRString(b, string); i:=0; WHILE string[i]#0X  DO  INC(i)  END;  len:=i+1
  END RString;

  PROCEDURE Input(VAR n: Node);
    VAR tag: LONGINT; left, right, par, h: Node; obj, sent: PLT.Object; restyp: PLT.Struct; match, remain: SHORTINT; r: REAL;
  BEGIN tag:=TAG;
    CASE  tag OF
    | TconstNil:  n:=nilNode; Kernel.BufRNum(B, TAG)
    | TconstFalse:  n:=falseNode; Kernel.BufRNum(B, TAG)
    | TconstTrue: n:=trueNode; Kernel.BufRNum(B, TAG)
    | TconstChar..TconstSet:
        NEW(obj); Kernel.BufRNum(B, obj.ival); Kernel.BufRNum(B, TAG);
        NNode(n, tag, contyp[tag], obj, NIL, NIL, Global)
    | TconstReal:
        NEW(obj); Kernel.BufRIEEE4(B, r); obj.ival:=SYS.VAL(LONGINT, r); Kernel.BufRNum(B, TAG);
        NNode(n, TconstReal, PLT.realtyp, obj, NIL, NIL, Global)
    | TconstLReal:
        NEW(obj); Kernel.BufRIEEE8(B, obj.rval); Kernel.BufRNum(B, TAG);
        NNode(n, TconstLReal, PLT.lrltyp, obj, NIL, NIL, Global)
    | TconstString:
        NEW(obj); NEW(obj.xval); RString(B, obj.xval^, obj.ival); Kernel.BufRNum(B, TAG);
        NNode(n, TconstString, PLT.stringtyp, obj, NIL, NIL, Global)
    | Tderef:
        Kernel.BufRNum(B, TAG); Input(left);
        NNode(n, Tderef, left.typ.BaseTyp, NIL, left, NIL, left.global)
    | Tindex:
        Kernel.BufRNum(B, TAG); Input(left); Input(right);
        NNode(n, Tindex, left.typ.BaseTyp, NIL, left, right, left.global&right.global)
    | TmopNot..TmopCap:
        Kernel.BufRNum(B, TAG); Input(left);
        NNode(n, tag, left.typ, NIL, left, NIL, left.global)
    | TmopOdd:
        Kernel.BufRNum(B, TAG); Input(left);
        NNode(n, TmopOdd, PLT.booltyp, NIL, left, NIL, left.global)
    | TdopAnd..TdopAsh:
        Kernel.BufRNum(B, TAG); Input(left); Input(right);
        NNode(n, tag, left.typ, NIL, left, right, left.global&right.global)
    | TdopLen:
        Kernel.BufRNum(B, TAG); Input(left); Input(right);
        NNode(n, TdopLen, PLT.linttyp, NIL, left, right, left.global&right.global)
    | TdopIn..TdopGeq:
        Kernel.BufRNum(B, TAG); Input(left); Input(right);
        NNode(n, tag, PLT.booltyp, NIL, left, right, left.global&right.global)
    | Tupto:
        Kernel.BufRNum(B, TAG); Input(left); Input(right);
        NNode(n, Tupto, PLT.settyp, NIL, left, right, left.global&right.global)
    | TasgnNewfn:
        Kernel.BufRNum(B, TAG); Input(left);
        NNode(n, TasgnNewfn, NIL, NIL, left, NIL, left.global);
        restyp:=left.typ.BaseTyp; h:=n;
        WHILE (restyp.form=Comp) & (restyp.comp=DynArr) DO
          NEW(par); Input(par.left); h.right:=par; h:=par;
          restyp:=restyp.BaseTyp
        END;
    | TasgnAssign:
        Kernel.BufRNum(B, TAG); Input(left); Input(right);
        IF  left.typ=PLT.booltyp  THEN  NNode(n, UasgnAssignBool, NIL, NIL, left, right, left.global&right.global)
                              ELSE  NNode(n, UasgnAssignOther, NIL, NIL, left, right, left.global&right.global) END
    | TasgnIncfn..TasgnCopyfn:
        Kernel.BufRNum(B, TAG); Input(left); Input(right);
        NNode(n, tag, NIL, NIL, left, right, left.global&right.global)
    | Tcall:
        Kernel.BufRNum(B, TAG); Input(left); restyp:=left.typ.BaseTyp; match:=0; remain:=SHORT(left.typ.nofdsc);
        NEW(sent); sent.par:=left.typ.dsc; CallNode(n, UcallPrcV, remain, restyp, sent, left, left.global);
        WHILE remain > 0  DO  Input(par); INC(match); DEC(remain); PNode(n, remain, match, par, n.global&par.global)  END
    ELSE
        n:=SYS.VAL(Node, N+tag*SIZE(NodeDesc));
        CASE  n.flag  OF
        | flgOK:  Kernel.BufRNum(B, TAG)
        | flgNoLeft:  Kernel.BufRNum(B, TAG); Input(left); NNode(n, n.tag, n.typ, n.obj, left, n.right, left.global&n.global)
        | flgNoRight: Kernel.BufRNum(B, TAG); Input(right); NNode(n, n.tag, n.typ, n.obj, n.left, right, n.global&right.global)
        | flgEnter: Enter(n)
        ELSE
          Kernel.BufRNum(B, TAG); match:=n.subflg; remain:=n.flag;  (*params*)
          WHILE remain > 0  DO  Input(par); INC(match); DEC(remain); PNode(n, remain, match, par, n.global&par.global)  END
        END
    END
  END Input;


  PROCEDURE Statement;
    VAR exp, stat: Node; x, dum: PLL.Item; L, Lcfj, Lfix, nxtobjExitChain: PLL.Label; tab: INTEGER; obj: PLT.Object; typ: PLT.Struct; t: Node;
      min, max, lo, hi, tno: LONGINT; tag, class: LONGINT;
  BEGIN
    CASE  TAG OF
    | Tassert:
        Kernel.BufRNum(B, tno); Kernel.BufRNum(B, TAG); Input(exp);
        IF  assert  THEN  Compile(exp, x); PLL.TrapCC(x, tno) END
    | Tif, Twith: tag:=TAG;
        Kernel.BufRNum(B, TAG); Input(exp); class:=exp.tag; Compile(exp, x);
        IF (tag=Twith) & (class=UmopIs) THEN
          PushDict;
          obj:=exp.left.obj; typ:=obj.typ; obj.typ:=exp.obj.typ;
          GenNode(obj, obj.typ, obj.mode, FALSE, exp.left.global);
        END;
        PLL.CFJ(x, Lcfj); Lfix:=0;
        LOOP
          CASE  TAG OF
          | Telsif: Kernel.BufRNum(B, TAG); PLL.FJ(Lfix); PLL.FixLink(Lcfj); Input(exp); class:=exp.tag; Compile(exp, x);
            PLL.CFJ(x, Lcfj);
            IF (tag=Twith) & (class=UmopIs) THEN
              PopDict; obj.typ:=typ; PushDict;
              obj:=exp.left.obj; typ:=obj.typ; obj.typ:=exp.obj.typ;
              GenNode(obj, obj.typ, obj.mode, FALSE, exp.left.global);
            END;
          | Telse:
            IF (tag=Twith) & (class=UmopIs) THEN PopDict; obj.typ:=typ END;
            Kernel.BufRNum(B, TAG); PLL.FJ(Lfix); PLL.FixLink(Lcfj); Lcfj:=0
          | Tend: Kernel.BufRNum(B, TAG); PLL.FixLink(Lcfj); PLL.FixLink(Lfix); EXIT
          | Twend:  Kernel.BufRNum(B, TAG); PLL.FJ(Lfix); PLL.FixLink(Lcfj); PLC.Trap(18); PLL.FixLink(Lfix);
            IF class=UmopIs THEN PopDict; obj.typ:=typ END;
            EXIT
          ELSE  Statement END
        END
    | Tcase:
        Kernel.BufRNum(B, min); Kernel.BufRNum(B, max); Kernel.BufRNum(B, TAG);
        Input(exp); Compile(exp, x); PLC.Case(x, min, max, tab, L); Lfix:=0;
        LOOP
          CASE  TAG OF
          | Tcastrap: Kernel.BufRNum(B, TAG); PLC.Trap(16)
          | Tcaslbl1: PLL.FJ(Lfix); Kernel.BufRNum(B, lo); Kernel.BufRNum(B, TAG); PLL.CaseJump(L, tab, SHORT(lo-min), SHORT(lo-min))
          | Tcasrng1: PLL.FJ(Lfix); Kernel.BufRNum(B, lo); Kernel.BufRNum(B, hi); Kernel.BufRNum(B, TAG); PLL.CaseJump(L, tab, SHORT(lo-min), SHORT(hi-min))
          | Tcaslbl2: Kernel.BufRNum(B, lo); Kernel.BufRNum(B, TAG); PLL.CaseJump(L, tab, SHORT(lo-min), SHORT(lo-min))
          | Tcasrng2: Kernel.BufRNum(B, lo); Kernel.BufRNum(B, hi); Kernel.BufRNum(B, TAG); PLL.CaseJump(L, tab, SHORT(lo-min), SHORT(hi-min))
          | Tend: Kernel.BufRNum(B, TAG); PLL.FixLink(Lfix); EXIT
          ELSE  Statement END
        END
    | Twhile:
        Kernel.BufRNum(B, TAG); L:=PLL.pc; Input(exp); Compile(exp, x); PLL.CFJ(x, Lcfj);
        WHILE TAG#Tend  DO  Statement END;
        Kernel.BufRNum(B, TAG); PLL.BJ(L); PLL.FixLink(Lcfj)
    | Trepeat:
        Kernel.BufRNum(B, TAG); L:=PLL.pc;
        WHILE TAG#Tend  DO  Statement END;
        Kernel.BufRNum(B, TAG); Input(exp); Compile(exp, x); PLL.CBJ(x, L)
    | Tloop:
        Kernel.BufRNum(B, TAG); nxtobjExitChain:=ExitChain; ExitChain:=0; L:=PLL.pc;
        WHILE TAG#Tend  DO  Statement END;
        Kernel.BufRNum(B, TAG); PLL.BJ(L); PLL.FixLink(ExitChain); ExitChain:=nxtobjExitChain
    | Texit:
        Kernel.BufRNum(B, TAG); PLL.FJ(ExitChain)
    | Ttrap:
        Kernel.BufRNum(B, lo); Kernel.BufRNum(B, TAG); PLC.Trap(lo)
    ELSE  Input(stat);  (*entry, return, assignment or call*)
      IF  stat.safe THEN  PLL.CopyCode(stat.from, stat.to)  ELSE  stat.from:=PLL.pc; Compile(stat, dum); stat.to:=PLL.pc  END
    END
  END Statement;

(* error messages *)

  PROCEDURE Str(s: ARRAY OF CHAR);
    VAR i: INTEGER;
  BEGIN i:=0; REPEAT Modules.resMsg[Modules.resMsgLen]:=s[i]; INC(i); INC(Modules.resMsgLen) UNTIL s[i-1]=0X; DEC(Modules.resMsgLen);
  END Str;

  PROCEDURE Ch(ch: CHAR);
  BEGIN Modules.resMsg[Modules.resMsgLen]:=ch; INC(Modules.resMsgLen); Modules.resMsg[Modules.resMsgLen]:=0X
  END Ch;

  PROCEDURE Ln;
  BEGIN Modules.resMsg[Modules.resMsgLen]:=0DX; INC(Modules.resMsgLen); Modules.resMsg[Modules.resMsgLen]:=0X
  END Ln;

  PROCEDURE Clear;
  BEGIN Modules.resMsg[0]:=0X; Modules.resMsgLen:=0
  END Clear;

(* loading *)

  PROCEDURE BuildExpBlock(M: Modules.Module; obj: PLT.Object);
    TYPE ExportList = POINTER- TO ARRAY MAX(INTEGER) OF Modules.ExportDesc;
    VAR nofObj: INTEGER; obj2: PLT.Object; dsc: ExportList; typ: PLT.Struct;

    PROCEDURE ExportRecord(typ: PLT.Struct; VAR scope: Modules.ExportDesc);
      VAR nofFld: INTEGER; fld: PLT.Object; dsc: ExportList; old: Modules.ExportPtr;
    BEGIN
      IF typ.mod=M THEN
        IF typ.oref#0 THEN old:=SYS.VAL(Modules.ExportPtr, typ.oref);
          scope.nofExp:=old.nofExp; scope.dsc:=old.dsc;
        ELSE
          nofFld:=2; fld:=typ.dsc; WHILE fld#NIL DO (* mfix *)
            IF fld.vis#internal THEN INC(nofFld) END;
            fld:=fld.nxtobj;
          END;
          Kernel.AllocBlock(SYS.VAL(LONGINT, scope.dsc), -SIZE(Modules.ExportDesc)*nofFld);
          scope.nofExp:=nofFld; nofFld:=2; dsc:=SYS.VAL(ExportList, scope.dsc);
          PLT.FPrintTyp(typ); typ.oref:=SYS.ADR(scope);
          IF (typ.BaseTyp#NIL) & (typ.mod=M) THEN ExportRecord(typ.BaseTyp, dsc[0]) END;
          dsc[0].fp:=typ.pbfp; dsc[1].fp:=typ.pvfp; dsc[0].adr:=(typ.tdadr-M.code) DIV 2;
          fld:=typ.dsc; WHILE fld#NIL DO
            IF fld.vis#internal THEN
              dsc[nofFld].fp:=fld.fp; typ:=fld.typ;
              WHILE (typ#NIL) & ((typ.form=Comp) & (typ.comp#Record) OR (typ.form=Pointer)) DO typ:=typ.BaseTyp END;
              IF (typ#NIL) & (typ.form=Comp) & (typ.comp=Record) THEN ExportRecord(typ, dsc[nofFld]) END;
              INC(nofFld);
            END;
            fld:=fld.nxtobj;
          END;
        END
      END;
    END ExportRecord;

  BEGIN obj2:=obj; nofObj:=0;
    WHILE obj#NIL DO
      IF obj.vis#internal THEN PLT.FPrintObj(M, obj); INC(nofObj) END; obj:=obj.nxtobj;
    END;
    Kernel.AllocBlock(SYS.VAL(LONGINT, M.export.dsc), -SIZE(Modules.ExportDesc)*nofObj);
    M.export.nofExp:=nofObj; nofObj:=0; dsc:=SYS.VAL(ExportList, M.export.dsc);
    WHILE obj2#NIL DO
      IF obj2.vis#internal THEN dsc[nofObj].fp:=obj2.fp;
        IF obj2.mode=Var THEN dsc[nofObj].adr:=obj2.adr-M.data
        ELSIF obj2.mode=XProc THEN dsc[nofObj].adr:=(obj2.adr-M.code) DIV 2
        ELSE dsc[nofObj].adr:=0 END;
        IF (obj2.mode>XProc) OR (obj2.mode=Var) THEN typ:=obj2.typ;
          WHILE (typ#NIL) & ((typ.form=Comp) & (typ.comp#Record) OR (typ.form=Pointer)) DO typ:=typ.BaseTyp END;
          IF (typ#NIL) & (typ.form=Comp) & (typ.comp=Record) THEN ExportRecord(typ, dsc[nofObj]) END;
        END;
        INC(nofObj);
      END;
      obj2:=obj2.nxtobj;
    END;
  END BuildExpBlock;

  PROCEDURE CheckUseBlock(VAR B: Kernel.Buffer; M: Modules.Module; VAR res: INTEGER);
    VAR mod: Modules.Module; name: Modules.ModuleName;

    PROCEDURE FindObj(VAR obj: PLT.Object; name: ARRAY OF CHAR);
    BEGIN
      obj:=SYS.VAL(PLT.Object, mod.publics);
      WHILE (obj#NIL) & (obj.name#name) DO obj:=obj.nxtobj END;
    END FindObj;

    PROCEDURE FindField(VAR obj: PLT.Object; typ: PLT.Struct; name: ARRAY OF CHAR);
    BEGIN obj:=typ.dsc;
      WHILE (obj#NIL) & (obj.name#name) DO obj:=obj.nxtobj END;
    END FindField;

    PROCEDURE Err;
    BEGIN
      IF res=0 THEN Str(M.name); Str(" imports incompatible version of "); Str(mod.name); Str(": "); res:=16;
      ELSE Ch(9X) END;
    END Err;

    PROCEDURE CheckScope(scope: Modules.ExportDesc; level: INTEGER; typ: PLT.Struct);
      TYPE ExportList = POINTER- TO ARRAY MAX(INTEGER) OF Modules.ExportDesc;
      VAR fp, i: LONGINT; dsc: ExportList; typ2: PLT.Struct; obj: PLT.Object; tmpErr: BOOLEAN;
        n: Node;  (* mfix *)
    BEGIN tmpErr:=(level=EUerrScope);
      IF level=EUrecScope THEN (* do not insert fields here *)
        UNodeO(Uguard, flgNoLeft, typ, NIL, Global);
        UNodeO(Ueguard, flgNoLeft, typ, NIL, Global);
        UNodeO(UmopIs, flgNoLeft, PLT.booltyp, typ.strobj, Global);
      END;
      dsc:=SYS.VAL(ExportList, scope.dsc); i:=0;
      Kernel.BufRNum(B, fp); i:=-1;
      WHILE fp#EUEnd DO
        IF fp=EURecord THEN
          IF i=-1 THEN i:=0; typ2:=typ.BaseTyp END;
          IF tmpErr THEN CheckScope(dsc[i], EUerrScope, typ2) ELSE CheckScope(dsc[i], EUrecScope, typ2) END;
        ELSE Kernel.BufRString(B, name);
          IF level>=EUobjScope THEN tmpErr:=FALSE;
            i:=0; WHILE (i<scope.nofExp) & (dsc[i].fp#fp) DO INC(i) END;
            IF i>=scope.nofExp THEN Err; tmpErr:=TRUE; Ln;
              Ch(9X); obj:=NIL; Str(name); Str(" incompatible");
            ELSIF level=EUrecScope THEN FindField(obj, typ, name);
              IF obj.mode = Fld THEN
                UNodeO(Ufield, flgNoLeft, obj.typ, obj, Global)
              ELSE
                NNode(n, Uproc, typ, obj, NIL, NIL, Global);
                CallNode(n, UcallXPrc, obj.nofpar, obj.typ, obj, NIL, Global);
                CallNode(n, UcallXPrc, obj.nofpar, obj.typ, obj, NIL, Global); n.super := TRUE;
              END;
              typ2:=obj.typ;
            ELSE FindObj(obj, name);
              typ2:=obj.typ;
              IF (obj.mode=Var) OR (obj.mode=XProc) OR (obj.mode=Con) THEN
                GenNode(obj, typ2, obj.mode, External, Global);
              END;
            END;
          END;
          IF (obj#NIL) & (obj.mode#TProc) & ((obj.mode#XProc) & (obj.mode#Con) OR (level=EUrecScope)) THEN
            WHILE (typ2#NIL) & ((typ2.form=Comp) & (typ2.comp#Record) OR (typ2.form=Pointer)) DO
              IF typ2.form=Pointer THEN GenNode(obj, typ2, TypPointer, External, Global) END;
              typ2:=typ2.BaseTyp
            END;
          END;
        END;
        Kernel.BufRNum(B, fp);
      END;
    END CheckScope;

  BEGIN res:=0; Kernel.BufRString(B, name);
    WHILE (name#"") & (res=0) DO
      mod:=Modules.modList;
      WHILE (mod#NIL) & (mod.name#name) DO mod:=mod.link END;
      IF mod#NIL THEN CheckScope(mod.export, 0, NIL) END;
      Kernel.BufRString(B, name);
    END;
  END CheckUseBlock;


  PROCEDURE Load*(VAR buf: Kernel.Buffer; mod: Modules.Module; globals: PLT.Object; b, a: LONGINT);
    VAR block: LONGINT; res: INTEGER;
  BEGIN B:=buf; M:=mod; N:=NNN; below:=-1; above:=Ttrap+1;
    IF  (b > MaxBelow) OR (a > MaxAbove)  THEN  Kernel.AllocBlock(block, (b+a-1)*SIZE(NodeDesc)); N:=block+((b-1)*SIZE(NodeDesc)) END;

    UNodeO(UmopConv, flgNoLeft, PLT.chartyp, NIL, Global);
    UNodeO(UmopConv, flgNoLeft, PLT.sinttyp, NIL, Global);
    UNodeO(UmopConv, flgNoLeft, PLT.inttyp, NIL, Global);
    UNodeO(UmopConv, flgNoLeft, PLT.linttyp, NIL, Global);
    UNodeO(UmopConv, flgNoLeft, PLT.realtyp, NIL, Global);
    UNodeO(UmopConv, flgNoLeft, PLT.lrltyp, NIL, Global);
    UNodeO(UmopConvSet, flgNoLeft, PLT.settyp, NIL, Global);

    GenNodes(globals, Internal, Global);
    res:=0;
    CheckUseBlock(B, mod, res);
    IF res=0 THEN
      INC(PLL.level);
      Kernel.BufRNum(B, TAG); WHILE TAG#Tbegin  DO  Statement END;  (*nested*)
      DEC(PLL.level); body:=SYS.VAL(Modules.Command, PLL.codeBase+2*LONG(PLL.pc));
      PLL.InitTypDescs;
      Kernel.BufRNum(B, TAG); WHILE TAG#Tend  DO  Statement END;  (*body*)
      PLC.ReturnFromMod;
      IF  (b > MaxBelow) OR (a > MaxAbove)  THEN  Kernel.DeAllocBlock(block)  END;
      buf:=B;
      BuildExpBlock(mod, globals);
    END;
    Modules.res:=res;
  END Load;


  PROCEDURE EnableAssert*;
  BEGIN assert:=TRUE
  END EnableAssert;

  PROCEDURE DisableAssert*;
  BEGIN assert:=FALSE
  END DisableAssert;

  PROCEDURE EnableRefs*;
  BEGIN refs:=TRUE
  END EnableRefs;

  PROCEDURE DisableRefs*;
  BEGIN refs:=FALSE
  END DisableRefs;

BEGIN
  constNodeOT[Char]:=TconstChar;
  constNodeOT[SInt]:=TconstSInt; constNodeOT[Int]:=TconstInt; constNodeOT[LInt]:=TconstLInt;
  constNodeOT[Real]:=TconstReal; constNodeOT[LReal]:=TconstLReal; constNodeOT[Set]:=TconstSet;
  constNodeOT[String]:=TconstString; constNodeOT[NilTyp]:=TconstNil;

  contyp[TconstChar]:=PLT.chartyp; contyp[TconstSet]:=PLT.settyp;
  contyp[TconstSInt]:=PLT.sinttyp; contyp[TconstInt]:=PLT.inttyp; contyp[TconstLInt]:=PLT.linttyp;

  NEW(nilNode); nilNode.tag:=TconstNil; nilNode.typ:=PLT.niltyp; nilNode.global:=Global; NEW(nilNode.obj);
  NEW(falseNode); falseNode.tag:=TconstFalse; falseNode.typ:=PLT.booltyp; falseNode.global:=Global; NEW(falseNode.obj);
  NEW(trueNode); trueNode.tag:=TconstTrue; trueNode.typ:=PLT.booltyp; trueNode.global:=Global; NEW(trueNode.obj); trueNode.obj.ival:=-1;
  Kernel.AllocBlock(NNN, (MaxBelow+MaxAbove-1)*SIZE(NodeDesc)); INC(NNN, (MaxBelow-1)*SIZE(NodeDesc))
END OPLV.