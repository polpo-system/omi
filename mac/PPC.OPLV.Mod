(* ETH Oberon, Copyright 2000 ETH Zürich Institut für Computersysteme, ETH Zentrum, CH-8092 Zürich.
Refer to the general ETH Oberon System license contract available at: http://www.oberon.ethz.ch/ *)

MODULE OPLV;  (*mf 15.5.94 / od Feb 95 / tk 30.6.96 *)

  (* 30.7.96  Method support (mfix) / WITH correction *)

  IMPORT
    SYS:=SYSTEM, Kernel, Modules, PLT:=OPLT, PLL:=OPLL, PLC:=OPLC;

  CONST
    MaxAbove=3072;  (* 16384 *)
    MaxBelow=768; (* 4096 *)

    Var=1; Par=2; VarPar=3; Con=4; Fld=5; LProc=6; XProc=7; TProc = 14; TypDynArr=8; TypArray=9; TypPointer=10; TypRecord=11;
    TypProcTyp=12;
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

    flgOK=0; flgNoLeft=-1; flgNoRight=-2; flgEnter=-3; Local=FALSE; Global=TRUE; Internal=FALSE; External=TRUE;

    Head = 12; Based = 14; Indexed = 15; Reg = 16; RegSI = 17; FReg = 18; Cond = 19;
    memTag = 1024;

    internal=0; external=1;

  (*Export/Use Section*)
    EUEnd = 0;  EURecord = 1; EUobjScope = 0;   EUrecScope = 1; EUerrScope = -1;

  TYPE
    Node=POINTER TO NodeDesc;
    NodeDesc=RECORD
      left, right: Node;
      tag: LONGINT; flag, subflg: SHORTINT;
      typ: PLT.Struct; obj: PLT.Object;
      safe, global: BOOLEAN; from, to: PLL.Label;
      filler: LONGINT
    END;


  VAR
    assert, refs: BOOLEAN;
    body*: LONGINT;
    TAG: LONGINT; B: Kernel.Buffer; M: Modules.Module;
    nilNode, falseNode, trueNode: Node;
    astk, bstk: ARRAY 64 OF LONGINT; dsp: INTEGER;  (*node dictionary stack*)
    NNN, N, above, below: LONGINT;  (*node memory*)
    constNodeOT: ARRAY NilTyp+1 OF SHORTINT;  (*node tags by form*)
    contyp: ARRAY TconstSet+1 OF PLT.Struct;  (*constant types by tag*)

    padr, vadr : LONGINT; f : INTEGER; levCall : INTEGER;

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
    n.tag:=tag; n.flag:=0; n.subflg:=0; n.typ:=typ; n.obj:=obj; n.left:=left; n.right:=right; n.safe:=FALSE; n.global:=global; p:=n
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
              CallNode(n, UcallXPrc, fld.nofpar, fld.typ, fld, NIL, global); n.safe := TRUE;
            ELSE
              CallNode(n, UcallLPrc, fld.nofpar, fld.typ, fld, NIL, global);
              CallNode(n, UcallLPrc, fld.nofpar, fld.typ, fld, NIL, global); n.safe := TRUE;
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
  PROCEDURE ^ Compile(n: Node; VAR x: PLL.Item; rt : LONGINT);

  PROCEDURE ActualPar (VAR ap : PLL.Item; formal: PLT.Object; actual : Node);
    VAR
      dest, form, mode, rt, n: LONGINT;
      y, z, desc, tag: PLL.Item;
      typ, atyp: PLT.Struct;
      ParReg, ind: BOOLEAN;
      c : INTEGER;

    PROCEDURE Alloc (ps, vs: LONGINT);
    BEGIN
      IF (formal^.mode # VarPar) & (form IN {Real, LReal}) & (f <= 13) THEN
        dest := -1-(FReg*32+f); INC(f)
      ELSIF (padr + ps <= 11*4) THEN
        dest := -1-(Reg*32+padr DIV 4);
      ELSE dest := padr+12
      END;
      IF vs = 0 THEN formal^.linkadr := memTag+padr-12
      ELSE PLL.Align(vadr, PLL.Base(typ)); formal^.linkadr := vadr; INC(vadr, vs)
      END;
      INC(padr, ps)
    END Alloc;

  BEGIN
    dest := formal^.adr; typ := formal^.typ; form := typ^.form; atyp := actual^.typ;

    IF dest=0 THEN
      c:=typ.comp;
      IF c = DynArr THEN Alloc(typ^.size, 0);
      ELSIF (formal^.mode = VarPar) THEN
        IF c = Record THEN Alloc(8, 0)
        ELSE Alloc(4, 0)
        END
      ELSE
        IF c IN {Record, Array} THEN Alloc(4, typ^.size)
        ELSIF form IN {LReal, ProcTyp} THEN Alloc(8, 0)
        ELSE Alloc(4, 0)
        END
      END;
    END;

    IF dest < 0 THEN rt := -1-dest; mode := rt DIV 32; rt := rt MOD 32; n := rt;
      IF ((typ^.form IN {Real, LReal}) & (formal^.mode # VarPar)) # (atyp^.form IN {Real, LReal}) THEN n := -1 END
    ELSE rt := -1; n := rt; mode := Based
    END;
    IF (atyp.comp=DynArr) & (rt>0) THEN PLL.LockParR(rt+1) END;
    IF (form=ProcTyp) & (formal.mode#VarPar) & (rt>0) THEN PLL.LockParR(rt); PLL.LockParR(rt+1); n:=-1 END;
    IF form = ProcTyp THEN PLL.fixProc:=actual.obj END;
    ap.Tjmp := 0; ap.Fjmp := 0;
    Compile(actual, ap, n);
    desc:=ap; ap.dreg:=-1; z:=ap;
    ind := (formal^.mode = VarPar) OR (form IN {String, Comp});
    IF ind THEN
      IF atyp^.comp # DynArr THEN PLC.LoadAddr(ap, rt) ELSE tag := ap END
    END;
    y := ap;
    IF ~ind THEN y.typ := typ END;
    ParReg := dest < 0;
    IF ParReg THEN y.mode := SHORT(SHORT(mode)); y.reg := rt;
    ELSE y.mode := Based; y.reg := 1 (*SP*); y.offset := dest
    END;
    IF atyp^.comp # DynArr THEN PLC.Assign(y, ap) END;
    IF mode = Reg THEN
      PLL.LockParR(rt);
      IF form = ProcTyp THEN PLL.LockParR(rt+1) END
    ELSIF mode = FReg THEN
      PLL.LockParF(rt)
    END;
    IF (formal^.mode = VarPar) & (form = Comp) & (typ^.comp = Record) THEN
      IF actual^.tag = Tderef THEN
        ASSERT(ap.mode = Reg);
        ap.mode := Based; ap.offset := -4
      ELSIF (actual^.tag = UvarparIndirect) OR (actual.tag = Uguard) (* OR (actual^.tag = UvarIndirect) *) THEN
        ap := z; ASSERT(ap.mode IN {Based, VarPar});
        IF ap.mode = Based THEN ap.mode := Reg; INC(ap.reg) ELSE ap.mode := Var; INC(ap.offset, 4) END
      ELSE
        ap.mode := Var; typ := actual^.typ; ap.mnolev := -PLT.GetTypMno(typ); ap.offset := typ^.tdadr
      END;
      ap.typ := PLT.linttyp; ASSERT(y.mode IN {Reg, Based});
      IF ParReg THEN INC(y.reg) ELSE INC(y.offset, 4) END;
      PLC.Assign(y, ap);
      IF ParReg THEN PLL.LockParR(y.reg) END
    ELSIF (form = Comp) & (typ^.comp = DynArr) THEN
      IF atyp^.comp # DynArr THEN
        n := typ^.n; typ := typ^.BaseTyp;
        WHILE n >= 0 DO
          ap.mode := Con; ap.typ := PLT.linttyp;
          IF atyp^.form = String THEN ap.offset := ap.adr
          ELSIF (typ.form = Char) & (atyp.comp # DynArr) & (atyp.comp # Array) THEN ap.offset := atyp.size
          ELSE ap.offset := atyp^.n
          END;
          IF ParReg THEN INC(y.reg) ELSE INC(y.offset, 4) END;
          PLC.Assign(y, ap);
          IF ParReg THEN PLL.LockParR(y.reg) END;
          typ := typ^.BaseTyp; atyp := atyp^.BaseTyp; DEC(n)
        END
      ELSE
        dest := rt; z := y; (* dest of adr part *)
        n := typ^.n; typ := typ^.BaseTyp; ap.typ := PLT.linttyp;
        y.typ := PLT.linttyp; mode := desc.dmode; ap.mode := SHORT(SHORT(mode)); ap.reg := desc.dreg;
        WHILE n >= 0 DO
          IF ParReg THEN INC(y.reg); rt := y.reg ELSE INC(y.offset, 4); rt := -1 END;
          IF mode = Reg THEN ap.reg := desc.dreg+atyp^.offset DIV 4
          ELSE ap.mode := SHORT(SHORT(mode)); ap.reg := desc.dreg; ap.offset := desc.adr+atyp^.offset
          END;
          PLC.Assign(y, ap);
          IF ParReg THEN PLL.LockParR(rt) END;
          typ := typ^.BaseTyp; atyp := atyp^.BaseTyp; DEC(n)
        END;
        PLC.LoadAddr(tag, dest); z.typ := PLT.linttyp; PLC.Assign(z, tag)
      END
    END;
    IF desc.dreg # -1 THEN PLL.UnholdTempR(desc.dreg); PLL.FreeTempR(desc.dreg) END;
  END ActualPar;

  PROCEDURE ArgSize (par: PLT.Object): LONGINT;
    VAR s: LONGINT; c: SHORTINT; typ: PLT.Struct;
  BEGIN s := 0;
    WHILE par # NIL DO
      typ := par^.typ; c := typ^.comp;
      IF c = DynArr THEN INC(s, typ^.size)
      ELSIF par^.mode = VarPar THEN
        IF c = Record THEN INC(s, 8) ELSE INC(s, 4) END
      ELSE
        IF c IN {Record, Array} THEN INC(s, 4)
        ELSIF typ^.form = LReal THEN INC(s, 8 + s MOD 8)
        ELSIF typ^.form = ProcTyp THEN INC(s, 8)
        ELSE INC(s, 4)
        END
      END;
      par := par.nxtobj;
    END;
    PLL.Align(s, 8); RETURN s*10000H
  END ArgSize;

  PROCEDURE Dim (VAR x, nofel: PLL.Item; n: Node; typ: PLT.Struct; nofdim, rt: LONGINT);
    VAR
      len, y: PLL.Item;
      btyp: PLT.Struct;
  BEGIN rt := -1;
    IF nofdim = 1 THEN
      PLL.LockParR(3) (*tag*); PLL.LockParR(4) (*nofelem*); PLL.LockParR(5) (*nofdim*);
      IF typ^.BaseTyp^.form IN {Bool, Char, SInt} THEN rt := 4 END
    END;
    Compile(n.left, len, rt); IF len.mode # Con THEN PLC.Load(len, -1); PLL.HoldTempR(len.reg) END;
    IF len.mode # Con THEN PLC.GenDimTrap(len) END;
    IF nofdim = 1 THEN nofel := len ELSE PLC.MulDim(nofel, len, 4) END;
    IF n^.right # NIL THEN
      Dim(x, nofel, n^.right, typ^.BaseTyp, nofdim+1, rt)
    ELSE
      btyp := typ^.BaseTyp; rt := 1;
      WHILE btyp^.comp = Array DO
        rt := rt*btyp^.n; btyp := btyp^.BaseTyp
      END;
      IF rt # 1 THEN
        y.mode := Con; y.offset := rt; y.typ := PLT.linttyp; PLC.MulDim(nofel, y, 4)
      END;
      PLC.NewArr(x, nofel, nofdim, btyp, rt); PLL.HoldTempR(x.reg);
    END;
    ASSERT(x.mode = Reg);
    y := x; y.mode := Based; y.offset := 8;
    PLC.SetDim(y, len, typ);
    IF nofdim = 1 THEN PLL.UnholdTempR(x.reg) END;
  END Dim;

  PROCEDURE Call(n: Node; rt : LONGINT);
    VAR tag: LONGINT; left, right : Node; parSize: LONGINT;
      x,y : PLL.Item; proc, rcv: Node;  (* mfix *)
  BEGIN
    tag:=n.tag; left:=n.left; right:=n.right;
    IF (n.flag=0) & ((n.tag=UcallPrcV) OR (n.tag=UcallFncV) OR (n.tag=UcallRFncV)) THEN
      proc:=n; WHILE proc.subflg>0 DO proc:=proc.left END;
      PLL.ParamAdr(proc.obj)
    END;
    IF n.subflg=0 THEN
      padr:=3*4; vadr:=0; f:=1;
      IF (tag=UcallXFnc) OR (tag=UcallLFnc) OR (tag=UcallFncV) THEN END;
    ELSE
      Call(left, rt); ActualPar(x, n.obj, right)
    END;
    IF n.flag=0 THEN proc:=n;
      INC(levCall);
      WHILE proc.subflg>0 DO rcv := proc; proc:=proc.left END;
      parSize:=proc.obj.ival;
      IF parSize=-1 THEN parSize:=ArgSize(proc.obj); proc.obj.ival:=parSize END;
      y.mnolev:=PLT.GetObjMno(proc.obj);
      y.adr:=proc.obj.linkadr;  y.offset:=proc.obj.adr; y.mode:=proc.obj.mode; y.typ := proc.obj.typ;
      IF proc.obj.mode = TProc THEN
        y.offset := proc.obj.adr DIV 10000H; IF proc.safe THEN y.dmode := 1 ELSE y.dmode := 0 END;
        PLC.GetMethod(y, rcv.right.typ, rcv.obj.typ.form = Pointer, y.dmode = 1);
      END;
      CASE  n.tag OF
        | UcallXPrc, UcallXFnc, UcallXRFnc: PLC.Call(y, parSize DIV 10000H);
        | UcallLPrc, UcallLFnc, UcallLRFnc: PLC.Call(y, parSize DIV 10000H);
        | UcallPrcV, UcallFncV, UcallRFncV:  PLL.ParamAdr(proc.obj); Compile(proc.left, x, -1);
          PLC.Call(x, parSize DIV 10000H);
      END;
      IF y.mode IN {LProc, XProc} THEN proc.obj.adr:=y.offset; proc.obj.linkadr:=y.adr END;
      IF levCall=1 THEN PLL.FreePar END;
      DEC(levCall);
    END;
  END Call;

  PROCEDURE Compile(n: Node; VAR x: PLL.Item; rt : LONGINT);
    VAR tag: LONGINT; left, right: Node; obj, obj0: PLT.Object; y, z: PLL.Item;
      t : LONGINT; mode : INTEGER; l : PLL.Label; VarRec : BOOLEAN;
      saved : PLL.SaveDesc;
  BEGIN
    x.dreg := -1; y.dreg := -1; z.dreg := -1;
    tag:=n.tag; left:=n.left; right:=n.right; obj:=n.obj;
    CASE tag OF (*for expressions, the type of Node parameter is guaranteed to be the correct result type*)
    | TconstNil..TconstSet: x.mode:=Con; x.typ:=n.typ; x.offset:=obj.ival;
    | TconstReal: x.mode:=Var; PLL.AllocConst(obj.ival, 4, x.offset, 4); x.mnolev:=0; x.adr:=0;
    | TconstLReal: x.mode:=Var; PLL.AllocConst(obj.rval, 8, x.offset, 4); x.mnolev:=0; x.adr:=0;
    | TconstString:
        IF PLT.GetObjMno(obj)#0 THEN  NEW(obj0); obj0^:=obj^; n.obj:=obj0; obj:=obj0  END;  (* reallocate string *)
        IF obj.adr=0 THEN PLL.AllocConst(obj.xval^, SHORT(obj.ival), obj.adr, 4) END;
        x.mode:=Var; x.adr:=obj.ival; x.mnolev:=0; x.offset:=obj.adr;
    | UvarGlobal, UvarDirect: x.typ:=n.typ; x.mnolev := PLT.GetObjMno(obj);
      t:=obj.linkadr; IF x.mnolev<0 THEN t:=obj.adr END;
      IF t<-1 THEN t:=-1-t; mode:=SHORT(t DIV 32); x.reg:=t MOD 32; x.mode:=SHORT(mode);
      ELSE x.offset:=t; x.adr := obj.adr; mode := obj^.mode; x.mode := SHORT(mode); x.reg := 0 END;
      x.dmode := SHORT(mode); x.dreg := -1;
      IF (n^.typ^.comp = DynArr) & (x.dreg = -1) THEN PLC.DynArrItem(x, rt) END;
    | UvarIndirect, UvarparIndirect: x.typ:=n.typ; x.mnolev := PLT.GetObjMno(obj);
      t:=obj.linkadr; IF x.mnolev<0 THEN t:=obj.adr END;
      IF t<-1 THEN t:=-1-t; mode:=SHORT(t DIV 32); x.reg:=t MOD 32;
        IF (mode=Reg)  &  (tag=UvarparIndirect)  &  (n.typ.comp#DynArr) THEN x.mode:=Based; x.offset:=0
        ELSE x.mode:=SHORT(mode) END;
      ELSE x.offset:=t; x.adr := obj.adr; mode := obj^.mode; x.mode := SHORT(mode); x.reg := 0 END;
      x.dmode := SHORT(mode); x.dreg := -1;
      IF (n^.typ^.comp = DynArr) & (x.dreg = -1) THEN PLC.DynArrItem(x, rt) END;
    | Ufield: x.typ:=n.typ; t:=rt; IF (n.typ.form IN {Real, LReal}) OR (n.typ.form=ProcTyp) & (rt>12) THEN t:=-1 END;
      Compile(left, x, t); PLC.Field(x, obj.adr, -1)
    | Tderef: x.typ:=n.typ;
      Compile(left, x, rt); PLC.Deref(x, rt);
      x.typ:=n.typ;
      IF n.typ.comp=DynArr THEN x.dmode:=Based;
        IF (x.dreg = -1) THEN PLC.DynArrItem(x, rt) END;
      END;
    | Tindex: x.typ:=n.typ; Compile(left, x, -1); Compile(right, y, -1); PLC.Index(x, y, -1)
    | Uguard:
      x.typ:=n.typ; VarRec:= (left.tag = UvarparIndirect) & (left.typ.comp = Record);
      Compile(left, x, rt); PLC.TypTest(x, n.typ, TRUE, FALSE, VarRec)
    | Ueguard:
      x.typ:=n.typ; VarRec:= (left.tag = UvarparIndirect) & (left.typ.comp = Record);
      Compile(left, x, rt); PLC.TypTest(x, n.typ, TRUE, TRUE, VarRec)
    | Uproc:
      x.typ:=n.typ; x.mnolev := PLT.GetObjMno(obj); x.mode:=obj.mode; x.offset:=obj.adr; x.adr:=obj.linkadr; x.reg:=0;
      IF x.mode = TProc THEN x.offset := (*mthno*) obj.adr DIV 10000H; IF n.safe THEN x.dmode := 1 ELSE x.dmode := 0 END END;
    | UmopIs: x.dreg := -1; y.dreg := -1;
      Compile(left, x, -1); y:=x; VarRec:= (left.tag = UvarparIndirect) & (left.typ.comp = Record);
      PLC.TypTest(x, obj.typ, FALSE, FALSE, VarRec)
    | UmopConv: Compile(left, x, -1); PLC.Convert(x, n.typ, rt, TRUE)
    | UmopConvSet: Compile(left, x, -1); PLC.SetElem(x, rt)
    | TmopNot: l := x.Tjmp; x.Tjmp := x.Fjmp; x.Fjmp := l; Compile(left, x, -1); PLC.Not(x, rt)
    | TmopMinus: Compile(left, x, -1); PLC.Neg(x, rt)
    | TmopAbs: Compile(left, x, -1); PLC.Abs(x, rt)
    | TmopCap: Compile(left, x, -1); PLC.Cap(x, rt)
    | TmopOdd: Compile(left, x, -1); PLC.Odd(x)
    | TdopTimes: Compile(left, x, -1); Compile(right, y, -1); PLC.Times(x, y, rt)
    | TdopSlash: Compile(left, x, -1); Compile(right, y, -1); PLC.Slash(x, y, rt)
    | TdopPlus: Compile(left, x, -1); Compile(right, y, -1); PLC.Plus(x, y, rt) (* MULADD optm fehlt *)
    | TdopMinus: Compile(left, x, -1); Compile(right, y, -1); PLC.Minus(x, y, rt) (* MULADD optm fehlt *)
    | TdopDiv: Compile(left, x, -1); Compile(right, y, -1); PLC.Div(x, y, rt)
    | TdopMod: Compile(left, x, -1); Compile(right, y, -1); PLC.Mod(x, y, rt)
    | TdopAnd:
      y.Fjmp := x.Fjmp; y.Tjmp := 0; Compile(left, y, -1); PLC.PutCondBranch(y, FALSE); PLC.SetLabel(y.Tjmp);
      x.Fjmp := y.Fjmp; Compile(right, x, -1)
    | TdopOr: y.Tjmp := x.Tjmp; y.Fjmp := 0;
      Compile(left, y, -1); PLC.PutCondBranch(y, TRUE); PLC.SetLabel(y.Fjmp); x.Tjmp := y.Tjmp; Compile(right, x, -1)
    | TdopEql..TdopGeq: Compile(left, x, -1); Compile(right, y, -1); PLC.Compare(x, y, SHORT(tag))
    | TdopIn: Compile(left, x, -1); Compile(right, y, -1); PLC.In(x, y)
    | TdopAsh: Compile(left, x, -1); Compile(right, y, -1); PLC.Ash(x, y, rt)
    | TdopMsk: Compile(left, x, -1); Compile(right, y, -1); PLC.Msk(x, y, rt)
    | TdopLen: Compile(left, x, -1); Compile(right, y, -1); PLC.Len(x, y, rt)
    | Tupto: Compile(left, x, -1); Compile(right, y, rt); PLC.SetRange(x, y, rt)
    | TasgnNewfn:
      PLL.LockParR(3); PLL.LockParR(4); PLL.LockParR(5);Compile(left, x, -1);
      IF right#NIL THEN Dim(y, z, right, left.typ.BaseTyp, 1, -1)
      ELSE PLC.NewRec(y, x.typ.BaseTyp, -1); END;
      PLC.Assign(x, y)
    | UasgnAssignOther, UasgnAssignBool:
      Compile(left, x, -1); IF (x.mode IN {Reg, FReg}) & ((x.mode=FReg)=(right.typ.form IN {Real, LReal})) THEN
      rt:=x.reg ELSE rt:=-1 END; y.Tjmp := 0; y.Fjmp := 0; Compile(right, y, rt); PLL.fixProc:=right.obj; PLC.Assign(x, y)
    | TasgnIncfn: Compile(left, x, -1); Compile(right, y, -1); PLC.Increment(x, y, TRUE)
    | TasgnDecfn: Compile(left, x, -1); Compile(right, y, -1); PLC.Increment(x, y, FALSE)
    | TasgnInclfn: Compile(left, x, -1); Compile(right, y, -1); PLC.Include(x, y);
    | TasgnExclfn: Compile(left, x, -1); Compile(right, y, -1); PLC.Exclude(x, y);
    | TasgnCopyfn: Compile(left, x, -1); Compile(right, y, -1); PLC.Copy(x, y)
    | Uenter: (*do nothing*)
    | UcallXPrc, UcallLPrc, UcallPrcV: Call(n, rt)
    | UcallXFnc, UcallLFnc, UcallFncV, UcallXRFnc, UcallLRFnc, UcallRFncV:
      PLC.SaveRegisters(x, saved);
      Call(n, rt); x.typ:=n.typ; x.dreg:=-1;
      IF x.typ.form IN {Real, LReal} THEN x.mode:=FReg; x.reg:=1 ELSE x.mode:=Reg; x.reg:=3 END;
      PLC.RestoreRegisters(x, saved, -1)
    | Ureturn0: x.mode:=Head; PLC.Return(x)
    | Ureturn1: IF obj.typ.form IN {Real, LReal} THEN rt := 1; x.mode := FReg ELSE rt := 3; x.mode := Reg END;
      y.Tjmp := 0; y.Fjmp := 0; y.dreg := -1;
      Compile(left, y, -1); x.typ:=obj.typ; x.reg:=rt; PLC.Assign(x, y);
      PLC.Return(x);
    END;
    x.typ:=n.typ;
  END Compile;

  PROCEDURE Enter1(n: Node; locs : PLT.Object);
    VAR
      ralloc, falloc, calloc, fsize, adr: LONGINT; p, v: PLT.Object;

    PROCEDURE Relocate (p: PLT.Object);
      VAR typ: PLT.Struct; form, comp, nrReg: LONGINT;
    BEGIN
      typ := p^.typ; form := typ^.form;
      IF (p^.mode = VarPar)   THEN
        IF form = Comp THEN comp := typ^.comp;
          IF comp = DynArr THEN nrReg := typ^.n+2 ELSIF comp = Record THEN nrReg := 2 ELSE nrReg := 1 END
        ELSE nrReg := 1 END;
        IF ralloc-nrReg > 11 THEN DEC(ralloc, nrReg); p^.linkadr := -1-(ralloc+1+Reg*32) END
      ELSE
        CASE form OF
          Char, SInt, Int, LInt, Set, Pointer:
            IF ralloc > 12 THEN p^.linkadr := -1-(ralloc+Reg*32); DEC(ralloc) END
        |  Real, LReal:
            IF falloc > 13 THEN p^.linkadr := -1-(falloc+FReg*32); DEC(falloc) END
        |  Bool:
            IF calloc > 7 THEN p^.linkadr := -1-(calloc+Cond*32); DEC(calloc) END
        |  Comp:
            IF typ^.comp = DynArr THEN nrReg := typ^.n+2;
              IF ralloc-nrReg > 11 THEN DEC(ralloc, nrReg); p^.linkadr := -1-(ralloc+1+Reg*32) END
            END
        |  ProcTyp:
            IF ralloc > 13 THEN DEC(ralloc, 2); p^.linkadr := -1-(ralloc+1+Reg*32) END
        ELSE END
      END
    END Relocate;

  BEGIN
    p := n^.obj;
    IF p # NIL THEN
      ralloc := 30; falloc := 31; calloc := 19; v := p.par;
      WHILE v # NIL DO
        IF (v^.adr < 0) & v^.leaf THEN Relocate(v) END;
        (* IF (v^.adr < 0)  & (v.mode=Par)  THEN Relocate(v)  END; *)
        v := v.nxtobj
      END;
      v := locs;
      WHILE (v # NIL) & (v # p.par) DO
        IF v^.leaf THEN Relocate(v) END;
        v := v.nxtobj
      END;
      fsize := p.intval2+(31-ralloc)*4+(31-falloc)*8+6*4; PLL.Align(fsize, 8);
      v := p.par;
      WHILE v # NIL DO
        adr := v^.linkadr;
        IF (adr >= 0) & ((v.mode = VarPar) (* OR (v.mode=Par) *) OR (v.typ.form # Comp) OR (v.typ.comp = DynArr)) THEN
          v^.linkadr := adr-memTag+fsize
        END;
        v := v.nxtobj
      END;
      p.ival := p.ival+ralloc*1024+falloc*32+calloc; p.intval2 := fsize-6*4
    END
  END Enter1;

  PROCEDURE Enter(n: Node);
    VAR proc, locals : PLT.Object; dum: Node; typ: PLT.Struct;
  BEGIN
    proc:=n.obj; typ:=proc.typ; (* proc.leaf:=FALSE; *)
    PushDict; INC(PLL.level);
    IF typ=PLT.notyp THEN NNode(dum, Ureturn0, NIL, proc, NIL, NIL, Local)
    ELSE UNodeO(Ureturn1, flgNoLeft, typ, proc, Local) END;
    locals:=proc.par; PLT.ReadScope(B, M, SHORT(PLL.level), locals, Local);
    IF refs THEN proc.locals:=locals ELSE proc.locals:=proc.par END;
    PLL.Traverse(locals); PLL.VarAdr(locals, proc.intval2); Enter1(n, locals);
    GenNodes(locals, Internal, Local);
    Kernel.BufRNum(B, TAG); WHILE TAG#Tbegin DO Statement END;  (*nested*)
    PLC.Enter(proc, locals);
    Kernel.BufRNum(B, TAG); WHILE TAG#Tend DO Statement END; (*body*)
    PLC.Leave(proc); DEC(PLL.level);
    (* PLL.OutRefName(proc.name); PLL.OutRefs(locals); *)
    PopDict;
  END Enter;

  PROCEDURE RString(VAR b: Kernel.Buffer; VAR string: ARRAY OF CHAR; VAR len: LONGINT);
    VAR i: INTEGER;
  BEGIN Kernel.BufRString(b, string); i:=0; WHILE string[i]#0X  DO  INC(i)  END;  len:=i+1
  END RString;

  PROCEDURE Input(VAR n: Node);
    VAR tag: LONGINT; left, right, par, h: Node; obj, sent: PLT.Object; restyp: PLT.Struct; match, remain: SHORTINT; r: LONGREAL; sr: REAL;
  BEGIN tag:=TAG;
    CASE  tag OF
    | TconstNil:  n:=nilNode; Kernel.BufRNum(B, TAG)
    | TconstFalse:  n:=falseNode; Kernel.BufRNum(B, TAG)
    | TconstTrue: n:=trueNode; Kernel.BufRNum(B, TAG)
    | TconstChar..TconstLInt:
        NEW(obj); Kernel.BufRNum(B, obj.ival); Kernel.BufRNum(B, TAG);
        NNode(n, tag, contyp[tag], obj, NIL, NIL, Global)
    | TconstSet:
        NEW(obj); Kernel.BufRNum(B, obj.ival); obj.ival:=PLT.FlipSet(obj.ival); Kernel.BufRNum(B, TAG);
        NNode(n, tag, contyp[tag], obj, NIL, NIL, Global)
    | TconstReal:
        NEW(obj); Kernel.BufRIEEE4(B, sr); obj.ival:=SYS.VAL(LONGINT, sr); Kernel.BufRNum(B, TAG);
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
        IF left.typ=PLT.booltyp THEN NNode(n, UasgnAssignBool, NIL, NIL, left, right, left.global&right.global)
        ELSE NNode(n, UasgnAssignOther, NIL, NIL, left, right, left.global&right.global) END
    | TasgnIncfn..TasgnCopyfn:
        Kernel.BufRNum(B, TAG); Input(left); Input(right);
        NNode(n, tag, NIL, NIL, left, right, left.global&right.global)
    | Tcall:
        Kernel.BufRNum(B, TAG); Input(left); restyp:=left.typ.BaseTyp; match:=0; remain:=SHORT(left.typ.nofdsc);
        NEW(sent); sent.par:=left.typ.dsc; CallNode(n, UcallPrcV, remain, restyp, sent, left, left.global);
        WHILE remain > 0 DO Input(par); INC(match); DEC(remain);
          PNode(n, remain, match, par, n.global&par.global)
        END
    ELSE
        n:=SYS.VAL(Node, N+tag*SIZE(NodeDesc));
        CASE n.flag OF
        | flgOK: Kernel.BufRNum(B, TAG)
        | flgNoLeft: Kernel.BufRNum(B, TAG); Input(left); NNode(n, n.tag, n.typ, n.obj, left, n.right, left.global&n.global)
        | flgNoRight: Kernel.BufRNum(B, TAG); Input(right); NNode(n, n.tag, n.typ, n.obj, n.left, right, n.global&right.global)
        | flgEnter: Enter(n)
        ELSE
          Kernel.BufRNum(B, TAG); match:=n.subflg; remain:=n.flag;  (*params*)
          WHILE remain > 0 DO Input(par); INC(match); DEC(remain); PNode(n, remain, match, par, n.global&par.global)  END
        END
    END
  END Input;


  PROCEDURE Statement;
    VAR exp, stat: Node; x, dum: PLL.Item; L, Lfix : PLL.Label; obj: PLT.Object; typ: PLT.Struct; t: Node;
      min, max, lo, hi, tno: LONGINT; table : LONGINT; bool : BOOLEAN; tag, class: LONGINT;
  BEGIN
    CASE TAG OF
    | Tassert:
        Kernel.BufRNum(B, tno); Kernel.BufRNum(B, TAG); Input(exp);
        IF assert THEN
          x.Tjmp := 0; x.Fjmp := 0; Lfix:=0;
          Compile(exp, x, -1); PLC.PutCondBranch(x, FALSE);
          PLC.SetLabel(x.Tjmp); PLC.Trap(SHORT(tno));
          PLC.SetLabel(x.Fjmp); PLC.SetLabel(Lfix);
        END
    | Tif, Twith: tag:=TAG;
        Kernel.BufRNum(B, TAG); x.Tjmp := 0; x.Fjmp := 0; Input(exp); class:=exp.tag; Compile(exp, x, -1);
        IF (tag=Twith) & (class=UmopIs) THEN
          PushDict;
          obj:=exp.left.obj; typ:=obj.typ; obj.typ:=exp.obj.typ;
          GenNode(obj, obj.typ, obj.mode, FALSE, exp.left.global);
        END;
        PLC.PutCondBranch(x, FALSE); Lfix:=0; PLC.SetLabel(x.Tjmp); bool:=FALSE;
        LOOP
          CASE TAG OF
          | Telsif:
            Kernel.BufRNum(B, TAG); PLC.PutBranch(Lfix); PLC.SetLabel(x.Fjmp);
            x.Tjmp := 0; x.Fjmp := 0; Input(exp); class:=exp.tag; Compile(exp, x, -1);
            PLC.PutCondBranch(x, FALSE); PLC.SetLabel(x.Tjmp);
            IF (tag=Twith) & (class=UmopIs) THEN
              PopDict; obj.typ:=typ; PushDict;
              obj:=exp.left.obj; typ:=obj.typ; obj.typ:=exp.obj.typ;
              GenNode(obj, obj.typ, obj.mode, FALSE, exp.left.global);
            END;
          | Telse:
            IF (tag=Twith) & (class=UmopIs) THEN PopDict; obj.typ:=typ END;
            Kernel.BufRNum(B, TAG); PLC.PutBranch(Lfix); PLC.SetLabel(x.Fjmp); bool:=TRUE
          | Tend:
            Kernel.BufRNum(B, TAG);
            IF ~bool THEN PLC.SetLabel(x.Fjmp) END;
            PLC.SetLabel(Lfix); EXIT
          | Twend:
            Kernel.BufRNum(B, TAG); PLC.PutBranch(Lfix); PLC.SetLabel(x.Fjmp);
            PLC.Trap(4); PLC.SetLabel(Lfix);
            IF class=UmopIs THEN PopDict; obj.typ:=typ END;
            EXIT
          ELSE Statement END
        END
    | Tcase:
        Kernel.BufRNum(B, min); Kernel.BufRNum(B, max); Kernel.BufRNum(B, TAG);
        Input(exp); Compile(exp, x, -1); PLC.Case(x, min, max, table); Lfix:=0;
        LOOP
          CASE TAG OF
          | Tcastrap: Kernel.BufRNum(B, TAG); PLC.Trap(3)
          | Tcaslbl1:
            PLC.PutBranch(Lfix); Kernel.BufRNum(B, lo); Kernel.BufRNum(B, TAG);
            PLL.FixCase(SHORT(lo-min), SHORT(lo-min), table)
          | Tcasrng1:
            PLC.PutBranch(Lfix); Kernel.BufRNum(B, lo); Kernel.BufRNum(B, hi); Kernel.BufRNum(B, TAG);
            PLL.FixCase(SHORT(lo-min), SHORT(hi-min), table)
          | Tcaslbl2:
            Kernel.BufRNum(B, lo); Kernel.BufRNum(B, TAG);
            PLL.FixCase(SHORT(lo-min), SHORT(lo-min), table)
          | Tcasrng2:
            Kernel.BufRNum(B, lo); Kernel.BufRNum(B, hi); Kernel.BufRNum(B, TAG);
            PLL.FixCase(SHORT(lo-min), SHORT(hi-min), table)
          | Tend:
            (* PLC.PutBranch(Lfix); *) Kernel.BufRNum(B, TAG); PLC.SetLabel(Lfix); EXIT
          ELSE Statement END
        END
    | Twhile:
        Kernel.BufRNum(B, TAG); L := 0; PLC.SetLabel(L); x.Tjmp := 0; x.Fjmp := 0; Input(exp); Compile(exp, x, -1);
        PLC.PutCondBranch(x, FALSE); PLC.SetLabel(x.Tjmp);
        WHILE TAG#Tend DO Statement END;
        Kernel.BufRNum(B, TAG); PLC.PutBranch(L); PLC.SetLabel(x.Fjmp)
    | Trepeat:
        Kernel.BufRNum(B, TAG); x.Fjmp := 0; PLC.SetLabel(x.Fjmp);
        WHILE TAG#Tend DO Statement END; x.Tjmp := 0;
        Kernel.BufRNum(B, TAG); Input(exp); Compile(exp, x, -1);
        PLC.PutCondBranch(x, FALSE); PLC.SetLabel(x.Tjmp)
    | Tloop:
        Kernel.BufRNum(B, TAG); PLC.EnterLoop;
        WHILE TAG#Tend DO Statement END;
        Kernel.BufRNum(B, TAG); PLC.EndLoop;
    | Texit:
        Kernel.BufRNum(B, TAG); PLC.ExitLoop
    | Ttrap:
        Kernel.BufRNum(B, lo); Kernel.BufRNum(B, TAG); PLC.Trap(SHORT(lo))
    ELSE
      Input(stat);  (*entry, return, assignment or call*)
      Compile(stat, dum, -1);
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
    VAR nofObj: INTEGER; obj2: PLT.Object; dsc: LONGINT; typ: PLT.Struct; elem: Modules.ExportPtr;

    PROCEDURE ExportRecord(typ: PLT.Struct; VAR scope: Modules.ExportDesc);
      VAR nofFld: INTEGER; fld: PLT.Object; dsc: LONGINT; elem, old: Modules.ExportPtr;
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
          scope.nofExp:=nofFld; nofFld:=2; dsc:=scope.dsc;
          PLT.FPrintTyp(typ); typ.oref:=SYS.ADR(scope);
          elem:=SYS.VAL(Modules.ExportPtr, dsc+0*SIZE(Modules.ExportDesc));
          IF (typ.BaseTyp#NIL) & (typ.mod=M) THEN ExportRecord(typ.BaseTyp, elem^) END;
          elem.fp:=typ.pbfp; elem.adr:=-typ.tdadr;
          elem:=SYS.VAL(Modules.ExportPtr, dsc+1*SIZE(Modules.ExportDesc));
          elem.fp:=typ.pvfp;
          fld:=typ.dsc; WHILE fld#NIL DO
            IF fld.vis#internal THEN
              elem:=SYS.VAL(Modules.ExportPtr, dsc+nofFld*SIZE(Modules.ExportDesc));
              elem.fp:=fld.fp; typ:=fld.typ;
              WHILE (typ#NIL) & ((typ.form=Comp) & (typ.comp#Record) OR (typ.form=Pointer)) DO typ:=typ.BaseTyp END;
              IF (typ#NIL) & (typ.form=Comp) & (typ.comp=Record) THEN ExportRecord(typ, elem^) END;
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
    M.export.nofExp:=nofObj; nofObj:=0; dsc:=M.export.dsc;
    WHILE obj2#NIL DO
      IF obj2.vis#internal THEN
        elem:=SYS.VAL(Modules.ExportPtr, dsc+nofObj*SIZE(Modules.ExportDesc));
        elem.fp:=obj2.fp;
        IF obj2.mode=Var THEN elem.adr:=obj2.adr (* dsc[nofObj].adr:=obj2.adr-M.data *)
        ELSIF obj2.mode=XProc THEN elem.adr:=PLL.entry[obj2.adr] (* dsc[nofObj].adr:=(obj2.adr-M.code) DIV 2 *)
        ELSE elem.adr:=0 END;
        IF (obj2.mode>XProc) OR (obj2.mode=Var) THEN typ:=obj2.typ;
          WHILE (typ#NIL) & ((typ.form=Comp) & (typ.comp#Record) OR (typ.form=Pointer)) DO typ:=typ.BaseTyp END;
          IF (typ#NIL) & (typ.form=Comp) & (typ.comp=Record) THEN ExportRecord(typ, elem^) END;
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
      VAR fp, i: LONGINT; dsc: LONGINT; typ2: PLT.Struct; obj: PLT.Object; tmpErr: BOOLEAN; elem: Modules.ExportPtr;
        n: Node;  (* mfix *)
    BEGIN tmpErr:=(level=EUerrScope);
      IF level=EUrecScope THEN (* do not insert fields here *)
        UNodeO(Uguard, flgNoLeft, typ, NIL, Global);
        UNodeO(Ueguard, flgNoLeft, typ, NIL, Global);
        UNodeO(UmopIs, flgNoLeft, PLT.booltyp, typ.strobj, Global);
      END;
      dsc:=scope.dsc; i:=0;
      Kernel.BufRNum(B, fp); i:=-1;
      WHILE fp#EUEnd DO
        IF fp=EURecord THEN
          IF i=-1 THEN i:=0; typ2:=typ.BaseTyp END;
          elem:=SYS.VAL(Modules.ExportPtr, dsc+i*SIZE(Modules.ExportDesc));
          IF tmpErr THEN CheckScope(elem^, EUerrScope, typ2) ELSE CheckScope(elem^, EUrecScope, typ2) END;
        ELSE Kernel.BufRString(B, name);
          IF level>=EUobjScope THEN tmpErr:=FALSE;
            elem:=SYS.VAL(Modules.ExportPtr, dsc);
            i:=0; WHILE (i<scope.nofExp) & (elem.fp#fp) DO INC(i); elem:=SYS.VAL(Modules.ExportPtr, dsc+i*SIZE(Modules.ExportDesc)) END;
            IF i>=scope.nofExp THEN Err; tmpErr:=TRUE; Ln;
              Ch(9X); obj:=NIL; Str(name); Str(" incompatible");
            ELSIF level=EUrecScope THEN FindField(obj, typ, name);
              IF obj.mode = Fld THEN
                UNodeO(Ufield, flgNoLeft, obj.typ, obj, Global);
              ELSE
                NNode(n, Uproc, typ, obj, NIL, NIL, Global);
                CallNode(n, UcallXPrc, obj.nofpar, obj.typ, obj, NIL, Global);
                CallNode(n, UcallXPrc, obj.nofpar, obj.typ, obj, NIL, Global); n.safe := TRUE;
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
    VAR i: INTEGER; block: LONGINT; dummy : PLT.Object; m1 : Modules.Module; res: INTEGER;
  BEGIN
    Kernel.GCenabled:=FALSE;  (* nodes must not be collected *)
    B:=buf; M:=mod; N:=NNN; below:=-1; above:=Ttrap+1; levCall:=0;
    IF (b > MaxBelow) OR (a > MaxAbove) THEN
      Kernel.AllocBlock(block, (b+a-1)*SIZE(NodeDesc)); N:=block+((b-1)*SIZE(NodeDesc)) END;

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
      Kernel.BufRNum(B, TAG); WHILE TAG#Tbegin  DO  Statement END;  (*nested*)
      body:=PLL.pc; PLC.Enter(NIL, NIL);
      Kernel.BufRNum(B, TAG); WHILE TAG#Tend  DO  Statement END;  (*body*)
      dummy:=NIL; PLC.Leave(dummy); (* PLL.OutRefName("$$"); *)
      dummy:=SYS.VAL(PLT.Object, mod.privates); (* PLL.OutRefs(dummy); *)

      IF  (b > MaxBelow) OR (a > MaxAbove)  THEN  Kernel.DeAllocBlock(block)  END;
      buf:=B;
      BuildExpBlock(mod, globals);
    END;
    Kernel.GCenabled:=TRUE;
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
  NEW(trueNode); trueNode.tag:=TconstTrue; trueNode.typ:=PLT.booltyp; trueNode.global:=Global; NEW(trueNode.obj);
  trueNode.obj.ival:=1;
  Kernel.AllocBlock(NNN, -(MaxBelow+MaxAbove-1)*SIZE(NodeDesc)); INC(NNN, (MaxBelow-1)*SIZE(NodeDesc))
END OPLV.