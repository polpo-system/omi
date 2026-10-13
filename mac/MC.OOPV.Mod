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

MODULE OOPV;  (*mf 27.5.94 / tk object model 1.7.96 *)

  (* 6/6/96 recursive typesize eliminated *)
  (* 1.7.96 Method support (mfix) *)

IMPORT
  OPL:=OOPL, OPC:=OOPC, OPT:=OOPT, OPM:=OOPM, SYS:=SYSTEM;

CONST
  (*OPT Visibility*)  internal=0;
  (*OPS Symbol Values*) and=5; or=8; eql=9; geq=14; is=16; conv=20;
  (*OPT Object Modes*)  Var=1; VarPar=2; Fld=4; Typ=5; LProc=6; XProc=7; CProc=9; IProc=10; TProc=13;
  (*OPT Structure Forms*) Undef=0; Byte=1; Bool=2; Char=3; SInt=4; Int=5; LInt=6; Real=7; LReal=8; Set=9; String=10; NilTyp=11;
  (*OPT Structure Forms*) NoTyp=12; Pointer=13; ProcTyp=14; (*Composite*) Array=2; DynArr=3; Record=4;
  (*OPT Node Subclasses*) super=1;
  (*OPB Node Classes*)  Nvar=0; Nvarpar=1; Nfield=2; Nderef=3; Nindex=4; Nguard=5; Neguard=6; Nconst=7; Nproc=9;
  (*OPB Node Classes*)  Nupto=10; Nmop=11; Ndop=12; Ncall=13; Ninittd=14; Nenter=18; Nassign=19;
  (*OPB Node Classes*)  Nifelse =20; Ncase=21; Nwhile=22; Nrepeat=23; Nloop=24; Nexit=25; Nreturn=26; Nwith=27; Ntrap=28;
  (*OPB Function Numbers*)  assign=0; newfn=1; movefn=31; assertfn=32;
  (*OPL Item Modes*)  GlobVar=20; GlobRef=22; GlobProc=23; Imm=27; TDProc=29;
  (*OPO safe Flag*) safe=42;
  (*OP2 Options*) oassert=6; ofindpc=9;
  (*Register Types*)  Dreg=0; Areg=1; Freg=2;


  VAR
    mod*: OPT.Node;
    ExitChain: OPL.Label;
    assert, findpc: BOOLEAN;

  PROCEDURE err(n: INTEGER);
  BEGIN OPM.err(n)
  END err;

  PROCEDURE TprocAdr(obj: OPT.Object);  (*only own Tprocs need enumeration*)
    VAR typ: OPT.Struct; redef: OPT.Object;
  BEGIN
    IF  obj#NIL THEN
      TprocAdr(obj.left);
      IF  obj.mode=TProc  THEN  typ:=obj.link.typ;
        IF  typ.form=Pointer  THEN  typ:=typ.BaseTyp  END;
        OPT.FindField(obj.name, typ.BaseTyp, redef, FALSE); (* mfix *)
        IF  redef#NIL THEN  obj.adr:=redef.adr;
          IF  ~(2 IN obj.conval.setval) THEN  err(119)  END
        ELSE
          obj.adr:=typ.n; INC(typ.n)
        END
      END;
      TprocAdr(obj.right)
    END
  END TprocAdr;

  PROCEDURE TypSize*(typ: OPT.Struct; dummy: BOOLEAN);
    VAR f, c, nofptr: INTEGER; btyp, ftyp: OPT.Struct; fld: OPT.Object; offset, size, n: LONGINT;
  BEGIN
    IF  typ=OPT.undftyp THEN  err(58)
  ELSIF typ.size<0  THEN  f:=typ.form; c:=typ.comp; btyp:=typ.BaseTyp;
      IF  c=Record  THEN  fld:=typ.link;
        IF  btyp=NIL  THEN  nofptr:=0; offset:=0; n:=0  ELSE  TypSize(btyp, FALSE); nofptr:=btyp.nofptr; offset:=btyp.size  END;
        typ.size := 0;
        WHILE fld#NIL DO  ftyp:=fld.typ;  TypSize(ftyp, FALSE);
          IF fld.mode=Fld THEN
            size:=ftyp.size;
            IF  size>1  THEN  INC(offset, offset MOD 2) END;
            fld.adr:=offset; INC(offset, size); INC(nofptr, ftyp.nofptr);
          END;
          fld:=fld.link
        END;
        INC(offset, offset MOD 2); typ.size:=offset; typ.nofptr:=nofptr;
        IF  btyp=NIL  THEN  typ.n:=0  ELSE  typ.n:=btyp.n END;
        TprocAdr(typ.link);
      ELSIF f=Pointer THEN  typ.size:=4; typ.nofptr:=1
      ELSIF c=Array THEN  TypSize(btyp, FALSE); typ.size:=typ.n*btyp.size; typ.nofptr:=SHORT(typ.n*btyp.nofptr)
      ELSIF f=ProcTyp THEN  typ.size:=4
      ELSE  (*c=DynArr*)  typ.size:=8*typ.n+8 END
    END
  END TypSize;

  PROCEDURE ^ Traverse(obj: OPT.Object);

  PROCEDURE TypAdrSize(typ: OPT.Struct);
    VAR f, c: INTEGER; btyp: OPT.Struct; par: OPT.Object;
  BEGIN
    IF  (typ.mno=0)&(~typ.inited) THEN  typ.inited:=TRUE; f:=typ.form; c:=typ.comp; btyp:=typ.BaseTyp; TypSize(typ, FALSE);
      IF  c=Record  THEN
        IF  typ.tdadr=OPM.TDAdrUndef  THEN  OPL.AllocTypDesc(typ) END;
        IF  btyp#NIL  THEN  TypAdrSize(btyp)  END;
        Traverse(typ.link);
      ELSE  TypAdrSize(btyp);
        IF  f=ProcTyp THEN  par:=typ.link;
          WHILE par#NIL DO  TypAdrSize(par.typ); par:=par.link  END
        ELSIF c=DynArr  THEN  typ.tdadr:=8*typ.n+4  END
      END
    END
  END TypAdrSize;

  PROCEDURE ProcAdr(proc: OPT.Object);
    VAR adr, s, psize, dsize, rsize, align: LONGINT; var, par: OPT.Object; typ: OPT.Struct;
  BEGIN
    par:=proc.link; adr:=0;
    WHILE par#NIL DO  typ:=par.typ; s:=typ.size;
      IF  typ.comp#DynArr THEN
        IF  par.mode=VarPar THEN
          IF  typ.comp=Record THEN  s:=8  ELSE  s:=4  END
        ELSIF typ.form=LReal  THEN  s:=8
        ELSIF s > 4 THEN  s:=4
        ELSIF s=1 THEN  s:=2  END
      END;
      INC(adr, s); par.adr:=adr; par:=par.link
    END;

    IF  proc.mnolev=0 THEN  psize:=adr+8  ELSE  psize:=adr+12 END;
    par:=proc.link;
    WHILE par#NIL DO  par.adr:=psize-par.adr; par:=par.link END;

    rsize:=0;
    IF  ~(proc.typ.form IN {NoTyp, Real, LReal})  THEN  rsize:=proc.typ.size; INC(rsize, rsize MOD 2) END;
    align:=-((-psize-rsize) MOD 4);

    var:=proc.scope.scope; adr:=0;
    WHILE var#NIL DO  s:=var.typ.size;
      IF  s > 2 THEN  DEC(adr, adr MOD 4)
      ELSIF s=2 THEN  DEC(adr, adr MOD 2) END;
      DEC(adr, s); var.adr:=adr+align; var:=var.link
    END;
    DEC(adr, adr MOD 4);
    IF  adr < -8000H  THEN  err(252); dsize:=0  ELSE  dsize:=-adr-align END;
    proc.conval.intval:=psize; proc.conval.intval2:=dsize
  END ProcAdr;

  PROCEDURE Traverse(obj: OPT.Object);  (*address all types and invisible global procedures, but leave variables alone*)
    CONST hasBody=1; VAR par: OPT.Object;
  BEGIN
    IF  obj#NIL THEN  Traverse(obj.left); TypAdrSize(obj.typ);
      IF  obj.mode IN {LProc, XProc, CProc, TProc}  THEN  Traverse(obj.scope.right);
        IF  ~(hasBody IN obj.conval.setval) THEN  err(129)  END;
        IF  obj.mode=XProc  THEN  ProcAdr(obj);
          IF  obj.adr=0 THEN  OPL.AllocGlobProc(obj.adr)  END
        ELSIF obj.mode IN {LProc, TProc}  THEN  ProcAdr(obj)
        ELSIF obj.mode=CProc  THEN  par:=obj.link;  (*verify parameter list restrictions*)
          WHILE par#NIL DO
            IF  par.typ.form IN {Char, Real, LReal} THEN  err(401)
            ELSIF par.typ.comp=DynArr THEN  err(402)  END;
            par:=par.link
          END;
          IF  obj.typ.form IN {Char, Real, LReal} THEN  err(401)
          ELSIF obj.typ.form=DynArr THEN  err(402)  END
        END
      END;
      Traverse(obj.right)
    END
  END Traverse;

  PROCEDURE AssignEntries*(obj: OPT.Object; browse: BOOLEAN); (*assign entry numbers of imported objects*)
    VAR nofEntries, nofVar: LONGINT;
  BEGIN nofEntries:=2;
    WHILE obj#NIL DO
      IF  obj.mode=Var  THEN  IF  browse  THEN  obj.adr:=nofVar; INC(nofVar)  END
      ELSIF obj.mode=XProc  THEN  IF  browse  THEN  obj.adr:=nofEntries; INC(nofEntries)  END
      ELSIF obj.mode=Typ  THEN  TypSize(obj.typ, FALSE);
        IF  obj.typ.comp=Record THEN  obj.typ.tdadr:=nofEntries; INC(nofEntries)
        ELSIF obj.typ.comp=DynArr THEN  obj.typ.tdadr:=8*obj.typ.n+4  END
      END;
      obj:=obj.nxtobj
    END
  END AssignEntries;

  PROCEDURE AssignOwnEntries(obj: OPT.Object);  (*assign entry numbers of exported objects*)
  BEGIN
    WHILE obj#NIL DO
      IF  obj.mode=Var  THEN  TypSize(obj.typ, FALSE); OPL.AllocGlobVar(obj.adr, obj.typ.size)
      ELSIF obj.mode=XProc  THEN  OPL.AllocGlobProc(obj.adr)
      ELSIF (obj.mode=Typ)&(obj.typ.comp=Record)  THEN  TypSize(obj.typ, FALSE); OPL.AllocTypDesc(obj.typ)  END;
      obj:=obj.nxtobj
    END
  END AssignOwnEntries;

  PROCEDURE AdrAndSize*;
    VAR var: OPT.Object; i: INTEGER;
  BEGIN OPM.errpos:=OPT.topScope.adr; i:=1;
    WHILE i < OPT.nofmod  DO  AssignEntries(OPT.modules[i].publics, FALSE); INC(i)  END;
    AssignOwnEntries(OPT.objects); Traverse(OPT.topScope.right); var:=OPT.topScope.scope;
    WHILE var#NIL DO
      IF  var.vis=internal  THEN  OPL.AllocGlobVar(var.adr, var.typ.size) END;
      var:=var.link
    END;
  END AdrAndSize;

  PROCEDURE ^ expr(n: OPT.Node; VAR x: OPL.Item);

  PROCEDURE design(n: OPT.Node; VAR x: OPL.Item);
    VAR left: OPT.Node; obj: OPT.Object; y: OPL.Item; mnolev: SHORTINT; adr: LONGINT;
  BEGIN left:=n.left;
    CASE  n.class OF
    | Nvar: obj:=n.obj; mnolev:=obj.mnolev; adr:=obj.adr; x.obj:=obj;
        IF  mnolev<=0 THEN  x.mode:=GlobVar; x.adr:=adr; x.disp:=0; x.alpha:=-mnolev
        ELSIF adr<=0  THEN  OPL.LocalVar(x, mnolev, adr, FALSE) (*locvar zero for empty records*)
        ELSIF (obj.typ.comp=DynArr)OR((obj.typ.size>4)&(obj.typ.form#LReal))  THEN  OPL.LocalVar(x, mnolev, adr, TRUE)
        ELSE  OPL.LocalVar(x, mnolev, adr, FALSE) END
    | Nvarpar:  OPL.LocalVar(x, n.obj.mnolev, n.obj.adr, TRUE)
    | Nfield: design(left, x); OPC.Field(x, n.obj.adr)
    | Nderef: design(left, x); OPC.DeRef(x, n.subcl=safe)
    | Nindex: design(left, x); expr(n.right, y); OPC.Index(x, y, n.subcl=safe)
    | Nguard: design(left, x); OPC.TypTest(x, n.typ, 0, TRUE, FALSE, n.subcl=safe)
    | Neguard:  design(left, x); OPC.TypTest(x, n.typ, left.class, TRUE, TRUE, n.subcl=safe)
    | Nproc:  obj:=n.obj; (*Use Object in Call*)
        x.mode:=GlobProc; x.obj:=obj; x.adr:=obj.adr; x.alpha:=-obj.mnolev
    END;
    x.typ:=n.typ
  END design;

  PROCEDURE ActualPar(n: OPT.Node; fp, proc: OPT.Object; VAR x: OPL.Item; tagVarPar, super: BOOLEAN);
    VAR ap: OPL.Item; receiver: OPT.Node;
  BEGIN
    IF  (proc#NIL)&(proc.mode=TProc)  THEN  receiver:=n ELSE  receiver:=NIL END;
    WHILE n#NIL DO  expr(n, ap);
      IF  n=receiver  THEN  OPC.PrepTprocCall(ap, n.class, x, super)  END;
      IF  n.class=Nguard  THEN  OPC.Param(ap, fp, n.left.class, tagVarPar)
      ELSE  OPC.Param(ap, fp, n.class, tagVarPar)
      END;
      n:=n.link; fp:=fp.link
    END
  END ActualPar;

  PROCEDURE Call(n: OPT.Node; VAR x: OPL.Item);
    VAR proc: OPT.Object; restyp: OPT.Struct; size: LONGINT; regs: OPL.RegSet;
  BEGIN restyp:=n.typ; OPL.SaveRegisters(regs);
    IF  (restyp#OPT.notyp)&(~(restyp.form IN {Real, LReal}))  THEN  size:=restyp.size; INC(size, size MOD 2); OPL.ADDA(-size, 7)  END;
    IF  n.left.class=Nproc  THEN  proc:=n.left.obj;
      IF  proc.mode=TProc THEN  x.mode:=TDProc; x.adr:=proc.adr END;
      ActualPar(n.right, n.obj, proc, x, ~(proc.mode IN {CProc, IProc}), n.left.subcl=super); OPC.Call(x, proc); x.typ:=n.left.typ
    ELSE  design(n.left, x); ActualPar(n.right, n.obj, NIL, x, x.typ.sysflag=0, FALSE); OPC.CallPV(x) END;
    OPL.RestoreRegisters(regs, x)
  END Call;

  PROCEDURE expr(n: OPT.Node; VAR x: OPL.Item);
    VAR y, z: OPL.Item; op: INTEGER; r: REAL; cval: OPT.Const;
  BEGIN
    CASE  n.class OF
    | Nconst: x.mode:=Imm; cval:=n.conval;
        CASE  n.typ.form  OF
        | Bool: IF  cval.intval=0 THEN  x.adr:=0  ELSE  x.adr:=-1 END
        | Byte, Char, SInt, Int, LInt, NilTyp, Pointer: x.adr:=cval.intval
        | Real: r:=SHORT(cval.realval); SYS.PUT(SYS.ADR(x.adr), r)
        | LReal:  SYS.PUT(SYS.ADR(x.adr), cval.realval)
        | Set:  SYS.PUT(SYS.ADR(x.adr), cval.setval)
        | String:
            IF  (n.obj=NIL) OR (n.obj.conval.intval=OPM.ConstNotAlloc)  THEN  OPL.AllocString(cval, x.adr);
              IF  n.obj#NIL THEN  n.obj.conval.intval:=x.adr  END
            ELSE  x.adr:=n.obj.conval.intval  END;
            x.mode:=GlobRef; x.alpha:=0; x.beta:=SHORT(cval.intval2)
        END
    | Nupto:  expr(n.left, y); expr(n.right, z); OPC.SetRange(x, y, z)
    | Nmop: expr(n.left, x); op:=n.subcl;
      IF  op=is THEN  OPC.TypTest(x, n.obj.typ, 0, FALSE, FALSE, FALSE)
      ELSIF (op=conv)&(n.typ.form#Set)  THEN  OPC.Convert(x, x.typ.form, n.typ.form)
      ELSE  OPC.MOp(x, op)  END;
    | Ndop: op:=n.subcl; expr(n.left, x);
        IF  op=and  THEN  OPC.CondAnd(x)
        ELSIF op=or THEN  OPC.CondOr(x)
        ELSIF (op>=eql)&(op<=geq) THEN  OPC.Relation(x)
        END;
        expr(n.right, y); OPC.DOp(x, y, op)
    | Ncall:  Call(n, x)
    ELSE  design(n, x)  END;
    x.typ:=n.typ
  END expr;

  PROCEDURE ^ stat(n: OPT.Node);

  PROCEDURE Checkpc;
  BEGIN
    IF  findpc&(OPL.pc > OPM.breakpc)&OPM.noerr THEN  err(255)  END
  END Checkpc;

  PROCEDURE IfStat(n: OPT.Node; withtrap: BOOLEAN);
    VAR x: OPL.Item; Lcfj, Lfix: OPL.Label; if: OPT.Node;
  BEGIN Lfix:=0; if:=n.left;
    LOOP  OPM.errpos:=if.conval.intval; expr(if.left, x); OPL.CFJ(x, Lcfj); Checkpc; stat(if.right); if:=if.link;
      IF  if=NIL  THEN  EXIT  END;
      OPL.FJ(Lfix); OPL.FixLink(Lcfj)
    END;
    IF  (n.right#NIL) OR withtrap THEN  OPL.FJ(Lfix); OPL.FixLink(Lcfj);
      IF  withtrap  THEN  OPC.Trap(15); OPM.errpos:=n.conval.intval; Checkpc  ELSE  stat(n.right) END
    ELSE  OPL.FixLink(Lcfj) END;
    OPL.FixLink(Lfix)
  END IfStat;

  PROCEDURE CaseStat(n: OPT.Node);
    VAR x: OPL.Item; Lfix, L: OPL.Label; case, lab: OPT.Node; tab: INTEGER; low, high: LONGINT;
  BEGIN expr(n.left, x); low:=n.right.conval.intval; high:=n.right.conval.intval2; OPC.Case(x, low, high, tab, L); Checkpc; Lfix:=0;
    IF  n.right.conval.setval#{}  THEN  stat(n.right.right); OPL.FJ(Lfix) ELSE  OPC.Trap(16)  END;
    case:=n.right.left;
    WHILE case#NIL  DO  lab:=case.left;
      WHILE lab#NIL DO  OPL.CaseJump(L, tab, SHORT(lab.conval.intval-low), SHORT(lab.conval.intval2-low)); lab:=lab.link  END;
      stat(case.right); OPL.FJ(Lfix); case:=case.link
    END;
    OPL.FixLink(Lfix)
  END CaseStat;

  PROCEDURE Enter(n: OPT.Node);
    VAR i: INTEGER; ch: CHAR; x: OPL.Item; proc, par: OPT.Object; rec: OPT.Struct;
  BEGIN INC(OPL.level); stat(n.left); DEC(OPL.level);
    IF  n.obj=NIL THEN
      OPL.SetEntry(0); stat(n.right); OPC.ReturnFromMod;
      OPL.OutRefPoint; OPM.SymW(0X); OPL.OutRefs(OPT.topScope);
    ELSE  proc:=n.obj; par:=proc.link;
      IF  (proc.mode=XProc)&(proc.adr>0)  THEN  OPL.SetEntry(SHORT(proc.adr)) END;
      OPC.EnterProc(proc);
      WHILE par#NIL DO
        IF  par.mode=Var  THEN
          IF  par.typ.comp=DynArr THEN  OPC.CopyDynArray(par.adr, par.typ)
          ELSIF (par.typ.size>4)&(par.typ.form#LReal) THEN  OPC.CopyPar(par.adr, SHORT(par.typ.size)) END
        END;
        par:=par.link
      END;
      stat(n.right);
      IF  proc.typ#OPT.notyp  THEN  OPC.Trap(17)  ELSE  OPC.ReturnFromProc(proc, FALSE, x)  END;
      OPL.OutRefPoint;
      IF  proc.mode=TProc THEN  rec:=proc.link.typ;
        IF  rec.form=Pointer  THEN  rec:=rec.BaseTyp  END;
        OPM.SymW("(");
        IF  rec.strobj#NIL  THEN  i:=0; ch:=rec.strobj.name[0];
          WHILE ch#0X DO  OPM.SymW(ch); INC(i); ch:=rec.strobj.name[i]  END;
        ELSE  OPM.SymW("?")
        END;
        OPM.SymW(")")
      END;
      OPM.SymWString(proc.name); OPL.OutRefs(proc.scope.right)
    END
  END Enter;

  PROCEDURE NewArr(VAR x, y: OPL.Item; e: OPT.Node; typ, typ0: OPT.Struct);
    VAR len: OPL.Item;
  BEGIN
    expr(e, len);
    OPC.NewArrMulLen(y, len, typ, typ0);  (* y:=nofelems *)
    IF  e.link=NIL  THEN  OPC.NewArr(x, y, typ, typ0) ELSE  NewArr(x, y, e.link, typ.BaseTyp, typ0) END;  (*y :=base type size *)
    OPC.NewArrSetLen(x, y, len, typ, typ0); (* y:=dimension*base typ size *)
    IF  typ=typ0  THEN  OPL.Release(x); OPL.Release(y); OPL.Release(len)  END
  END NewArr;

  PROCEDURE stat(n: OPT.Node);
    VAR x, y, z: OPL.Item; proc: OPT.Object; L, Lcfj, prevExitChain: OPL.Label; op: INTEGER;
      i: INTEGER;
  BEGIN
    WHILE n#NIL DO  OPM.errpos:=n.conval.intval;
      CASE  n.class OF
      | Ncall:
          IF  n.left.class=Nproc  THEN  proc:=n.left.obj;
            IF  proc.mode=TProc THEN  x.mode:=TDProc; x.adr:=proc.adr END;
            ActualPar(n.right, n.obj, n.left.obj, x, n.left.obj.mode#CProc, n.left.subcl=super); OPC.Call(x, proc)
          ELSE  design(n.left, x); ActualPar(n.right, n.obj, n.left.obj, x, TRUE, FALSE); OPC.CallPV(x) END
      | Ninittd:  OPC.InitTypDesc(n.typ);
      | Nenter: Enter(n)
      | Nassign:
          op:=n.subcl;
          IF  op=assign THEN
            IF  n.left.typ#OPT.booltyp  THEN  expr(n.right, y); expr(n.left, x) ELSE  expr(n.left, x); expr(n.right, y) END;
            OPC.Assign(x, y)
          ELSIF op=movefn THEN  expr(n.right.link, z); expr(n.right, y); expr(n.left, x); OPC.SYSmove(x, y, z)
          ELSIF op=newfn  THEN  expr(n.left, x);
            IF  n.right=NIL THEN  OPC.New(x)  ELSE  NewArr(x, z, n.right, x.typ.BaseTyp, x.typ.BaseTyp) END
          ELSE  expr(n.right, y); expr(n.left, x); OPC.AStat(x, y, op)  END
      | Nifelse:
          IF  n.subcl=assertfn  THEN
            IF  assert  THEN  expr(n.left.left, x); OPL.TrapCC(x, n.left.right.right.conval.intval)  END
          ELSE  IfStat(n, FALSE)
          END
      | Ncase:  CaseStat(n)
      | Nwhile: L:=OPL.pc; expr(n.left, x); OPL.CFJ(x, Lcfj); Checkpc; stat(n.right); OPL.BJ(L); OPL.FixLink(Lcfj)
      | Nrepeat:  L:=OPL.pc; stat(n.left); expr(n.right, x); OPL.CBJ(x, L)
      | Nloop:  prevExitChain:=ExitChain; ExitChain:=0; L:=OPL.pc; stat(n.left); OPL.BJ(L); OPL.FixLink(ExitChain); ExitChain:=prevExitChain
      | Nexit:  OPL.FJ(ExitChain)
      | Nreturn:  IF  n.left#NIL  THEN  expr(n.left, x) END;
          OPC.ReturnFromProc(n.obj, n.left#NIL, x)
      | Nwith:  IfStat(n, n.subcl=0)
      | Ntrap:  OPC.Trap(n.right.conval.intval)
      END;
      Checkpc; n:=n.link;

i:=4; WHILE i>=0  DO  IF OPL.register[Areg, i]#0 THEN OPL.register[Areg, i]:=0; OPM.err(-(1008+i)) END; DEC(i)  END;
i:=7; WHILE i>=0  DO  IF OPL.register[Dreg, i]#0 THEN OPL.register[Dreg, i]:=0; OPM.err(-(1000+i)) END; DEC(i)  END;
i:=7; WHILE i>=0  DO  IF OPL.register[Freg, i]#0 THEN OPL.register[Freg, i]:=0; OPM.err(-(1100+i)) END; DEC(i)  END;

    END
  END stat;

  PROCEDURE Module*(opt: SET; prog: OPT.Node; bpc: LONGINT);
  BEGIN
    assert:=oassert IN opt; findpc:=ofindpc IN opt;
    IF  findpc  THEN  OPM.breakpc:=SHORT(bpc DIV 2) ELSE  OPM.breakpc:=MAX(INTEGER) END;
    stat(prog); mod:=NIL; (* GC *)
    IF  findpc & OPM.noerr  THEN  err(254)  END;
  END Module;

BEGIN OPT.typSize:=TypSize
END OOPV.