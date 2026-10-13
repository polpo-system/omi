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

MODULE OPLT;  (*mf 18.10.93 / tk object model 1.7.96 *)

  (* 1.7.96 Method support (mfix) *)
  (* 29.10.96 Symbolfile format change (SysFlag) *)

  IMPORT
    SYS:=SYSTEM, Kernel, Modules;

  CONST
    DefMaxImport=64; DefMaxStruct=32; DefMaxReimp=32;

  TYPE
    Name*=ARRAY 32 OF CHAR;
    Object*=POINTER TO ObjDesc;
    Struct*=POINTER TO StrDesc;
    StrPtr*= POINTER TO ARRAY 256 OF CHAR;

    ObjDesc*=RECORD
      name*: Name; nxtobj*, locals*: Object;
      mode*, level*, vis*: SHORTINT; typ*: Struct;
      ival*: LONGINT; rval*: LONGREAL; xval*: StrPtr; (*constants*)
      inited*: BOOLEAN; psize*, dsize*, fp*: LONGINT; par*: Object; nofpar*, fixlink*: INTEGER; adr*, lim*: LONGINT (*procedures*)
    END;

    StrDesc*=RECORD
      form*, comp*, mno*, extlev*: SHORTINT; sysflag*: BOOLEAN;
      BaseTyp*: Struct; strobj*, dsc*: Object;
      nofdsc*, nofptr*: INTEGER; fpdone: LONGINT; mod*: Modules.Module;
      n*, size*, tdadr*, fp*, pvfp*, pbfp*, oref*: LONGINT
    END;


  VAR
    booltyp*, chartyp*, sinttyp*, inttyp*, linttyp*, realtyp*, lrltyp*, settyp*, stringtyp*, niltyp*, notyp*, sysptrtyp*, ptrtyp*, proctyp*: Struct;

  CONST
    Var=1; Par=2; VarPar=3; Con=4; Fld=5; LProc=6; XProc=7; TypDynArr=8; TypArray=9;
    TypPointer=10; TypRecord=11; TypProcTyp=12; TypAlias=13; TProc=14;
    Bool=2; Char=3; SInt=4; Int=5; LInt=6; Real=7; LReal=8; Set=9; String=10; NilTyp=11;
    NoTyp=12; Pointer=13; ProcTyp=14; Comp=15; Basic=1; Array=2; DynArr=3; Record=4;

    SFtypBool=01H; SFtypChar=02H; SFtypSInt=03H; SFtypInt=04H; SFtypLInt=05H;
    SFtypReal=06H; SFtypLReal=07H; SFtypSet=08H; SFtypString=09H; SFtypNoTyp=0AH; SFtypNilTyp=0BH;
    SFtypByte=0CH; SFtypSptr=0DH; SFmod1=0EH; SFmod31=2CH; SFmodOther=2DH;
    SFtypDynArr=2EH; SFtypArray=2FH; SFtypPointer=30H; SFtypRecord=31H; SFtypProcTyp=32H;
    SFsysflag=33H; SFinvisible=34H; SFreadonly=35H; SFleaf=36H;
    SFconst=37H; SFvar=38H; SFlproc=39H; SFxproc=3AH; SFcproc=3BH; SFtproc=3CH; SFalias=3DH; SFtyp=3EH; SFend=3FH;

    internal=0; external=1; externalR=2;

  VAR
    predefStruct: ARRAY SFtypProcTyp+1 OF Struct; (*predefined types*)
    strucForm: ARRAY SFtypProcTyp+1 OF SHORTINT;  (*forms of structures*)
    strucComp: ARRAY SFtypProcTyp+1 OF SHORTINT;  (*forms of structures*)
    tobjMode: ARRAY SFtypProcTyp+1 OF SHORTINT; (*modes of type objects*)
    cobjMode: ARRAY TypAlias+1 OF SHORTINT;   (*compiler's object modes*)
    thisMod: Modules.Module; predefMod: LONGINT;
    typSize*: PROCEDURE (typ: Struct);

(* Fingerprinting *)

  PROCEDURE FPrint(VAR fp: LONGINT; val: LONGINT);
  BEGIN fp:=SYS.VAL(LONGINT, SYS.VAL(SET, SYS.ROT(fp, 7)) / SYS.VAL(SET, val))
  END FPrint;

  PROCEDURE FPrintSet(VAR fp: LONGINT; set: SET);
  BEGIN FPrint(fp, SYS.VAL(LONGINT, set))
  END FPrintSet;

  PROCEDURE FPrintReal(VAR fp: LONGINT; real: REAL);
  BEGIN FPrint(fp, SYS.VAL(LONGINT, real))
  END FPrintReal;

  PROCEDURE FPrintLReal(VAR fp: LONGINT; lr: LONGREAL);
    VAR l, h: LONGINT;
  BEGIN
    SYS.GET(SYS.ADR(lr), l); SYS.GET(SYS.ADR(lr)+4, h);
    FPrint(fp, l); FPrint(fp, h);
  END FPrintLReal;

  PROCEDURE ^ FPrintTyp0(typ: Struct);
  PROCEDURE ^ FPrintTyp*(typ: Struct);

  PROCEDURE FPrintName(VAR fp: LONGINT; VAR name: ARRAY OF CHAR);
    VAR i: INTEGER; ch: CHAR;
  BEGIN i:=0; REPEAT ch:=name[i]; FPrint(fp, ORD(ch)); INC(i) UNTIL ch=0X
  END FPrintName;

  PROCEDURE FPrintSign(VAR fp: LONGINT; result: Struct; par: Object);
  BEGIN
    FPrintTyp0(result); FPrint(fp, result.fp);
    WHILE par#NIL DO
      FPrint(fp, cobjMode[par.mode]);
      IF par.typ # NIL THEN FPrintTyp0(par.typ); FPrint(fp, par.typ.fp) END;
      par:=par.nxtobj;
    END;
  END FPrintSign;

  PROCEDURE FindField(VAR name: Name; typ: Struct; VAR res: Object);  (* mfix *)
    VAR obj: Object;
  BEGIN res := NIL;
    WHILE (typ # NIL) & (res = NIL) DO obj := typ.dsc;
      WHILE obj # NIL DO
        IF name = obj.name THEN res := obj; obj := NIL ELSE obj := obj.nxtobj END;
      END;
      IF res = NIL THEN typ := typ.BaseTyp END
    END
  END FindField;

  PROCEDURE FPrintMeth(typ: Struct; fld: Object);
    VAR fp: LONGINT; redef: Object;
  BEGIN
    WHILE fld # NIL DO
      IF (fld.mode=TProc) & (fld.vis#internal) THEN
        fp:=0; FPrint(fp, 13 (* TProc *)); FPrintName(fp, fld.name); FPrintSign(fp, fld.typ, fld.par); fld.fp:=fp;
        FPrint(fp, fld.adr); FPrint(typ.pbfp, fp); FPrint(typ.pvfp, fp);
      END;
      fld := fld.nxtobj;
    END
  END FPrintMeth;

  PROCEDURE FPrintRecord(typ: Struct);
    VAR fld: Object; fp, pbfp, pvfp: LONGINT;
  BEGIN
    pvfp:=typ.fp; pbfp:=typ.fp;
    IF typ.BaseTyp#NIL THEN FPrint(pvfp, typ.BaseTyp.pvfp);
      FPrint(pbfp, typ.BaseTyp.pbfp)
    END;
    IF typ.size<0 THEN typSize(typ) END; fld:=typ.dsc;
    FPrintMeth(typ, fld);   (* mfix *)
    WHILE (fld#NIL) & (fld.mode=Fld) DO FPrintTyp(fld.typ);
      IF fld.vis#internal THEN
        fp:=0; FPrint(fp, cobjMode[fld.mode]);
        FPrintName(fp, fld.name); FPrint(fp, fld.vis);
        FPrint(fp, fld.typ.fp); fld.fp:=fp;
        FPrint(pbfp, fld.typ.pbfp); FPrint(pbfp, fld.adr);
        FPrint(pvfp, fld.typ.pvfp); FPrint(pvfp, fld.adr);
        FPrint(pvfp, fp); FPrint(pbfp, fp);
        fld:=fld.nxtobj;
      ELSE
        FPrint(pvfp, fld.fp); fld:=fld.nxtobj;
      (*  fp:=fld.adr;  (* include size and pointeradresses *)
        WHILE (fld#NIL) & (fld.mode=Fld) & (fld.vis=internal) DO
          IF fld.typ.form=Pointer THEN FPrint(pvfp, fld.adr) END;
          fld:=fld.nxtobj
        END;
        IF fld#NIL THEN fp:=fld.adr-fp ELSE fp:=typ.size-fp END;
        FPrint(pvfp, fp); *)
      END
    END;
    typ.pbfp := pbfp; typ.pvfp := pvfp; (* replace typ.pbfp with pbfp and typ.pvfp with pvfp *)
  END FPrintRecord;

  PROCEDURE FPrintTyp0(typ: Struct);
    VAR fp: LONGINT; f, c: SHORTINT; btyp: Struct;
  BEGIN
    IF (typ#NIL) & (typ.fpdone#predefMod) THEN
      fp:=0; f:=typ.form; c:=typ.comp; FPrint(fp, f); FPrint(fp, c);
      IF typ.sysflag THEN FPrint(fp, 1) END;
      IF typ.mod#thisMod THEN FPrintName(fp, typ.mod.name); FPrintName(fp, typ.strobj.name);
      END;
      btyp:=typ.BaseTyp; typ.fp:=fp;
      IF (c=Record) & (btyp#NIL) OR (f=Pointer) THEN FPrintTyp0(btyp); FPrint(typ.fp, btyp.fp)
      ELSIF (c=DynArr) OR (c=Array) THEN FPrintTyp0(btyp); FPrint(typ.fp, btyp.fp);
        IF c=Array THEN FPrint(typ.fp, typ.n) END; typ.pbfp:=typ.fp; typ.pvfp:=typ.fp;
      ELSIF f=ProcTyp THEN FPrintSign(typ.fp, btyp, typ.dsc); typ.pbfp:=typ.fp; typ.pvfp:=typ.fp;
      END;
    END
  END FPrintTyp0;

  PROCEDURE FPrintTyp*(typ: Struct);
  BEGIN
    IF (typ#NIL) & (typ.fpdone#SYS.VAL(LONGINT, thisMod)) & (typ.fpdone#predefMod) THEN (* not calculated for this mod *)
      FPrintTyp0(typ);
      IF typ.comp # Record THEN typ.fpdone:=SYS.VAL(LONGINT, thisMod) END;
      IF typ.BaseTyp#NIL THEN FPrintTyp(typ.BaseTyp) END;
      IF typ.comp=Record THEN FPrintRecord(typ) END;
      typ.fpdone:=SYS.VAL(LONGINT, thisMod);
    END;
  END FPrintTyp;

  PROCEDURE FPrintObj*(M: Modules.Module; obj: Object);
    VAR fp: LONGINT; f: INTEGER;
  BEGIN
    fp:=0; thisMod:=M;
    FPrint(fp, cobjMode[obj.mode]); FPrintName(fp, obj.name); FPrint(fp, obj.vis);
    IF obj.mode=Con THEN
      f:=obj.typ.form; FPrint(fp, f); FPrint(fp, obj.typ.comp);
      CASE f OF
      | Bool, Char, SInt, Int, LInt: FPrint(fp, obj.ival);
      | Set: FPrintSet(fp, SYS.VAL(SET, obj.ival));
      | Real: FPrintReal(fp, SYS.VAL(REAL, obj.ival));
      | LReal: FPrintLReal(fp, obj.rval);
      | String: FPrintName(fp, obj.xval^);
      | NilTyp:
      END
    ELSIF obj.mode=Var THEN FPrintTyp(obj.typ); FPrint(fp, obj.typ.fp);
    ELSIF obj.mode=XProc THEN  FPrintSign(fp, obj.typ, obj.par);
    ELSIF obj.mode>XProc THEN FPrintTyp(obj.typ); FPrint(fp, obj.typ.fp);
    END;
    obj.fp:=fp;
  END FPrintObj;

  PROCEDURE DoubleArr*(VAR x: Modules.ArrayPtr);
    VAR i: LONGINT; h: Modules.ArrayPtr;
  BEGIN
    i := LEN(x^); h := x; NEW(x, 2*i);
    ASSERT(x # NIL);
    SYS.MOVE(SYS.ADR(h[0]), SYS.ADR(x[0]), i*SIZE(LONGINT));
  END DoubleArr;

  PROCEDURE ReadScope*(VAR B: Kernel.Buffer; M: Modules.Module; level: SHORTINT; VAR scope: Object; global: BOOLEAN);
    VAR tag: LONGINT; mode: SHORTINT; ch: CHAR; obj, odum: Object; tdum: Struct;
      ndum: Name; idum: INTEGER;

    PROCEDURE^InStruct(VAR typ: Struct);

    (* Cyclic structures require post-processing *)
    PROCEDURE SetTypFlags(typ: Struct);

      PROCEDURE TraverseTProc(fld: Object);
        VAR redef: Object;
      BEGIN
        WHILE fld # NIL DO
          IF fld.mode = TProc THEN
            FindField(fld.name, typ.BaseTyp, redef);
            IF redef # NIL THEN fld.adr := redef.adr
            ELSE fld.adr:=typ.n; INC(typ.n)
            END;
          END;
          fld := fld.nxtobj
        END
      END TraverseTProc;

    BEGIN
      IF (typ.extlev = -1) OR (typ.n < 0) THEN
        IF typ.BaseTyp # NIL THEN SetTypFlags(typ.BaseTyp);
          typ.extlev := typ.BaseTyp.extlev + 1;
          typ.n := typ.BaseTyp.n;
        ELSE typ.extlev := 0; typ.n := 0
        END;
        TraverseTProc(typ.dsc)
      END
    END SetTypFlags;


    PROCEDURE InList(mode: SHORTINT; typ: Struct; VAR first: Object; VAR nofelem: INTEGER); (* mfix *)
      VAR last, elem: Object; dummy0: INTEGER; dummy1: LONGINT; lev: SHORTINT;
    BEGIN
      first:=NIL; last:=NIL; nofelem:=0; Kernel.BufRNum(B, tag);
      WHILE tag<SFtproc DO  NEW(elem); INC(nofelem);
        IF  last=NIL  THEN  first:=elem ELSE  last.nxtobj:=elem END;
        last:=elem; elem.vis:=external;
        IF  tag=SFreadonly  THEN  Kernel.BufRNum(B, tag); elem.vis:=externalR; elem.mode:=mode
        ELSIF tag=SFvar THEN  elem.mode:=VarPar; Kernel.BufRNum(B, tag)
        ELSE  elem.mode:=mode END;
        IF  tag=SFleaf  THEN  Kernel.BufRNum(B, tag)  END;
        InStruct(elem.typ); Kernel.BufRString(B, elem.name);
        IF  (elem.name="") & global THEN  elem.vis:=internal  END;
        Kernel.BufRNum(B, tag)
      END;
      IF  tag=SFtproc THEN  (* skip methods *)
        Kernel.BufRNum(B, tag);
        WHILE tag#SFend DO  NEW(elem); elem.level:=0;
          IF  last=NIL  THEN  first:=elem ELSE  last.nxtobj:=elem END;
          last:=elem; elem.vis:=external; elem.mode:=TProc;
          InStruct(elem.typ); Kernel.BufRString(B, elem.name);
          IF elem.name = "" THEN elem.vis:=internal; Kernel.BufRString(B, elem.name) END;
          lev := level; level := 1; InList(Par, NIL, elem.par, elem.nofpar); level := lev;
          Kernel.BufRNum(B, tag)
        END
      END
    END InList;

    PROCEDURE InStruct(VAR typ: Struct);
      VAR typtag, typadr, modadr: LONGINT; strobj, tobj: Object; btyp: Struct;
        typname: ARRAY 32 OF CHAR; mod: Modules.Module; i: INTEGER; vis: SHORTINT;
    BEGIN
      IF  tag <= 0  THEN  ASSERT(tag>-LEN(M.struct^)); typ:=SYS.VAL(Struct, M.struct[-tag])
      ELSIF tag <= SFtypSptr  THEN  typ:=predefStruct[tag]
      ELSIF tag <= SFmodOther THEN
        IF tag = SFmodOther THEN Kernel.BufRNum(B, tag) ELSE tag:=tag-SFmod1 END;
        mod:=SYS.VAL(Modules.Module, M.import[tag]); Kernel.BufRString(B, typname);
        IF typname[0]#0X THEN btyp:=SYS.VAL(Struct, mod.struct[1]);
          i:=1; WHILE (i<mod.nofstrc) & (btyp.strobj.name#typname) DO INC(i);
            btyp:=SYS.VAL(Struct, mod.struct[i]);
          END;
          IF i<mod.nofstrc THEN typ:=SYS.VAL(Struct, mod.struct[i]); INC(mod.nofreimp);
            IF mod.nofreimp>=LEN(mod.reimp^) THEN DoubleArr(mod.reimp) END;
            mod.reimp[mod.nofreimp]:=SYS.VAL(LONGINT, typ);
          ELSE typ:=niltyp END;
        ELSE Kernel.BufRNum(B, typadr); ASSERT(typadr<LEN(mod.reimp^)); typ:=SYS.VAL(Struct, mod.reimp[typadr]);
        END;
      ELSE  NEW(typ); typ.mod:=M; M.struct[M.nofstrc]:=SYS.VAL(LONGINT, typ); INC(M.nofstrc);
        vis:=internal;
        IF M.nofstrc>=LEN(M.struct^) THEN DoubleArr(M.struct) END;
        IF  tag=SFinvisible THEN  Kernel.BufRNum(B, tag)  ELSIF global  THEN  vis:=external END;
        IF  tag=SFsysflag THEN  Kernel.BufRNum(B, tag); typ.sysflag:=TRUE; Kernel.BufRNum(B, tag) END;
        typ.form:=strucForm[tag]; typ.comp:=strucComp[tag]; typ.size:=-1; typtag:=tag; Kernel.BufRNum(B, tag);
        typ.extlev := -1; InStruct(btyp); typ.BaseTyp:=btyp;
        IF  (typ.form=Pointer) & (typ.BaseTyp=NIL) THEN typ:=ptrtyp; DEC(M.nofstrc); RETURN END;
        NEW(tobj); tobj.mode:=tobjMode[typtag]; tobj.nxtobj:=scope; scope:=tobj; tobj.typ:=typ; Kernel.BufRString(B, tobj.name);
        typ.strobj:=tobj;
        IF  tobj.name#""  THEN  tobj.vis:=vis; NEW(strobj); strobj.mode:=tobjMode[typtag]; COPY(tobj.name, strobj.name);
          strobj.typ:=typ; typ.strobj:=strobj; strobj.vis:=vis;
        ELSE  tobj.vis:=internal  END;
        CASE  typtag  OF
        | SFtypDynArr:
        | SFtypArray: Kernel.BufRNum(B, typ.n)
        | SFtypPointer:
        | SFtypRecord:  InList(Fld, typ, typ.dsc, typ.nofdsc) (* mfix *)
        | SFtypProcTyp: InList(Par, NIL, typ.dsc, typ.nofdsc)
        END;
      END
    END InStruct;

    PROCEDURE InObj;
      VAR o: Object;
    BEGIN NEW(o); o.mode:=mode; o.level:=level; o.nxtobj:=scope; scope:=o;
      IF  tag=SFreadonly  THEN  Kernel.BufRNum(B, tag); o.vis:=externalR
      ELSIF global  THEN  o.vis:=external
      ELSE  o.vis:=internal END;
      IF  tag=SFleaf  THEN  Kernel.BufRNum(B, tag)  END;
      InStruct(o.typ); Kernel.BufRString(B, o.name); obj:=o;
    END InObj;

    PROCEDURE InConst;
      VAR len: INTEGER; r: REAL;
    BEGIN
      CASE  tag OF
      | SFtypBool:  Kernel.BufRNum(B, obj.ival)
      | SFtypChar, SFtypSInt..SFtypLInt, SFtypSet:  Kernel.BufRNum(B, obj.ival)
      | SFtypReal:  Kernel.BufRIEEE4(B, r); obj.ival:=SYS.VAL(LONGINT, r)
      | SFtypLReal: Kernel.BufRIEEE8(B, obj.rval)
      | SFtypString:  NEW(obj.xval); Kernel.BufRString(B, obj.xval^); len:=0; WHILE obj.xval[len]#0X DO INC(len) END; obj.ival:=len+1
      | SFtypNilTyp:
      END
    END InConst;

  BEGIN
    Kernel.BufRNum(B, tag);
    IF  tag=SFconst THEN  mode:=Con; Kernel.BufRNum(B, tag);
      WHILE tag < SFvar DO  InObj; InConst; Kernel.BufRNum(B, tag)  END
    END;
    IF  tag=SFvar THEN  mode:=Var; Kernel.BufRNum(B, tag);
      WHILE tag < SFlproc DO  InObj; Kernel.BufRNum(B, tag) END
    END;
    IF  tag=SFlproc THEN  mode:=LProc; Kernel.BufRNum(B, tag);
      WHILE tag < SFxproc DO  InObj; InList(Par, NIL, obj.par, obj.nofpar); Kernel.BufRNum(B, tag)  END
    END;
    IF  tag=SFxproc THEN  mode:=XProc; Kernel.BufRNum(B, tag);
      WHILE tag < SFcproc DO  InObj; InList(Par, NIL, obj.par, obj.nofpar); Kernel.BufRNum(B, tag)  END
    END;
    IF  tag=SFcproc THEN  Kernel.BufRNum(B, tag);
      WHILE tag < SFalias DO  InStruct(tdum); Kernel.BufRString(B, ndum); InList(Par, NIL, odum, idum); Kernel.BufRCh(B, ch); Kernel.BufSkip(B, ORD(ch)); Kernel.BufRNum(B, tag)  END
    END;
    IF  tag=SFalias THEN  Kernel.BufRNum(B, tag);
      WHILE tag < SFtyp DO  InObj; obj.mode:=TypAlias; Kernel.BufRNum(B, tag)
      END
    END;
    IF  tag=SFtyp THEN  Kernel.BufRNum(B, tag);
      WHILE tag < SFend DO  InStruct(tdum); Kernel.BufRNum(B, tag)  END
    END;
    odum := scope;
    WHILE odum # NIL DO
      IF odum.mode = TypRecord THEN SetTypFlags(odum.typ) END;
      odum := odum.nxtobj
    END
  END ReadScope;


  PROCEDURE EnterTyp(form, tref: SHORTINT; size: LONGINT; VAR typ: Struct; name: Name);
    VAR obj: Object;
  BEGIN NEW(typ); typ.form:=form; typ.comp:=Basic; typ.size:=size;
    predefStruct[tref]:=typ; typ.fpdone:=predefMod; typ.pvfp:=size; typ.pbfp:=form; typ.fp:=form;
    NEW(obj); obj.typ:=typ; obj.name:=name; typ.strobj:=obj
  END EnterTyp;

  PROCEDURE Init;
    VAR M: Modules.Module;
  BEGIN
    M := Modules.modList;
    WHILE M # NIL DO
      IF M.import = NIL THEN NEW(M.import, DefMaxImport) END;
      IF M.struct = NIL THEN NEW(M.struct, DefMaxStruct) END;
      IF M.reimp = NIL THEN NEW(M.reimp, DefMaxReimp) END;
      M := M.link;
    END
  END Init;

BEGIN Init;
  predefMod:=-1;
  EnterTyp(Bool, SFtypBool, 1, booltyp, "BOOLEAN"); EnterTyp(Char, SFtypChar, 1, chartyp, "CHAR");
  EnterTyp(SInt, SFtypSInt, 1, sinttyp, "SHORTINT"); EnterTyp(Int, SFtypInt, 2, inttyp, "INTEGER");
  EnterTyp(LInt, SFtypLInt, 4, linttyp, "LONGINT");
  EnterTyp(Real, SFtypReal, 4, realtyp, "REAL"); EnterTyp(LReal, SFtypLReal, 8, lrltyp, "LONGREAL");
  EnterTyp(Set, SFtypSet, 4, settyp, "SET"); EnterTyp(String, SFtypString, 0, stringtyp, "STRING");
  EnterTyp(NilTyp, SFtypNilTyp, 4, niltyp, "NIL"); EnterTyp(NoTyp, SFtypNoTyp, 0, notyp, "NOTYP");
  EnterTyp(Pointer, SFtypPointer, 4, ptrtyp, "PTR"); EnterTyp(Pointer, SFtypSptr, 4, sysptrtyp, "POINTER");
  EnterTyp(ProcTyp, SFtypProcTyp, 4, proctyp, "PROC");
  predefStruct[SFtypByte]:=chartyp;
  strucForm[SFtypPointer]:=Pointer; strucForm[SFtypRecord]:=Comp; strucForm[SFtypProcTyp]:=ProcTyp;
  strucForm[SFtypDynArr]:=Comp; strucForm[SFtypArray]:=Comp;
  strucComp[SFtypPointer]:=Basic; strucComp[SFtypRecord]:=Record; strucComp[SFtypProcTyp]:=Basic;
  strucComp[SFtypDynArr]:=DynArr; strucComp[SFtypArray]:=Array;
  tobjMode[SFtypPointer]:=TypPointer; tobjMode[SFtypRecord]:=TypRecord; tobjMode[SFtypProcTyp]:=TypProcTyp;
  tobjMode[SFtypDynArr]:=TypDynArr; tobjMode[SFtypArray]:=TypArray;
  cobjMode[Var]:=1; cobjMode[Par]:=1; cobjMode[VarPar]:=2; cobjMode[Con]:=3; cobjMode[Fld]:=4;
  cobjMode[XProc]:=7; cobjMode[TypDynArr]:=5; cobjMode[TypArray]:=5; cobjMode[TypPointer]:=5;
  cobjMode[TypRecord]:=5; cobjMode[TypProcTyp]:=5; cobjMode[TypAlias]:=5;
END OPLT.