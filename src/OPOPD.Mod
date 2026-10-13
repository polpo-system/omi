MODULE OPOPD;  (* polpo: the decoder of slim binaries, for polpo's x86 compiler *)

(* Reads a slim binary written by OPOPV and rebuilds what polpo's parser (OPP) would have made of
   the source: the objects in the scopes of OPT and the syntax tree of the module, so that the x86
   back end (OPV, OPC, OPL) can compile it to a native object.

   The node dictionary is the one of the encoder, kept step for step: every node the encoder made
   is made here at the same index (global nodes from Ttrap+1 up, local ones from -1 down), and a
   number in the stream either starts a new node (a tag, 0..Ttrap) or refers to one of them.
   M. Franz's loader of mac oberon (mac/PPC.OPL2, OPLT, OPLV) does the same for the powerpc; this
   one builds OPT trees instead of code. *)

  IMPORT SYSTEM, Files, OPS, OPT, OPM, OPB;

  CONST
    (* object modes *)
    Var=1; VarPar=2; Con=3; Fld=4; Typ=5; LProc=6; XProc=7; CProc=9; Mod=11; Head=12; TProc=13;
    (* forms *)
    Bool=2; Char=3; SInt=4; Int=5; LInt=6; Real=7; LReal=8; Set=9; String=10; NilTyp=11; NoTyp=12;
    Pointer=13; ProcTyp=14; Comp=15;
    Basic=1; StaticArr=2; SDynArr=3; DynArr=4; OpenArr=5; Record=6;
    (* visibility *)
    internal=0; external=1; externalR=2;
    (* ops *)
    times=1; slash=2; div=3; mod=4; and=5; plus=6; minus=7; or=8; eql=9; neq=10; lss=11; leq=12; gtr=13;
    geq=14; in=15; is=16; ash=17; msk=18; len=19; conv=20; abs=21; cap=22; odd=23; not=33;
    assign=0; newfn=1; incfn=13; decfn=14; inclfn=15; exclfn=16; copyfn=18; assertfn=32;
    getfn=24; putfn=25; sysnewfn=30; movefn=31;
    adr=24; bit=26; lsh=27; rot=28; val=29; get8=30; get16=31; get32=32;
    (* node classes *)
    Nvar=0; Nvarpar=1; Nfield=2; Nderef=3; Nindex=4; Nguard=5; Neguard=6; Nconst=7; Nproc=9;
    Nupto=10; Nmop=11; Ndop=12; Ncall=13; Ninittd=14; Nif=15; Ncaselse=16; Ncasedo=17; Nenter=18;
    Nassign=19; Nifelse=20; Ncase=21; Nwhile=22; Nrepeat=23; Nloop=24; Nexit=25; Nreturn=26;
    Nwith=27; Ntrap=28;
    (* procedure and type flags of polpo's OPT *)
    hasBody=1; protectedObj=4; systemtype=6;
    (* tags of the stream (OPOPV) *)
    Tend=00H; Telsif=01H; Telse=02H; Twend=03H; Tcastrap=04H; Tcaslbl1=05H; Tcasrng1=06H; Tcaslbl2=07H; Tcasrng2=08H;
    Tbegin=09H; TconstNil=00H; TconstFalse=01H; TconstTrue=02H; TconstChar=03H;
    TconstSInt=04H; TconstInt=05H; TconstLInt=06H; TconstSet=07H; TconstReal=08H; TconstLReal=09H; TconstString=0AH;
    Tderef=0BH; Tindex=0CH; TmopNot=0DH; TmopMinus=0EH; TmopAbs=0FH; TmopCap=10H; TmopOdd=11H;
    TdopAnd=12H; TdopOr=13H; TdopTimes=14H; TdopSlash=15H; TdopDiv=16H; TdopMod=17H;
    TdopPlus=18H; TdopMinus=19H; TdopMsk=1AH; TdopAsh=1BH; TdopLen=1CH; TdopIn=1DH;
    TdopEql=1EH; TdopNeq=1FH; TdopLss=20H; TdopLeq=21H; TdopGtr=22H; TdopGeq=23H; Tupto=24H;
    Tcall=25H; TasgnNewfn=26H; TasgnAssign=27H; TasgnIncfn=28H; TasgnDecfn=29H; TasgnInclfn=2AH; TasgnExclfn=2BH;
    TasgnCopyfn=2CH; Tassert=2DH; Tif=2EH; Tcase=2FH; Twhile=30H; Trepeat=31H; Tloop=32H; Texit=33H; Twith=34H; Ttrap=35H;
    TsysAdr=36H; TsysBit=37H; TsysLsh=38H; TsysRot=39H; TsysGet8=3AH; TsysGet16=3BH; TsysGet32=3CH;
    TsysGet=3DH; TsysPut=3EH; TsysNew=3FH; TsysMove=40H; TlastTag=40H;
    Uvar=50H; Uvarpar=51H; Uproc=52H; Ufield=53H; Uguard=54H; Ueguard=55H; UmopIs=56H; UmopConv=57H; Uenter=58H; Ureturn=59H;
    UsysVal=5AH;
    flgOK=0; flgNoLeft=-1; flgNoRight=-2; flgEnter=-3;
    Global=TRUE; Local=FALSE;
    EUEnd=0; EURecord=1;
    (* symbol file tags (OPT) *)
    SFtypBool=01H; SFtypChar=02H; SFtypSInt=03H; SFtypInt=04H; SFtypLInt=05H; SFtypHInt=06H;
    SFtypReal=07H; SFtypLReal=08H; SFtypSet=09H; SFtypString=0AH; SFtypNoTyp=0BH; SFtypNilTyp=0CH;
    SFtypByte=0DH; SFtypptr=0EH; SFlastStruct=0EH;
    SFmod1=0FH; SFmodOther=2DH;
    SFtypOpenArr=2EH; SFtypDynArr=2FH; SFtypArray=30H; SFtypPointer=31H; SFtypRecord=32H; SFtypProcTyp=33H;
    SFsysflag=34H; SFinvisible=35H; SFreadonly=36H; SFobjflag=37H;
    SFconst=37H; SFvar=38H; SFlproc=39H; SFxproc=3AH; SFoperator=3BH; SFtproc=3CH; SFcproc=3CH;
    SFalias=3DH; SFtyp=3EH; SFend=3FH;
    OFtag=0BBX; OFportable=088X;
    MaxMods=64;

  TYPE
    DNode = POINTER TO DNodeDesc;  (* a node of the dictionary *)
    DNodeDesc = RECORD
      tag: INTEGER; flag, subflg: SHORTINT; super: BOOLEAN;
      typ: OPT.Struct; obj: OPT.Object; conval: OPT.Const;
      left, right: DNode; global: BOOLEAN
    END;
    DArr = POINTER TO ARRAY OF DNode;
    SArr = POINTER TO ARRAY OF OPT.Struct;
    Alias = POINTER TO AliasDesc;  (* a variable in a WITH, as polpo's parser declares it *)
    AliasDesc = RECORD orig, obj: OPT.Object; next: Alias END;

  VAR
    R: Files.Rider; tok: LONGINT;
    glob, loc: DArr; above, below: LONGINT;
    bstk: ARRAY 256 OF LONGINT; dsp: INTEGER;
    objects: OPT.Object;  (* as OPT.objects in the encoder: the order of GenNodes *)
    structs: SArr; nofstruc: LONGINT;
    emods: ARRAY MaxMods OF OPT.Module; nofemods: INTEGER;
    reimp: ARRAY MaxMods OF SArr; nofreimp: ARRAY MaxMods OF INTEGER;
    predef: ARRAY SFlastStruct+1 OF OPT.Struct;
    level: SHORTINT;
    TDinit, lastTDinit: OPT.Node;
    vars: OPT.Object;  (* the last variable of the scope being read, for the list in topScope.scope *)
    declScope: OPT.Object;  (* the scope whose declarations are read: named types go there *)
    aliases: Alias;
    nilNode, falseNode, trueNode: DNode;
    mopOf, dopOf: ARRAY TlastTag+1 OF SHORTINT;  (* the subclass of a tag *)
    modName: OPS.Name;

  PROCEDURE Err(n: INTEGER);
  BEGIN OPM.err(n)
  END Err;

  PROCEDURE ErrObj(n: INTEGER; VAR mod, name: ARRAY OF CHAR; fp, fp2: LONGINT);  (* an error about an imported object *)
  BEGIN OPM.LogWLn; OPM.LogWStr("  "); OPM.LogWStr(mod); OPM.LogW("."); OPM.LogWStr(name);
    OPM.LogWStr(" fingerprint "); OPM.LogWHex(fp2); OPM.LogWStr(", the slim binary has "); OPM.LogWHex(fp);
    OPM.err(n)
  END ErrObj;

  PROCEDURE Next;
  BEGIN Files.ReadNum(R, tok)
  END Next;

  PROCEDURE ReadString(VAR string: ARRAY OF CHAR);  (* as OPT: the last character + 80H ends it, 7FX starts a plain rest *)
    VAR i: INTEGER; ch: CHAR;
  BEGIN i := 0;
    LOOP Files.Read(R, ch);
      IF ch = 0X THEN string[i] := 0X; RETURN
      ELSIF ch < 7FX THEN string[i] := ch; INC(i)
      ELSIF ch > 7FX THEN string[i] := CHR(ORD(ch)-80H); string[i+1] := 0X; RETURN
      ELSE EXIT END
    END;
    LOOP Files.Read(R, ch);
      IF ch = 0X THEN string[i] := 0X; RETURN ELSE string[i] := ch; INC(i) END
    END
  END ReadString;

  (* ---------- scopes, as the parser builds them ---------- *)

  PROCEDURE Find(root: OPT.Object; VAR name: ARRAY OF CHAR): OPT.Object;  (* in a scope tree *)
  BEGIN
    WHILE (root # NIL) & (root.name # name) DO
      IF name < root.name THEN root := root.left ELSE root := root.right END
    END;
    RETURN root
  END Find;

  PROCEDURE InsertInto(scope, obj: OPT.Object);  (* an object made already, into a scope *)
    VAR ob0, ob1: OPT.Object; left: BOOLEAN;
  BEGIN ob0 := scope; ob1 := ob0.right; left := FALSE;
    WHILE ob1 # NIL DO
      ob0 := ob1;
      IF obj.name < ob1.name THEN ob1 := ob1.left; left := TRUE ELSE ob1 := ob1.right; left := FALSE END
    END;
    IF left THEN ob0.left := obj ELSE ob0.right := obj END;
    obj.left := NIL; obj.right := NIL; obj.mnolev := scope.mnolev
  END InsertInto;

  PROCEDURE InsertObj(obj: OPT.Object);
  BEGIN InsertInto(OPT.topScope, obj)
  END InsertObj;

  PROCEDURE Prepend(obj: OPT.Object);
  BEGIN obj.nxtobj := objects; objects := obj
  END Prepend;

  PROCEDURE AddVar(obj: OPT.Object);  (* to the list of variables of topScope (VarAdr allocates them) *)
  BEGIN obj.link := NIL;
    IF vars = NIL THEN OPT.topScope.scope := obj ELSE vars.link := obj END;
    vars := obj
  END AddVar;

  (* ---------- symbol stream ---------- *)

  PROCEDURE ^ InStruct(VAR typ: OPT.Struct);

  PROCEDURE InParList(VAR first: OPT.Object);  (* parameters: not inserted yet, linked by link and nxtobj *)
    VAR last, par: OPT.Object;
  BEGIN first := NIL; last := NIL; Next;
    WHILE tok # SFend DO
      par := OPT.NewObj(); par.flag := {OPT.param};
      IF tok = SFvar THEN par.mode := VarPar; Next ELSE par.mode := Var END;
      InStruct(par.typ); ReadString(par.name); par.conval := OPT.NewConst();
      IF last = NIL THEN first := par ELSE last.link := par; last.nxtobj := par END;
      last := par; Next
    END
  END InParList;

  PROCEDURE InRecord(typ: OPT.Struct);
    VAR flags: LONGINT; prio: CHAR; fld, last: OPT.Object; owner, outer: OPT.Object; v: OPT.Object;
  BEGIN
    owner := typ.strobj; Files.ReadNum(R, flags); Files.Read(R, prio);
    outer := OPT.topScope; v := vars; OPT.OpenScope(0, owner); last := NIL;
    Next;
    WHILE (tok # SFend) & (tok # SFtproc) DO
      fld := OPT.NewObj(); fld.mode := Fld; fld.conval := OPT.NewConst(); fld.vis := external;
      IF tok = SFobjflag THEN Files.Read(R, fld.sysflag); Next END;
      IF tok = SFreadonly THEN fld.vis := externalR; Next END;
      InStruct(fld.typ); ReadString(fld.name);
      IF fld.name = "" THEN fld.vis := internal ELSE InsertObj(fld) END;
      fld.myscope := OPT.topScope;
      IF last = NIL THEN typ.link := fld ELSE last.link := fld END;
      last := fld; Next
    END;
    IF tok = SFtproc THEN Err(507) (* methods: not yet *) END;
    OPT.topScope := outer; vars := v
  END InRecord;

  PROCEDURE NewOwnStruct(VAR typ: OPT.Struct; tag: LONGINT);  (* a structure of the module itself *)
    VAR vis, sysflag: SHORTINT; btyp: OPT.Struct; tobj, hidden: OPT.Object; name: OPS.Name; n: LONGINT;
  BEGIN
    vis := external; sysflag := 0;
    IF tag = SFinvisible THEN vis := internal; Next; tag := tok END;
    IF tag = SFsysflag THEN Next; sysflag := SHORT(SHORT(tok)); Next; tag := tok END;
    CASE tag OF
    | SFtypOpenArr: typ := OPT.NewStr(Comp, OpenArr)
    | SFtypDynArr: typ := OPT.NewStr(Comp, DynArr)
    | SFtypArray: typ := OPT.NewStr(Comp, StaticArr)
    | SFtypPointer: typ := OPT.NewStr(Pointer, Basic)
    | SFtypRecord: typ := OPT.NewStr(Comp, Record)
    | SFtypProcTyp: typ := OPT.NewStr(ProcTyp, Basic)
    END;
    INC(nofstruc); IF nofstruc >= LEN(structs^) THEN Err(508); nofstruc := 1 END;
    structs[nofstruc] := typ; n := nofstruc;
    typ.sysflag := sysflag; typ.mno := 0; typ.size := -1; typ.incomplete := FALSE;
    tobj := OPT.NewObj(); tobj.mode := Typ; tobj.typ := typ; tobj.conval := OPT.NewConst();
    typ.strobj := tobj;  (* named or not, the parser gives every record an owner *)
    Next; InStruct(btyp);  (* base type, as OutStruct writes it *)
    Prepend(tobj);
    ReadString(name); hidden := NIL;
    IF (name = OPT.Delegate) OR (name = OPT.HdPtrStruct) THEN hidden := Find(OPT.topScope.right, name) END;
    IF hidden # NIL THEN COPY(name, tobj.name)  (* made already, as the parser does: read into the copy, keep the first *)
    ELSIF name # "" THEN COPY(name, tobj.name); tobj.vis := vis; InsertInto(declScope, tobj)  (* not into a record read now *)
    END;
    CASE tag OF
    | SFtypOpenArr, SFtypDynArr:
        typ.BaseTyp := btyp;
        IF btyp.comp = typ.comp THEN typ.n := btyp.n + 1 ELSE typ.n := 0 END
    | SFtypArray: typ.BaseTyp := btyp; Files.ReadNum(R, typ.n)
    | SFtypPointer: typ.BaseTyp := btyp;
        IF (btyp.comp = Record) & (btyp.strobj.name = "") THEN btyp.ptr := typ END
    | SFtypRecord:
        IF (btyp = OPT.notyp) OR (btyp = OPT.niltyp) THEN typ.BaseTyp := NIL
        ELSIF btyp.form = Pointer THEN typ.BaseTyp := btyp.BaseTyp
        ELSE typ.BaseTyp := btyp
        END;
        IF typ.BaseTyp # NIL THEN typ.extlev := typ.BaseTyp.extlev + 1 ELSE typ.extlev := 0 END;
        InRecord(typ);
        IF sysflag # systemtype THEN OPB.Inittd(TDinit, lastTDinit, typ) END
    | SFtypProcTyp: typ.BaseTyp := btyp; InParList(typ.link)
    END;
    IF hidden # NIL THEN structs[n] := hidden.typ; tobj.typ := hidden.typ END
  END NewOwnStruct;

  PROCEDURE InStruct(VAR typ: OPT.Struct);  (* the structure whose tag is in tok *)
    VAR m, k: LONGINT; name: OPS.Name; obj: OPT.Object; mod: OPT.Module;
  BEGIN
    IF tok <= 0 THEN m := 1 - tok;  (* own structure written before: -n+1 *)
      IF (m < 1) OR (m > nofstruc) THEN Err(509); typ := OPT.undftyp ELSE typ := structs[m] END
    ELSIF tok <= SFlastStruct THEN typ := predef[tok]
    ELSIF tok <= SFmodOther THEN
      IF tok = SFmodOther THEN Files.ReadNum(R, m); INC(m) ELSE m := tok - SFmod1 + 1 END;
      IF (m < 1) OR (m > nofemods) THEN Err(510); typ := OPT.undftyp; RETURN END;
      mod := emods[m]; ReadString(name);
      IF name # "" THEN
        obj := Find(mod.right, name);
        IF (obj = NIL) OR (obj.mode # Typ) THEN Err(511); typ := OPT.undftyp ELSE typ := obj.typ END;
        INC(nofreimp[m]); IF nofreimp[m] >= LEN(reimp[m]^) THEN Err(508); nofreimp[m] := 1 END;
        reimp[m][nofreimp[m]] := typ
      ELSE Files.ReadNum(R, k); INC(k);  (* the k-th structure of mod written before *)
        IF k > nofreimp[m] THEN Err(511); typ := OPT.undftyp ELSE typ := reimp[m][k] END
      END
    ELSE NewOwnStruct(typ, tok)
    END
  END InStruct;

  PROCEDURE InObj(mode: SHORTINT; vis: SHORTINT): OPT.Object;  (* OutObj: struct, then the name *)
    VAR obj: OPT.Object;
  BEGIN
    obj := OPT.NewObj(); obj.mode := mode; obj.vis := vis; obj.conval := OPT.NewConst();
    IF tok = SFobjflag THEN Files.Read(R, obj.sysflag); Next END;
    IF tok = SFreadonly THEN obj.vis := externalR; Next END;
    Prepend(obj);  (* before its structure, as OutObj *)
    InStruct(obj.typ); ReadString(obj.name);
    IF obj.name[0] = "&" THEN Err(507) END;
    InsertObj(obj);
    RETURN obj
  END InObj;

  PROCEDURE InConst(obj: OPT.Object);
    VAR r: REAL; s: LONGINT;
  BEGIN
    CASE obj.typ.form OF
    | Bool, Char, SInt, Int, LInt: Files.ReadNum(R, obj.conval.intval)
    | Set: Files.ReadNum(R, SYSTEM.VAL(LONGINT, obj.conval.setval))
    | Real: Files.ReadReal(R, r); obj.conval.realval := r; obj.conval.intval := OPM.ConstNotAlloc
    | LReal: Files.ReadLReal(R, obj.conval.realval); obj.conval.intval := OPM.ConstNotAlloc
    | String: obj.conval.ext := OPT.NewExt(); ReadString(obj.conval.ext^);
        s := 0; WHILE obj.conval.ext[s] # 0X DO INC(s) END;
        obj.conval.intval := OPM.ConstNotAlloc; obj.conval.intval2 := s + 1
    | NilTyp:
    END
  END InConst;

  PROCEDURE DeclareParams(proc: OPT.Object);  (* the scope of a procedure with its parameters *)
    VAR outer, par: OPT.Object;
  BEGIN
    outer := OPT.topScope; OPT.OpenScope(level+1, proc); OPT.topScope.conval := OPT.NewConst();
    par := proc.link; WHILE par # NIL DO InsertObj(par); par := par.link END;
    OPT.topScope := outer
  END DeclareParams;

  PROCEDURE ReadScope(vis: SHORTINT);  (* a scope as OutScope writes it, up to SFend *)
    VAR obj: OPT.Object; mode: SHORTINT; dum: OPT.Struct;
  BEGIN
    declScope := OPT.topScope; Next;
    IF tok = SFconst THEN Next;
      WHILE tok < SFvar DO obj := InObj(Con, vis); InConst(obj); Next END
    END;
    IF tok = SFvar THEN Next;
      WHILE tok < SFlproc DO obj := InObj(Var, vis); obj.leaf := vis = internal; AddVar(obj); Next END
    END;
    IF tok = SFlproc THEN Next;
      WHILE tok < SFxproc DO
        obj := InObj(LProc, vis); InParList(obj.link); obj.conval.setval := {hasBody}; DeclareParams(obj); Next
      END
    END;
    IF tok = SFxproc THEN Next;
      WHILE tok < SFoperator DO
        obj := InObj(XProc, vis); InParList(obj.link); obj.conval.setval := {hasBody}; DeclareParams(obj); Next
      END
    END;
    IF tok = SFoperator THEN Err(507) END;
    IF tok = SFcproc THEN Err(505) END;
    IF tok = SFalias THEN Next;  (* TYPE A = B: an object of the type, not in the list of OutObj *)
      WHILE tok < SFtyp DO
        obj := OPT.NewObj(); obj.mode := Typ; obj.vis := vis; obj.conval := OPT.NewConst();
        InStruct(obj.typ); ReadString(obj.name); InsertObj(obj); Next
      END
    END;
    IF tok = SFtyp THEN Next;
      WHILE tok < SFend DO InStruct(dum); Next END
    END;
    IF tok # SFend THEN Err(512) END
  END ReadScope;

  PROCEDURE Imports;  (* module names up to 0X: import them as the parser does *)
    VAR name: OPS.Name; i: INTEGER;
  BEGIN ReadString(name);
    WHILE name # "" DO
      OPT.Import(name, name, modName);
      i := 1; WHILE (i < OPT.nofmod) & (OPT.modules[i].name # name) DO INC(i) END;
      IF (i < OPT.nofmod) & (nofemods < MaxMods-1) THEN
        INC(nofemods); emods[nofemods] := OPT.modules[i];
        NEW(reimp[nofemods], 256); nofreimp[nofemods] := 0
      ELSE Err(152)
      END;
      ReadString(name)
    END
  END Imports;

  (* ---------- the dictionary, as the encoder keeps it ---------- *)

  PROCEDURE PushDict;
  BEGIN bstk[dsp] := below; INC(dsp)
  END PushDict;

  PROCEDURE PopDict;
  BEGIN DEC(dsp); below := bstk[dsp]
  END PopDict;

  PROCEDURE Put(n: DNode; global: BOOLEAN);
  BEGIN n.global := global;
    IF global THEN
      IF above >= LEN(glob^) THEN Err(513) ELSE glob[above] := n END; INC(above)
    ELSE
      IF -below >= LEN(loc^) THEN Err(513) ELSE loc[-below] := n END; DEC(below)
    END
  END Put;

  PROCEDURE NNode(tag: INTEGER; typ: OPT.Struct; obj: OPT.Object; left, right: DNode; global: BOOLEAN): DNode;
    VAR n: DNode;
  BEGIN NEW(n); n.tag := tag; n.typ := typ; n.obj := obj; n.left := left; n.right := right; Put(n, global); RETURN n
  END NNode;

  PROCEDURE UNodeO(tag: INTEGER; flag: SHORTINT; typ: OPT.Struct; obj: OPT.Object; global: BOOLEAN);
    VAR n: DNode;
  BEGIN NEW(n); n.tag := tag; n.flag := flag; n.typ := typ; n.obj := obj; Put(n, global)
  END UNodeO;

  PROCEDURE UNodeLR(tag: INTEGER; flag: SHORTINT; typ: OPT.Struct; left, right: DNode; global: BOOLEAN);
    VAR n: DNode;
  BEGIN NEW(n); n.tag := tag; n.flag := flag; n.typ := typ; n.left := left; n.right := right; Put(n, global)
  END UNodeLR;

  PROCEDURE PNode(p: DNode; remain, match: SHORTINT; par: DNode; global: BOOLEAN): DNode;
    VAR n: DNode;
  BEGIN NEW(n); n.tag := Tcall; n.flag := remain; n.subflg := match; n.left := p; n.right := par;
    n.super := p.super; Put(n, global); RETURN n
  END PNode;

  PROCEDURE ConstNode(tag: INTEGER; conval: OPT.Const): DNode;
    VAR n: DNode;
  BEGIN NEW(n); n.tag := tag; n.conval := conval; Put(n, Global); RETURN n
  END ConstNode;

  PROCEDURE NofPar(par: OPT.Object): SHORTINT;
    VAR n: SHORTINT;
  BEGIN n := 0; WHILE par # NIL DO INC(n); par := par.link END; RETURN n
  END NofPar;

  PROCEDURE ConstTag(form: SHORTINT): INTEGER;
  BEGIN
    CASE form OF
    | Char: RETURN TconstChar | SInt: RETURN TconstSInt | Int: RETURN TconstInt | LInt: RETURN TconstLInt
    | Real: RETURN TconstReal | LReal: RETURN TconstLReal | Set: RETURN TconstSet | String: RETURN TconstString
    | NilTyp: RETURN TconstNil
    END
  END ConstTag;

  PROCEDURE VarNodes(n: DNode; typ: OPT.Struct; global: BOOLEAN);
    VAR d: DNode;
  BEGIN
    UNodeLR(TasgnAssign, flgNoLeft, NIL, NIL, n, global);
    UNodeLR(TasgnAssign, flgNoRight, NIL, n, NIL, global);
    IF typ.form = Pointer THEN d := NNode(Tderef, typ.BaseTyp, NIL, n, NIL, global)
    ELSIF typ.comp IN {StaticArr, SDynArr, DynArr, OpenArr} THEN UNodeLR(Tindex, flgNoRight, typ.BaseTyp, n, NIL, global)
    END
  END VarNodes;

  PROCEDURE GenNodes(obj: OPT.Object; external, global: BOOLEAN);  (* as GenNodes of the encoder *)
    VAR n, d: DNode; fld: OPT.Object;
  BEGIN
    WHILE obj # NIL DO
      IF obj.mode IN {Var, VarPar} THEN
        IF obj.mode = Var THEN n := NNode(Uvar, NIL, obj, NIL, NIL, global) ELSE n := NNode(Uvarpar, NIL, obj, NIL, NIL, global) END;
        IF ~external THEN VarNodes(n, obj.typ, global) END
      ELSIF obj.mode = Typ THEN
        UNodeO(UsysVal, flgNoLeft, obj.typ, NIL, global);
        IF (obj.typ.form = Pointer) OR (obj.typ.comp = Record) THEN
          UNodeO(Uguard, flgNoLeft, obj.typ, NIL, global);
          UNodeO(Ueguard, flgNoLeft, obj.typ, NIL, global);
          UNodeO(UmopIs, flgNoLeft, obj.typ, NIL, global);
          IF obj.typ.comp = Record THEN fld := obj.typ.link;
            WHILE fld # NIL DO
              IF fld.mode = Fld THEN UNodeO(Ufield, flgNoLeft, NIL, fld, global) END;
              fld := fld.link
            END
            (* type-bound procedures: not yet (refused when the record is read) *)
          END
        END
      ELSIF obj.mode IN {LProc, XProc} THEN
        n := NNode(Uproc, NIL, obj, NIL, NIL, global);
        d := NNode(Tcall, NIL, obj.link, n, NIL, global); d.flag := NofPar(obj.link);
        IF ~external THEN UNodeO(Uenter, flgEnter, NIL, obj, global) END
      ELSIF (obj.mode = Con) & (obj.typ.form # Bool) THEN d := ConstNode(ConstTag(obj.typ.form), obj.conval)
      END;
      obj := obj.nxtobj
    END
  END GenNodes;

  (* ---------- the export/use section ---------- *)

  PROCEDURE ^ UseRecord(typ: OPT.Struct; mno: INTEGER);

  PROCEDURE UseTyp(typ: OPT.Struct; mno: INTEGER);  (* arrays and pointers down to a record, as Use *)
  BEGIN
    WHILE (typ # NIL) & ((typ.form = Comp) & (typ.comp # Record) OR (typ.form = Pointer)) DO
      IF typ.form = Pointer THEN
        UNodeO(Uguard, flgNoLeft, typ, NIL, Global); UNodeO(Ueguard, flgNoLeft, typ, NIL, Global);
        UNodeO(UmopIs, flgNoLeft, typ, NIL, Global)
      END;
      typ := typ.BaseTyp
    END;
    IF (typ # NIL) & (typ.form = Comp) & (typ.comp = Record) THEN UseRecord(typ, mno) END
  END UseTyp;

  PROCEDURE UseRecord(typ: OPT.Struct; mno: INTEGER);
    VAR fp: LONGINT; name: OPS.Name; fld: OPT.Object;
  BEGIN
    IF (typ.oref = 0) & (typ.mno = mno) THEN
      UNodeO(Uguard, flgNoLeft, typ, NIL, Global); UNodeO(Ueguard, flgNoLeft, typ, NIL, Global);
      UNodeO(UmopIs, flgNoLeft, typ, NIL, Global);
      Next; IF tok # EURecord THEN Err(514) END;
      typ.oref := -1; OPT.FPrintTyp(typ);  (* the fingerprints of the fields, as UseRecord of the encoder *)
      Next;
      IF (tok = EURecord) & (typ.BaseTyp # NIL) & (typ.BaseTyp.oref = 0) & (typ.BaseTyp.mno = mno) THEN
        (* the base record was used too: its block comes first *)
        Files.Set(R, Files.Base(R), Files.Pos(R) - 1); UseRecord(typ.BaseTyp, mno); Next
      END;
      WHILE tok # EUEnd DO
        fp := tok; ReadString(name);
        fld := typ.link; WHILE (fld # NIL) & (fld.name # name) DO fld := fld.link END;
        IF (fld = NIL) OR (fld.mode # Fld) THEN Err(507)
        ELSE
          IF fld.fp # fp THEN ErrObj(515, typ.strobj.name, name, fp, fld.fp) END;
          OPT.MarkObj(fld);
          UNodeO(Ufield, flgNoLeft, NIL, fld, Global); UseTyp(fld.typ, mno)
        END;
        Next
      END
    END
  END UseRecord;

  (* the use section fingerprints imported types and marks records (fpdone, oref) as the encoder did; the
     parser computes no fingerprints that early, and Export and OPL would take these over: undone *)
  PROCEDURE ResetTyp(typ: OPT.Struct);
    VAR fld: OPT.Object;
  BEGIN
    IF (typ # NIL) & ((typ.fpdone > 0) OR (typ.oref # 0)) THEN
      typ.fpdone := 0; typ.oref := 0;
      ResetTyp(typ.BaseTyp);
      IF (typ.comp = Record) OR (typ.form = ProcTyp) THEN
        fld := typ.link; WHILE fld # NIL DO ResetTyp(fld.typ); fld := fld.link END
      END
    END
  END ResetTyp;

  PROCEDURE ResetScope(obj: OPT.Object);
    VAR par: OPT.Object;
  BEGIN
    IF obj # NIL THEN
      ResetScope(obj.left);
      IF obj.typ # NIL THEN ResetTyp(obj.typ) END;
      IF obj.mode = XProc THEN par := obj.link; WHILE par # NIL DO ResetTyp(par.typ); par := par.link END END;
      ResetScope(obj.right)
    END
  END ResetScope;

  PROCEDURE UseSection;
    VAR name: OPS.Name; i: INTEGER; fp: LONGINT; obj: OPT.Object; n, d: DNode;
  BEGIN
    ReadString(name);
    WHILE name # "" DO
      i := 1; WHILE (i < OPT.nofmod) & (OPT.modules[i].name # name) DO INC(i) END;
      IF i = OPT.nofmod THEN Err(152); RETURN END;
      OPT.modNo := i;
      Next;
      WHILE tok # EUEnd DO
        fp := tok; ReadString(name);
        obj := Find(OPT.modules[i].right, name);
        IF obj = NIL THEN Err(516); RETURN END;
        OPT.FPrintObj(obj); IF obj.fp # fp THEN ErrObj(515, OPT.modules[i].name, name, fp, obj.fp) END;
        OPT.MarkObj(obj);  (* used: the object file lists it, as the parser marks it *)
        IF obj.mode = Var THEN n := NNode(Uvar, NIL, obj, NIL, NIL, Global)
        ELSIF obj.mode = XProc THEN
          n := NNode(Uproc, NIL, obj, NIL, NIL, Global);
          d := NNode(Tcall, NIL, obj.link, n, NIL, Global); d.flag := NofPar(obj.link)
        ELSIF (obj.mode = Con) & (obj.typ.form # Bool) THEN d := ConstNode(ConstTag(obj.typ.form), obj.conval)
        ELSIF obj.mode = Typ THEN UNodeO(UsysVal, flgNoLeft, obj.typ, NIL, Global)
        ELSIF obj.mode = CProc THEN Err(505)
        END;
        IF obj.mode IN {Typ, Var} THEN UseTyp(obj.typ, i) END;
        Next
      END;
      ReadString(name)
    END;
    i := 1; WHILE i < OPT.nofmod DO ResetScope(OPT.modules[i].right); INC(i) END;
    OPT.modNo := 0
  END UseSection;

  (* ---------- trees ---------- *)

  PROCEDURE Current(obj: OPT.Object): OPT.Object;  (* a variable, or its WITH object while the WITH lasts *)
    VAR a: Alias;
  BEGIN a := aliases;
    WHILE (a # NIL) & (a.orig # obj) DO a := a.next END;
    IF a # NIL THEN RETURN a.obj ELSE RETURN obj END
  END Current;

  PROCEDURE CopyConst(c: OPT.Const): OPT.Const;
    VAR d: OPT.Const;
  BEGIN d := OPT.NewConst(); d^ := c^; RETURN d
  END CopyConst;

  PROCEDURE NewNode(class, subcl: SHORTINT; typ: OPT.Struct; left, right: OPT.Node): OPT.Node;
    VAR n: OPT.Node;
  BEGIN n := OPT.NewNode(class); n.subcl := subcl; n.typ := typ; n.left := left; n.right := right; RETURN n
  END NewNode;

  PROCEDURE Stat(class, subcl: SHORTINT; left, right: OPT.Node): OPT.Node;  (* a statement, with a text position *)
    VAR n: OPT.Node;
  BEGIN n := NewNode(class, subcl, OPT.notyp, left, right); n.conval := OPT.NewConst(); RETURN n
  END Stat;

  (* as the parser: a variable of another level is no leaf; one of an enclosing procedure, or a call of a
     procedure local to one, needs the static link of the procedures in between (OPB.StaticLink) *)
  PROCEDURE Level(obj: OPT.Object);
    VAR lev: SHORTINT;
  BEGIN lev := obj.mnolev;
    IF obj.mode IN {Var, VarPar, Fld} THEN
      IF lev # level THEN obj.leaf := FALSE; IF lev > 0 THEN OPB.StaticLink(level - lev) END END
    ELSIF obj.mode IN {LProc, XProc} THEN
      IF lev > 0 THEN OPB.StaticLink(level - lev) END
    END
  END Level;

  (* SYSTEM.VAL(typ, x) as OPB.Val makes it of a node not folded: a designator gets the type, else Nmop(val) *)
  PROCEDURE Val(x: OPT.Node; typ: OPT.Struct): OPT.Node;
    VAR t: OPT.Node; f: SHORTINT;
  BEGIN f := x.typ.form;
    IF (x.class >= Nconst) OR ((f = Real) OR (f = LReal)) # ((typ.form = Real) OR (typ.form = LReal))
    OR (typ.sysflag = 5 (* delegate *)) & (typ.form = ProcTyp) & (f # ProcTyp) THEN
      t := NewNode(Nmop, val, typ, x, NIL); RETURN t
    ELSE x.readonly := FALSE; x.typ := typ; RETURN x
    END
  END Val;

  PROCEDURE ^ Build(d: DNode): OPT.Node;

  PROCEDURE Formals(proc: OPT.Node): OPT.Object;  (* the formal parameters of what is called *)
  BEGIN
    IF proc.class = Nproc THEN RETURN proc.obj.link ELSE RETURN proc.typ.link END
  END Formals;

  PROCEDURE ResultType(proc: OPT.Node): OPT.Struct;
  BEGIN
    IF proc.class = Nproc THEN RETURN proc.obj.typ ELSE RETURN proc.typ.BaseTyp END
  END ResultType;

  PROCEDURE BuildCall(d: DNode): OPT.Node;  (* d: the last parameter node of a complete call, or the call *)
    VAR pars, p, proc, n: OPT.Node;
  BEGIN pars := NIL;
    WHILE d.subflg > 0 DO p := Build(d.right); p.link := pars; pars := p; d := d.left END;
    proc := Build(d.left);
    n := NewNode(Ncall, 0, ResultType(proc), proc, pars); n.obj := Formals(proc); n.conval := OPT.NewConst();
    RETURN n
  END BuildCall;

  PROCEDURE Build(d: DNode): OPT.Node;  (* a new OPT tree for a complete expression *)
    VAR x, y: OPT.Node; obj: OPT.Object; t: OPT.Struct;
  BEGIN
    CASE d.tag OF
    | TconstNil: x := NewNode(Nconst, 0, OPT.niltyp, NIL, NIL); x.conval := OPT.NewConst()
    | TconstFalse: x := OPB.NewBoolConst(FALSE)
    | TconstTrue: x := OPB.NewBoolConst(TRUE)
    | TconstChar..TconstString:
        CASE d.tag OF
        | TconstChar: t := OPT.chartyp | TconstSInt: t := OPT.sinttyp | TconstInt: t := OPT.inttyp
        | TconstLInt: t := OPT.linttyp | TconstSet: t := OPT.settyp | TconstReal: t := OPT.realtyp
        | TconstLReal: t := OPT.lrltyp | TconstString: t := OPT.stringtyp
        END;
        x := NewNode(Nconst, 0, t, NIL, NIL); x.conval := CopyConst(d.conval)
    | Uvar, Uvarpar, Uproc: obj := Current(d.obj); Level(obj); x := OPB.NewLeaf(obj)
    | Ufield: x := NewNode(Nfield, 0, d.obj.typ, Build(d.left), NIL); x.obj := d.obj
    | Tderef: y := Build(d.left); x := NewNode(Nderef, 0, y.typ.BaseTyp, y, NIL)
    | Tindex: y := Build(d.left); x := NewNode(Nindex, 0, y.typ.BaseTyp, y, Build(d.right))
    | Uguard: x := NewNode(Nguard, 0, d.typ, Build(d.left), NIL)
    | Ueguard: x := NewNode(Neguard, 0, d.typ, Build(d.left), NIL)
    | UmopIs: x := NewNode(Nmop, is, OPT.booltyp, Build(d.left), NIL); x.obj := d.typ.strobj
    | UmopConv: x := NewNode(Nmop, conv, d.typ, Build(d.left), NIL)
    | TmopNot..TmopOdd:
        y := Build(d.left);
        IF (d.tag = TmopNot) OR (d.tag = TmopOdd) THEN t := OPT.booltyp ELSE t := y.typ END;
        x := NewNode(Nmop, mopOf[d.tag], t, y, NIL)
    | TdopAnd..TdopGeq:
        y := Build(d.left);
        IF (d.tag = TdopAnd) OR (d.tag = TdopOr) OR (d.tag >= TdopIn) THEN t := OPT.booltyp
        ELSIF d.tag = TdopLen THEN t := OPT.linttyp
        ELSE t := y.typ
        END;
        x := NewNode(Ndop, dopOf[d.tag], t, y, Build(d.right))
    | Tupto: x := NewNode(Nupto, 0, OPT.settyp, Build(d.left), Build(d.right))
    | TsysAdr: x := NewNode(Nmop, adr, OPT.linttyp, Build(d.left), NIL)
    | TsysGet8: x := NewNode(Nmop, get8, OPT.sinttyp, Build(d.left), NIL)
    | TsysGet16: x := NewNode(Nmop, get16, OPT.inttyp, Build(d.left), NIL)
    | TsysGet32: x := NewNode(Nmop, get32, OPT.linttyp, Build(d.left), NIL)
    | TsysBit: x := NewNode(Ndop, bit, OPT.booltyp, Build(d.left), Build(d.right))
    | TsysLsh, TsysRot: y := Build(d.left);
        IF d.tag = TsysLsh THEN x := NewNode(Ndop, lsh, y.typ, y, Build(d.right)) ELSE x := NewNode(Ndop, rot, y.typ, y, Build(d.right)) END
    | UsysVal: x := Val(Build(d.left), d.typ)
    | Tcall: x := BuildCall(d)
    ELSE Err(517); x := OPB.NewBoolConst(FALSE)
    END;
    RETURN x
  END Build;

  (* ---------- the stream of the code ---------- *)

  PROCEDURE ^ Expr(): DNode;
  PROCEDURE ^ StatSeq(VAR first: OPT.Node);
  PROCEDURE ^ StatSeqFrom(VAR first: OPT.Node);
  PROCEDURE ^ Enter(d: DNode): OPT.Node;

  PROCEDURE Params(n: DNode; skip: SHORTINT): DNode;  (* the remaining parameters of a call *)
    VAR match, remain: SHORTINT; par: DNode;
  BEGIN match := n.subflg; remain := n.flag;
    WHILE remain > 0 DO par := Expr(); INC(match); DEC(remain); n := PNode(n, remain, match, par, n.global & par.global) END;
    RETURN n
  END Params;

  PROCEDURE Complete(n: DNode): DNode;  (* a node found in the dictionary, completed if partial *)
    VAR left, right: DNode;
  BEGIN
    IF n.flag > 0 THEN n := Params(n, 0)
    ELSIF n.flag = flgNoLeft THEN left := Expr(); n := NNode(n.tag, n.typ, n.obj, left, n.right, left.global & n.global)
    ELSIF n.flag = flgNoRight THEN right := Expr(); n := NNode(n.tag, n.typ, n.obj, n.left, right, n.global & right.global)
    END;
    RETURN n
  END Complete;

  PROCEDURE Ref(): DNode;  (* tok is a reference *)
    VAR n: DNode;
  BEGIN
    IF tok > TlastTag THEN
      IF tok >= above THEN Err(518); RETURN falseNode END; n := glob[tok]
    ELSE
      IF -tok > -below THEN Err(518); RETURN falseNode END; n := loc[-tok]
    END;
    IF n = NIL THEN Err(518); RETURN falseNode END;
    RETURN n
  END Ref;

  PROCEDURE CallNode(left: DNode): DNode;  (* a new call of left, then its parameters *)
    VAR n: DNode; proc: OPT.Node;
  BEGIN
    n := NNode(Tcall, NIL, NIL, left, NIL, left.global);
    proc := Build(left); n.flag := NofPar(Formals(proc));
    RETURN Params(n, 0)
  END CallNode;

  PROCEDURE Expr(): DNode;  (* as Expression of the encoder *)
    VAR tag: INTEGER; n, left, right: DNode; c: OPT.Const; r: REAL; s: LONGINT;
  BEGIN
    Next; tag := SHORT(tok);
    IF (tok > TlastTag) OR (tok < 0) THEN RETURN Complete(Ref()) END;
    CASE tag OF
    | TconstNil: n := nilNode
    | TconstFalse: n := falseNode
    | TconstTrue: n := trueNode
    | TconstChar..TconstLInt: c := OPT.NewConst(); Files.ReadNum(R, c.intval); n := ConstNode(tag, c)
    | TconstSet: c := OPT.NewConst(); Files.ReadNum(R, SYSTEM.VAL(LONGINT, c.setval)); n := ConstNode(tag, c)
    | TconstReal: c := OPT.NewConst(); Files.ReadReal(R, r); c.realval := r; c.intval := OPM.ConstNotAlloc; n := ConstNode(tag, c)
    | TconstLReal: c := OPT.NewConst(); Files.ReadLReal(R, c.realval); c.intval := OPM.ConstNotAlloc; n := ConstNode(tag, c)
    | TconstString: c := OPT.NewConst(); c.ext := OPT.NewExt(); ReadString(c.ext^);
        s := 0; WHILE c.ext[s] # 0X DO INC(s) END; c.intval := OPM.ConstNotAlloc; c.intval2 := s + 1;
        n := ConstNode(tag, c)
    | Tderef, TmopNot..TmopOdd, TsysAdr, TsysGet8..TsysGet32: left := Expr(); n := NNode(tag, NIL, NIL, left, NIL, left.global)
    | Tindex, TdopAnd..Tupto, TsysBit..TsysRot: left := Expr(); right := Expr(); n := NNode(tag, NIL, NIL, left, right, left.global & right.global)
    | Tcall: left := Expr(); n := CallNode(left)
    ELSE Err(519); n := falseNode
    END;
    RETURN n
  END Expr;

  PROCEDURE Link(VAR first, last: OPT.Node; x: OPT.Node);
  BEGIN
    IF x # NIL THEN
      IF first = NIL THEN first := x ELSE last.link := x END;
      last := x; WHILE last.link # NIL DO last := last.link END
    END
  END Link;

  PROCEDURE WithVar(cond: DNode; VAR orig: OPT.Object; VAR typ: OPT.Struct);  (* a WITH branch: its variable, retyped *)
    VAR obj, a: OPT.Object; t: DNode; al: Alias; outer: OPT.Object;
  BEGIN
    PushDict;
    obj := cond.left.obj; orig := obj; typ := obj.typ; obj.typ := cond.typ;
    IF obj.mode = Var THEN t := NNode(Uvar, NIL, obj, NIL, NIL, cond.left.global)
    ELSE t := NNode(Uvarpar, NIL, obj, NIL, NIL, cond.left.global)
    END;
    VarNodes(t, obj.typ, cond.left.global);
    IF obj.mnolev >= 0 THEN  (* the parser declares a new object for the branch *)
      outer := OPT.topScope; OPT.OpenScope(level, OPT.topScope.link);
      a := OPT.NewObj(); COPY(obj.name, a.name); InsertObj(a);
      a.mode := obj.mode; a.scope := obj; a.typ := cond.typ; a.conval := OPT.NewConst();
      NEW(al); al.orig := obj; al.obj := a; al.next := aliases; aliases := al;
      OPT.topScope := outer; outer.link.scope := outer  (* as the parser: OpenScope made the new scope that of the owner *)
    END
  END WithVar;

  PROCEDURE EndWithVar(orig: OPT.Object; typ: OPT.Struct);
  BEGIN
    orig.typ := typ; PopDict;
    IF (aliases # NIL) & (aliases.orig = orig) THEN aliases := aliases.next END
  END EndWithVar;

  PROCEDURE IfStat(tag: INTEGER): OPT.Node;  (* IF or WITH, as IfStat of the encoder *)
    VAR first, last, if, seq, x: OPT.Node; cond: DNode; with: BOOLEAN; orig: OPT.Object; typ: OPT.Struct;
  BEGIN first := NIL; last := NIL; with := FALSE;
    cond := Expr();
    IF (tag = Twith) & (cond.tag = UmopIs) THEN with := TRUE; WithVar(cond, orig, typ) END;
    if := Stat(Nif, 0, Build(cond), NIL); StatSeq(seq); if.right := seq; Link(first, last, if);
    WHILE tok = Telsif DO
      cond := Expr();
      IF with THEN EndWithVar(orig, typ); with := FALSE END;
      IF (tag = Twith) & (cond.tag = UmopIs) THEN with := TRUE; WithVar(cond, orig, typ) END;
      if := Stat(Nif, 0, Build(cond), NIL); StatSeq(seq); if.right := seq; Link(first, last, if)
    END;
    IF tag = Twith THEN x := Stat(Nwith, 0, first, NIL) ELSE x := Stat(Nifelse, 0, first, NIL) END;
    IF tok = Twend THEN
      IF with THEN EndWithVar(orig, typ) END
    ELSIF tok = Telse THEN
      IF with THEN EndWithVar(orig, typ) END;
      StatSeq(seq); x.right := seq; IF tag = Twith THEN x.subcl := 1 END;
      IF tok # Tend THEN Err(520) END
    ELSIF tok = Tend THEN
      IF with THEN EndWithVar(orig, typ) END
    ELSE Err(520)
    END;
    RETURN x
  END IfStat;

  PROCEDURE Label(VAR first, last: OPT.Node; lo, hi: LONGINT; typ: OPT.Struct);
    VAR n: OPT.Node;
  BEGIN n := NewNode(Nconst, 0, typ, NIL, NIL); n.conval := OPT.NewConst(); n.conval.intval := lo; n.conval.intval2 := hi;
    Link(first, last, n)
  END Label;

  PROCEDURE CaseStat(): OPT.Node;  (* as CaseStat of the encoder: ELSE first (or Tcastrap), then the cases *)
    VAR min, max, lo, hi: LONGINT; sel, x, els, cases, lastcase, labs, lastlab, seq, do: OPT.Node; hasElse: BOOLEAN;
  BEGIN
    Files.ReadNum(R, min); Files.ReadNum(R, max); sel := Build(Expr());
    StatSeq(els);  (* the ELSE part, ended by the first label (or Tend) *)
    hasElse := TRUE;
    IF tok = Tcastrap THEN hasElse := FALSE; StatSeq(seq); IF seq # NIL THEN Err(520) END END;
    cases := NIL; lastcase := NIL;
    WHILE (tok = Tcaslbl1) OR (tok = Tcasrng1) DO
      labs := NIL; lastlab := NIL;
      Files.ReadNum(R, lo); IF tok = Tcasrng1 THEN Files.ReadNum(R, hi) ELSE hi := lo END;
      Label(labs, lastlab, lo, hi, sel.typ);
      Next;
      WHILE (tok = Tcaslbl2) OR (tok = Tcasrng2) DO
        Files.ReadNum(R, lo); IF tok = Tcasrng2 THEN Files.ReadNum(R, hi) ELSE hi := lo END;
        Label(labs, lastlab, lo, hi, sel.typ); Next
      END;
      StatSeqFrom(seq);  (* tok: the first number of the statements *)
      do := Stat(Ncasedo, 0, labs, seq); Link(cases, lastcase, do)
    END;
    IF tok # Tend THEN Err(520) END;
    x := Stat(Ncaselse, 0, cases, els);
    x.conval.intval := min; x.conval.intval2 := max;
    IF hasElse THEN x.conval.setval := {1} ELSE x.conval.setval := {} END;
    RETURN Stat(Ncase, 0, sel, x)
  END CaseStat;

  PROCEDURE SysStat(tag: INTEGER; left, right: OPT.Node): OPT.Node;  (* SYSTEM.GET, PUT, NEW *)
  BEGIN
    CASE tag OF
    | TsysGet: RETURN Stat(Nassign, getfn, left, right)
    | TsysPut: RETURN Stat(Nassign, putfn, left, right)
    | TsysNew: RETURN Stat(Nassign, sysnewfn, left, right)
    END
  END SysStat;

  PROCEDURE Statement(): OPT.Node;  (* tok: the first number of a statement *)
    VAR tag: INTEGER; n, left, right, cnt: DNode; x, seq, y, z: OPT.Node; trapno: LONGINT; dims, last: OPT.Node; t: OPT.Struct;
  BEGIN
    IF (tok > TlastTag) OR (tok < 0) THEN
      n := Ref();
      IF n.flag = flgEnter THEN RETURN Enter(n) END;
      n := Complete(n);
      CASE n.tag OF
      | Tcall: RETURN BuildCall(n)
      | TasgnAssign: RETURN Stat(Nassign, assign, Build(n.left), Build(n.right))
      | TasgnIncfn: RETURN Stat(Nassign, incfn, Build(n.left), Build(n.right))
      | TasgnDecfn: RETURN Stat(Nassign, decfn, Build(n.left), Build(n.right))
      | TasgnInclfn: RETURN Stat(Nassign, inclfn, Build(n.left), Build(n.right))
      | TasgnExclfn: RETURN Stat(Nassign, exclfn, Build(n.left), Build(n.right))
      | TasgnCopyfn: RETURN Stat(Nassign, copyfn, Build(n.left), Build(n.right))
      | TsysGet..TsysNew: RETURN SysStat(n.tag, Build(n.left), Build(n.right))
      | Ureturn:
          IF n.left = NIL THEN x := Stat(Nreturn, 0, NIL, NIL) ELSE x := Stat(Nreturn, 0, Build(n.left), NIL) END;
          x.obj := n.obj; RETURN x
      ELSE Err(521); RETURN NIL
      END
    END;
    tag := SHORT(tok);
    CASE tag OF
    | Tcall: left := Expr(); RETURN BuildCall(CallNode(left))
    | TasgnNewfn:
        left := Expr(); n := NNode(TasgnNewfn, NIL, NIL, left, NIL, left.global);
        x := Build(left); dims := NIL; last := NIL; t := x.typ.BaseTyp;
        WHILE (t # NIL) & (t.comp IN {DynArr, OpenArr}) DO Link(dims, last, Build(Expr())); t := t.BaseTyp END;
        RETURN Stat(Nassign, newfn, x, dims)
    | TasgnAssign..TasgnCopyfn:
        left := Expr(); right := Expr(); n := NNode(tag, NIL, NIL, left, right, left.global & right.global);
        CASE tag OF
        | TasgnAssign: RETURN Stat(Nassign, assign, Build(left), Build(right))
        | TasgnIncfn: RETURN Stat(Nassign, incfn, Build(left), Build(right))
        | TasgnDecfn: RETURN Stat(Nassign, decfn, Build(left), Build(right))
        | TasgnInclfn: RETURN Stat(Nassign, inclfn, Build(left), Build(right))
        | TasgnExclfn: RETURN Stat(Nassign, exclfn, Build(left), Build(right))
        | TasgnCopyfn: RETURN Stat(Nassign, copyfn, Build(left), Build(right))
        END
    | TsysGet..TsysNew:
        left := Expr(); right := Expr(); n := NNode(tag, NIL, NIL, left, right, left.global & right.global);
        RETURN SysStat(tag, Build(left), Build(right))
    | TsysMove:  (* MOVE(src, dst, n): Nassign(movefn, dst, src) with n after src *)
        left := Expr(); right := Expr(); cnt := Expr(); n := NNode(tag, NIL, NIL, left, right, left.global & right.global);
        y := Build(right); y.link := Build(cnt); RETURN Stat(Nassign, movefn, Build(left), y)
    | Tif, Twith: RETURN IfStat(tag)
    | Tcase: RETURN CaseStat()
    | Twhile: x := Build(Expr()); StatSeq(seq); IF tok # Tend THEN Err(520) END; RETURN Stat(Nwhile, 0, x, seq)
    | Trepeat: StatSeq(seq); IF tok # Tend THEN Err(520) END; RETURN Stat(Nrepeat, 0, seq, Build(Expr()))
    | Tloop: StatSeq(seq); IF tok # Tend THEN Err(520) END; RETURN Stat(Nloop, 0, seq, NIL)
    | Texit: RETURN Stat(Nexit, 0, NIL, NIL)
    | Tassert:
        Files.ReadNum(R, trapno); x := Build(Expr());
        y := OPB.NewIntConst(trapno); y := Stat(Ntrap, 0, y, y);
        y := Stat(Nif, 0, x, y); x := Stat(Nifelse, assertfn, y, NIL); RETURN x
    | Ttrap: Files.ReadNum(R, trapno); y := OPB.NewIntConst(trapno); RETURN Stat(Ntrap, 0, y, y)
    ELSE Err(521); RETURN NIL
    END
  END Statement;

  PROCEDURE StatSeqFrom(VAR first: OPT.Node);  (* statements from tok up to one of the ends 0..Tbegin; tok: that end *)
    VAR last, x: OPT.Node;
  BEGIN first := NIL; last := NIL;
    WHILE ((tok > Tbegin) OR (tok < 0)) & OPM.noerr DO
      x := Statement(); Link(first, last, x); Next
    END
  END StatSeqFrom;

  PROCEDURE StatSeq(VAR first: OPT.Node);
  BEGIN Next; StatSeqFrom(first)
  END StatSeq;

  PROCEDURE Enter(d: DNode): OPT.Node;  (* a procedure: its scope, nested procedures and body *)
    VAR proc, outer, v: OPT.Object; dum: DNode; procdec, body, x: OPT.Node;
  BEGIN
    proc := d.obj; outer := OPT.topScope; v := vars;
    PushDict;
    IF proc.typ = OPT.notyp THEN dum := NNode(Ureturn, NIL, proc, NIL, NIL, Local)
    ELSE UNodeO(Ureturn, flgNoLeft, NIL, proc, Local)
    END;
    INC(level); OPT.topScope := proc.scope; vars := NIL;
    objects := proc.link; ReadScope(internal);
    GenNodes(objects, FALSE, Local);
    StatSeq(procdec); IF tok # Tbegin THEN Err(522) END;
    StatSeq(body); IF tok # Tend THEN Err(522) END;
    x := Stat(Nenter, 0, procdec, body); x.obj := proc;
    DEC(level); OPT.topScope := outer; vars := v;
    PopDict;
    RETURN x
  END Enter;

  (* ---------- the module ---------- *)

  PROCEDURE HiddenStructs;  (* as CreateHiddenStructs of the parser *)
    VAR obj, fld1, fld2: OPT.Object;

    PROCEDURE Struct(name: ARRAY OF CHAR; VAR obj: OPT.Object);
      VAR typ: OPT.Struct;
    BEGIN typ := OPT.NewStr(Comp, Record); typ.BaseTyp := NIL; typ.sysflag := systemtype;
      OPT.Insert(name, obj); obj.mode := Typ; obj.typ := typ; obj.vis := internal; typ.strobj := obj;
      INCL(obj.flag, OPT.used); obj.conval := OPT.NewConst()
    END Struct;

  BEGIN
    Struct(OPT.Delegate, obj); OPT.OpenScope(0, obj);
    OPT.Insert("proc", fld1); fld1.mode := Fld; fld1.typ := OPT.linttyp; obj.typ.link := fld1; INCL(fld1.flag, OPT.used);
    OPT.Insert("self", fld2); fld2.mode := Fld; fld2.typ := OPT.ptrtyp; fld2.link := fld1; INCL(fld2.flag, OPT.used);
    OPT.CloseScope;
    Struct(OPT.HdPtrStruct, obj); OPT.OpenScope(0, obj);
    OPT.Insert("ptr", fld1); fld1.mode := Fld; fld1.typ := OPT.ptrtyp; obj.typ.link := fld1; INCL(fld1.flag, OPT.used);
    OPT.CloseScope
  END HiddenStructs;

  (** Read the slim binary F of the module name: its objects into OPT (OPT.Init is done here), its tree into
     prog, as OPP.Module would have; OPM.Init must have been called. *)
  PROCEDURE Module*(F: Files.File; VAR name: OPS.Name; VAR prog: OPT.Node);
    VAR ch: CHAR; size, expSect, nloc, nglob: LONGINT; mod: OPT.Object; i: INTEGER; procdec, body, init: OPT.Node;
  BEGIN
    prog := NIL; COPY(name, modName);
    Files.Set(R, F, 0); Files.Read(R, ch);
    IF ch # OFtag THEN Err(523); RETURN END;
    Files.Read(R, ch); IF ch # OFportable THEN Err(523); RETURN END;
    Files.ReadNum(R, size);
    OPT.Init(modName);
    mod := OPT.NewObj(); mod.scope := OPT.topScope; OPT.topScope.link := mod;
    OPT.topScope.conval := OPT.NewConst(); mod.mode := Mod; mod.conval := OPT.NewConst(); mod.typ := OPT.notyp;
    INCL(mod.conval.setval, protectedObj); COPY(modName, mod.name);
    nofemods := 0; nofstruc := 0; NEW(structs, 4096); objects := NIL; level := 0; vars := NIL; aliases := NIL;
    TDinit := NIL; lastTDinit := NIL; dsp := 0;
    Imports;  (* the imports of the interface *)
    IF ~OPM.noerr THEN RETURN END;
    HiddenStructs;
    ReadScope(external);  (* the interface *)
    Files.ReadNum(R, expSect); Files.ReadNum(R, nloc); Files.ReadNum(R, nglob);
    NEW(glob, nglob + 1); NEW(loc, nloc + 2);
    Imports;  (* the other imports *)
    ReadScope(internal);  (* the rest of the module scope *)
    IF ~OPM.noerr THEN RETURN END;
    above := TlastTag + 1; below := -1;
    UNodeO(UmopConv, flgNoLeft, OPT.chartyp, NIL, Global);
    UNodeO(UmopConv, flgNoLeft, OPT.sinttyp, NIL, Global);
    UNodeO(UmopConv, flgNoLeft, OPT.inttyp, NIL, Global);
    UNodeO(UmopConv, flgNoLeft, OPT.linttyp, NIL, Global);
    UNodeO(UmopConv, flgNoLeft, OPT.realtyp, NIL, Global);
    UNodeO(UmopConv, flgNoLeft, OPT.lrltyp, NIL, Global);
    UNodeO(UmopConv, flgNoLeft, OPT.settyp, NIL, Global);
    UNodeO(UsysVal, flgNoLeft, OPT.booltyp, NIL, Global); UNodeO(UsysVal, flgNoLeft, OPT.chartyp, NIL, Global);
    UNodeO(UsysVal, flgNoLeft, OPT.sinttyp, NIL, Global); UNodeO(UsysVal, flgNoLeft, OPT.inttyp, NIL, Global);
    UNodeO(UsysVal, flgNoLeft, OPT.linttyp, NIL, Global); UNodeO(UsysVal, flgNoLeft, OPT.realtyp, NIL, Global);
    UNodeO(UsysVal, flgNoLeft, OPT.lrltyp, NIL, Global); UNodeO(UsysVal, flgNoLeft, OPT.settyp, NIL, Global);
    UNodeO(UsysVal, flgNoLeft, OPT.bytetyp, NIL, Global); UNodeO(UsysVal, flgNoLeft, OPT.ptrtyp, NIL, Global);
    GenNodes(objects, FALSE, Global);
    UseSection;
    IF ~OPM.noerr THEN RETURN END;
    StatSeq(procdec); IF tok # Tbegin THEN Err(522) END;
    StatSeq(body); IF tok # Tend THEN Err(522) END;
    IF TDinit # NIL THEN lastTDinit.link := body; body := TDinit END;
    prog := Stat(Nenter, 0, procdec, body)
  END Module;

  PROCEDURE Init;
  BEGIN
    predef[SFtypBool] := OPT.booltyp; predef[SFtypChar] := OPT.chartyp; predef[SFtypSInt] := OPT.sinttyp;
    predef[SFtypInt] := OPT.inttyp; predef[SFtypLInt] := OPT.linttyp; predef[SFtypHInt] := OPT.hinttyp;
    predef[SFtypReal] := OPT.realtyp; predef[SFtypLReal] := OPT.lrltyp; predef[SFtypSet] := OPT.settyp;
    predef[SFtypString] := OPT.stringtyp; predef[SFtypNoTyp] := OPT.notyp; predef[SFtypNilTyp] := OPT.niltyp;
    predef[SFtypByte] := OPT.bytetyp; predef[SFtypptr] := OPT.ptrtyp;
    mopOf[TmopNot] := not; mopOf[TmopMinus] := minus; mopOf[TmopAbs] := abs; mopOf[TmopCap] := cap; mopOf[TmopOdd] := odd;
    dopOf[TdopAnd] := and; dopOf[TdopOr] := or; dopOf[TdopTimes] := times; dopOf[TdopSlash] := slash;
    dopOf[TdopDiv] := div; dopOf[TdopMod] := mod; dopOf[TdopPlus] := plus; dopOf[TdopMinus] := minus;
    dopOf[TdopMsk] := msk; dopOf[TdopAsh] := ash; dopOf[TdopLen] := len; dopOf[TdopIn] := in;
    dopOf[TdopEql] := eql; dopOf[TdopNeq] := neq; dopOf[TdopLss] := lss; dopOf[TdopLeq] := leq;
    dopOf[TdopGtr] := gtr; dopOf[TdopGeq] := geq;
    NEW(nilNode); nilNode.tag := TconstNil; nilNode.global := Global;
    NEW(falseNode); falseNode.tag := TconstFalse; falseNode.global := Global;
    NEW(trueNode); trueNode.tag := TconstTrue; trueNode.global := Global
  END Init;

BEGIN Init
END OPOPD.
