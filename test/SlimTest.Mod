MODULE SlimTest;  (** SlimTest.Run: language constructs through a slim binary; the same output as compiled natively *)

IMPORT out;

CONST
  N = 10; Pi = 3.1415926535897932D0; Greeting = "slim"; Mask = {0, 3, 5..7};

TYPE
  Shape = POINTER TO ShapeDesc;
  ShapeDesc = RECORD name: ARRAY 16 OF CHAR; next: Shape END;
  Circle = POINTER TO CircleDesc;
  CircleDesc = RECORD (ShapeDesc) r: REAL END;
  Rect = POINTER TO RectDesc;
  RectDesc = RECORD (ShapeDesc) w, h: LONGINT END;
  Vector = ARRAY N OF LONGINT;
  Matrix = ARRAY 3, 4 OF INTEGER;
  Func = PROCEDURE (x: LONGINT): LONGINT;
  Buffer = POINTER TO ARRAY OF CHAR;

VAR
  shapes: Shape; v: Vector; m: Matrix; f: Func; checks, fails: INTEGER;
  ch: CHAR; s: SET; b: BOOLEAN; buf: Buffer; total: LONGINT; lr: LONGREAL;

PROCEDURE Check(what: ARRAY OF CHAR; ok: BOOLEAN);
BEGIN INC(checks);
  IF ~ok THEN INC(fails); out.String("SlimTest: failed: "); out.String(what); out.Ln END
END Check;

PROCEDURE Square(x: LONGINT): LONGINT;
BEGIN RETURN x * x
END Square;

PROCEDURE Cube(x: LONGINT): LONGINT;
BEGIN RETURN x * x * x
END Cube;

PROCEDURE Fact(n: LONGINT): LONGINT;
BEGIN IF n <= 1 THEN RETURN 1 ELSE RETURN n * Fact(n - 1) END
END Fact;

PROCEDURE Swap(VAR a, b: LONGINT);
VAR t: LONGINT;
BEGIN t := a; a := b; b := t
END Swap;

PROCEDURE Sum(VAR a: ARRAY OF LONGINT): LONGINT;  (* open array *)
VAR i, s: LONGINT;
BEGIN s := 0; i := 0; WHILE i < LEN(a) DO s := s + a[i]; INC(i) END; RETURN s
END Sum;

PROCEDURE Length(s: ARRAY OF CHAR): LONGINT;
VAR i: LONGINT;
BEGIN i := 0; WHILE (i < LEN(s)) & (s[i] # 0X) DO INC(i) END; RETURN i
END Length;

PROCEDURE Outer(x: LONGINT): LONGINT;  (* nested procedure, using a variable of the outer one *)
VAR k: LONGINT;
  PROCEDURE Inner(y: LONGINT): LONGINT;
  BEGIN RETURN y + k
  END Inner;
BEGIN k := 100; RETURN Inner(x) + Inner(2 * x)
END Outer;

PROCEDURE Kind(sh: Shape): INTEGER;  (* type tests *)
BEGIN
  IF sh IS Circle THEN RETURN 1 ELSIF sh IS Rect THEN RETURN 2 ELSE RETURN 0 END
END Kind;

PROCEDURE Area(sh: Shape): LONGREAL;  (* WITH *)
VAR a: LONGREAL;
BEGIN a := 0;
  WITH sh: Circle DO a := Pi * sh.r * sh.r
  | sh: Rect DO a := sh.w * sh.h
  ELSE a := -1
  END;
  RETURN a
END Area;

PROCEDURE Grade(n: INTEGER): CHAR;  (* CASE *)
VAR c: CHAR;
BEGIN
  CASE n OF
  | 0..4: c := "F"
  | 5, 6: c := "C"
  | 7: c := "B"
  | 8..10: c := "A"
  ELSE c := "?"
  END;
  RETURN c
END Grade;

PROCEDURE Add(sh: Shape; name: ARRAY OF CHAR);
BEGIN COPY(name, sh.name); sh.next := shapes; shapes := sh
END Add;

PROCEDURE Run*;
VAR i, j, a, c: LONGINT; circle: Circle; rect: Rect; sh: Shape; n: INTEGER; str: ARRAY 32 OF CHAR;
BEGIN
  checks := 0; fails := 0;
  i := 0; WHILE i < N DO v[i] := i * i; INC(i) END;
  Check("open array", Sum(v) = 285);
  Check("recursion", Fact(10) = 3628800);
  a := 3; c := 7; Swap(a, c); Check("VAR parameters", (a = 7) & (c = 3));
  f := Square; Check("procedure variable", f(9) = 81); f := Cube; Check("procedure variable 2", f(3) = 27);
  Check("nested procedure", Outer(5) = 215);
  i := 0; j := 0; REPEAT INC(j, i); INC(i) UNTIL i > 10; Check("REPEAT", j = 55);
  i := 0; LOOP INC(i); IF i = 7 THEN EXIT END END; Check("LOOP, EXIT", i = 7);
  i := 0; WHILE i < 3 DO j := 0; WHILE j < 4 DO m[i, j] := SHORT(i * 10 + j); INC(j) END; INC(i) END;
  Check("two dimensions", (m[2, 3] = 23) & (m[1, 0] = 10));
  NEW(circle); circle.r := 2.0; Add(circle, "circle");
  NEW(rect); rect.w := 3; rect.h := 4; Add(rect, "rect");
  Check("IS", (Kind(circle) = 1) & (Kind(rect) = 2));
  Check("WITH", (ABS(Area(circle) - 4 * Pi) < 1.0D-6) & (Area(rect) = 12));
  sh := shapes; n := 0; WHILE sh # NIL DO INC(n); sh := sh.next END; Check("list", n = 2);
  Check("guard", shapes(Rect).w = 3);
  Check("CASE", (Grade(3) = "F") & (Grade(6) = "C") & (Grade(7) = "B") & (Grade(9) = "A") & (Grade(11) = "?"));
  s := Mask; INCL(s, 1); EXCL(s, 3);
  Check("sets", (s = {0, 1, 5, 6, 7}) & (6 IN s) & ~(3 IN s) & (s * {0..2} = {0, 1}));
  ch := "a"; ch := CAP(ch); Check("CAP, ORD, CHR", (ch = "A") & (ORD(ch) = 65) & (CHR(66) = "B"));
  str := Greeting; Check("strings", (Length(str) = 4) & (str = "slim") & (str < "slip"));
  NEW(buf, 8); COPY("abc", buf^); Check("NEW of an open array", (LEN(buf^) = 8) & (buf[1] = "b"));
  lr := 1.5; lr := lr * 4 + 0.25; Check("reals", (lr = 6.25) & (ENTIER(lr) = 6));
  Check("DIV, MOD", ((-7) DIV 2 = -4) & ((-7) MOD 2 = 1) & (-7 DIV 2 = -3) & (ASH(1, 10) = 1024) & (ODD(7)));
  i := 5; j := 1; b := (i > 3) OR (j < 0); Check("booleans", b & ~(b & FALSE));
  total := 0; i := 1; WHILE i <= 100 DO total := total + i; INC(i) END; Check("long loop", total = 5050);
  ASSERT(total = 5050);
  out.String("SlimTest: "); out.Int(checks, 0); out.String(" checks, "); out.Int(fails, 0); out.String(" failed"); out.Ln
END Run;

END SlimTest.
