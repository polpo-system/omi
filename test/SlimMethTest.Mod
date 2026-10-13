MODULE SlimMethTest;  (** SlimMethTest.Run: type-bound procedures through a slim binary (compile with /2) *)

IMPORT out;

TYPE
  Shape* = POINTER TO ShapeDesc;
  ShapeDesc* = RECORD n*: LONGINT END;
  Square = POINTER TO SquareDesc;
  SquareDesc = RECORD (ShapeDesc) side: LONGINT END;
  Counter = RECORD count: LONGINT END;

VAR checks, fails: INTEGER;

PROCEDURE Check(what: ARRAY OF CHAR; ok: BOOLEAN);
BEGIN INC(checks);
  IF ~ok THEN INC(fails); out.String("SlimMethTest: failed: "); out.String(what); out.Ln END
END Check;

PROCEDURE (s: Shape) Area*(): LONGINT;
BEGIN RETURN 0
END Area;

PROCEDURE (s: Shape) Name*(VAR name: ARRAY OF CHAR);
BEGIN COPY("shape", name)
END Name;

PROCEDURE (s: Square) Area*(): LONGINT;
BEGIN RETURN s.side * s.side
END Area;

PROCEDURE (s: Square) Name*(VAR name: ARRAY OF CHAR);
BEGIN s.Name^(name); name[5] := "!"; name[6] := 0X  (* the super call *)
END Name;

PROCEDURE (VAR c: Counter) Inc(k: LONGINT);
BEGIN INC(c.count, k)
END Inc;

PROCEDURE Run*;
VAR sh: Shape; sq: Square; name: ARRAY 16 OF CHAR; c: Counter;
BEGIN
  checks := 0; fails := 0;
  NEW(sh); NEW(sq); sq.side := 7;
  Check("method", sh.Area() = 0);
  Check("overridden method", sq.Area() = 49);
  sh := sq; Check("dynamic binding", sh.Area() = 49);
  sh.Name(name); Check("super call", name = "shape!");
  c.count := 0; c.Inc(3); c.Inc(4); Check("VAR receiver", c.count = 7);
  out.String("SlimMethTest: "); out.Int(checks, 0); out.String(" checks, "); out.Int(fails, 0); out.String(" failed"); out.Ln
END Run;

END SlimMethTest.
