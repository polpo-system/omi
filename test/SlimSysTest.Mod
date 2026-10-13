MODULE SlimSysTest;  (** SlimSysTest.Run: SYSTEM through a slim binary; the same output as compiled natively *)

IMPORT SYSTEM, out;

TYPE
  Rec = RECORD a, b: LONGINT; c: CHAR END;
  P = POINTER TO Rec;

VAR
  checks, fails: INTEGER; buf: ARRAY 16 OF CHAR; r: Rec; p: P; adr, i: LONGINT; s: SET; x: REAL; c: CHAR;
  n8: SHORTINT; n16: INTEGER;

PROCEDURE Check(what: ARRAY OF CHAR; ok: BOOLEAN);
BEGIN INC(checks);
  IF ~ok THEN INC(fails); out.String("SlimSysTest: failed: "); out.String(what); out.Ln END
END Check;

PROCEDURE Run*;
VAR a, b: ARRAY 8 OF CHAR; k: LONGINT; q: P;
BEGIN
  checks := 0; fails := 0;
  r.a := 12345; adr := SYSTEM.ADR(r.a);
  SYSTEM.GET(adr, i); Check("ADR, GET", i = 12345);
  i := 678; SYSTEM.PUT(adr, i); Check("PUT", r.a = 678);
  SYSTEM.PUT(SYSTEM.ADR(r.c), "z"); Check("PUT of a character", r.c = "z");
  SYSTEM.PUT8(SYSTEM.ADR(buf[0]), 65); SYSTEM.PUT16(SYSTEM.ADR(buf[2]), 4242H); SYSTEM.PUT32(SYSTEM.ADR(buf[4]), 61626364H);
  Check("PUT8", buf[0] = "A"); Check("GET8", SYSTEM.GET8(SYSTEM.ADR(buf[0])) = 65);
  Check("GET16", SYSTEM.GET16(SYSTEM.ADR(buf[2])) = 4242H); Check("GET32", SYSTEM.GET32(SYSTEM.ADR(buf[4])) = 61626364H);
  i := 5; s := SYSTEM.VAL(SET, i); Check("VAL of a variable", s = {0, 2});
  i := SYSTEM.VAL(LONGINT, {1, 3}); Check("VAL of a constant", i = 10);
  x := 1.0; Check("VAL of a REAL", SYSTEM.VAL(LONGINT, x) = 3F800000H);
  i := 3; Check("VAL of an expression", SYSTEM.VAL(SET, i + 1) = {2});
  NEW(p); p.b := 99; adr := SYSTEM.VAL(LONGINT, p); q := SYSTEM.VAL(P, adr); Check("VAL of pointers", q.b = 99);
  Check("LSH", (SYSTEM.LSH(1, 4) = 16) & (SYSTEM.LSH(256, -4) = 16));
  Check("ROT", SYSTEM.ROT(LONG(LONG(1)), -1) = MIN(LONGINT));
  i := 6; Check("BIT", SYSTEM.BIT(SYSTEM.ADR(i), 1) & ~SYSTEM.BIT(SYSTEM.ADR(i), 0));
  a := "slim"; SYSTEM.MOVE(SYSTEM.ADR(a), SYSTEM.ADR(b), 5); Check("MOVE", b = "slim");
  SYSTEM.NEW(q, 64); k := SYSTEM.VAL(LONGINT, q); Check("SYSTEM.NEW", k # 0);
  c := "A"; n8 := SYSTEM.VAL(SHORTINT, c); Check("VAL of CHAR", n8 = 65);
  n16 := SHORT(SYSTEM.VAL(LONGINT, s)); Check("VAL in SHORT", n16 = 5);
  out.String("SlimSysTest: "); out.Int(checks, 0); out.String(" checks, "); out.Int(fails, 0); out.String(" failed"); out.Ln
END Run;

END SlimSysTest.
