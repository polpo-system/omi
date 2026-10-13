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

MODULE OMI; (* tk 25.10.95 *)

  IMPORT Modules, PLL:=OPLL, PLV:=OPLV, Interchange, Texts, Oberon;

  VAR
    W: Texts.Writer;

  PROCEDURE VerboseMod(M: Modules.Module);
  BEGIN
    Texts.WriteString(W, "Decoder.MemDecode "); Texts.WriteString(W, M.name); Texts.Write(W, " ");
    Texts.WriteHex(W, M.code); Texts.WriteString(W, "H ");
    Texts.WriteInt(W, 2*LONG(PLL.pc), 1);
    Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf)
  END VerboseMod;

  PROCEDURE Start*;
  BEGIN Interchange.Start; Texts.WriteString(W, "OMI enabled"); Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf)
  END Start;

  PROCEDURE Stop*;
  BEGIN Interchange.Stop; Texts.WriteString(W, "OMI disabled"); Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf)
  END Stop;

  PROCEDURE Verbose*;
  BEGIN Interchange.Verbose; Texts.WriteString(W, "OMI verbose enabled"); Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf)
  END Verbose;

  PROCEDURE ChecksOn*;
  BEGIN Interchange.ChecksOn; Texts.WriteString(W, "OMI run_time checks enabled"); Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf)
  END ChecksOn;

  PROCEDURE ChecksOff*;
  BEGIN Interchange.ChecksOff; Texts.WriteString(W, "OMI run_time checks disabled"); Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf)
  END ChecksOff;

  PROCEDURE AssertsOn*;
  BEGIN PLV.EnableAssert; Texts.WriteString(W, "OMI asserts enabled"); Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf)
  END AssertsOn;

  PROCEDURE AssertsOff*;
  BEGIN PLV.DisableAssert; Texts.WriteString(W, "OMI asserts disabled"); Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf)
  END AssertsOff;

  PROCEDURE RefsOn*;
  BEGIN PLV.EnableRefs; Texts.WriteString(W, "OMI reference info enabled"); Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf)
  END RefsOn;

  PROCEDURE RefsOff*;
  BEGIN PLV.DisableRefs; Texts.WriteString(W, "OMI reference info disabled"); Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf)
  END RefsOff;


BEGIN
  Interchange.verboseHook:=VerboseMod;
  Texts.OpenWriter(W); Texts.WriteString(W, "Oberon Module Interchange (OMI) / mf, tk 9.7.96"); Texts.WriteLn(W);
  Texts.Append(Oberon.Log, W.buf)
END OMI.