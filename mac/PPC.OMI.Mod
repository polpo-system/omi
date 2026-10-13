(* ETH Oberon, Copyright 2000 ETH Zürich Institut für Computersysteme, ETH Zentrum, CH-8092 Zürich.
Refer to the general ETH Oberon System license contract available at: http://www.oberon.ethz.ch/ *)

MODULE OMI; (* tk 25.10.95 *)

  IMPORT Modules, PLL:=OPLL, PLV:=OPLV, Interchange, Texts, Oberon;

  VAR
    W: Texts.Writer;

  PROCEDURE VerboseMod(M: Modules.Module);
  BEGIN
    Texts.WriteString(W, "Decoder.DecodeMem "); Texts.WriteHex(W, M.block); Texts.WriteString(W, "H ");
    Texts.WriteInt(W, 4*PLL.pc, 1); Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf);
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

  PROCEDURE StackInitOn*;
  BEGIN Interchange.StackInitOn; Texts.WriteString(W, "OMI stack initialization enabled"); Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf)
  END StackInitOn;

  PROCEDURE StackInitOff*;
  BEGIN Interchange.StackInitOff; Texts.WriteString(W, "OMI stack initialization disabled"); Texts.WriteLn(W); Texts.Append(Oberon.Log, W.buf)
  END StackInitOff;

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