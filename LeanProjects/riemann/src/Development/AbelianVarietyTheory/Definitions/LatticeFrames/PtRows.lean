import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TruePack
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.MiS

namespace GlobalTheory.Fam

@[reducible] def packB {D : D7} {O : Obj D} {c : ℝ} (b : GlobalTheory.Fc.Bundle D O c) : RealPack O.ex :=
  letI := b.B.alg
  { R := b.R, S := b.S, P := b.P, Dcf := b.C.c.face, Spf := b.C.Sp, Zscf := GlobalTheory.Fc.zsc b.P b.DH.1.1 b.DH.1.2 c,
    Ks := b.B.T.Q.c.F, Q := b.B.Q }

structure PtRows {D : D7} {O : Obj D} {c : ℝ} (b : GlobalTheory.Fc.Bundle D O c) : Prop where
  join : Nonempty (Formalism.L2.SG.JoinSI.JoinSI b.R b.S b.B.Q)
  dc : DcPtG b.P
  frames : Formalism.IndefR.RealT.FramesEx b.B.Q
  see : Formalism.IndefR.SeeEx b.B.Q
  ex : b.B.Q.Rl.toRealDat.ExAt
  prim : Formalism.IndefR.Links.PrimRows3 b.B.Q.Rl b.B.Q.F ∧ b.P.A3.fam3.TypesSep3
  fin : Formalism.L2.SG.PackageTie2.FinX b.S.Y
  gapS : GlobalTheory.Count.GapGe b.S.X.B (100 * (D.R.r : ℝ) ^ 4)
  gap : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D
  rS : 1 ≤ D.R.rS

end GlobalTheory.Fam

end
