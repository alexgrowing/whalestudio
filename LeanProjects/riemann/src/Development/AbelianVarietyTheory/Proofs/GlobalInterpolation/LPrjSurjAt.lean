import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LPrjSurjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.R1.ZLAt

theorem lPrj_surj_at {D : D7} {O : Obj D} {c : ℝ} (b : Bundle D O c) (k : Fin D.R.m) :
    Function.Surjective (Formalism.L2.DIV.lPrj D b.P.A3.A b.P.P0 b.P.ψ0 (b.P.A3.fam3.toSub2 b.P.Zs) k b.P.A3.A.μ0).mulVec :=
  GlobalTheory.Mem.LiftProjOnto.lPrj_surjective D b.P.Gp b.P.Pl0 b.P.T b.P.A3.A b.P.P0 b.P.ψ0 (b.P.A3.fam3.toSub2 b.P.Zs) k
    b.P.A3.A.μ0 _ _ _ b.C.ok1.ok2 (b.P.tied.div.mt.forms k b.P.A3.A.μ0)

theorem row_zL : ∀ (Q : V4.Slot) (Lk : LkT Bundle), R1.PeriodAdmissibilityAtBundlePoints Q Lk → R1.LZeroConditionAtBundlePoints Q Lk := by
  intro Q Lk _
  refine Row.of_sel fun 𝒜 σ _ => ?_
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ hc => ⟨0, fun x hx _ _ i k => ?_⟩⟩⟩
  exact lPrj_surj_at (σ Fm (GlobalTheory.Cp.d3_a hc) x hx i) k

end GlobalTheory.Fc.R1.ZLAt
