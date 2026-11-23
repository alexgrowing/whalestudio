import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LPrjSurjAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowSideDetermined
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc
namespace GlobalTheory.Fc.R1.ZLAt
theorem lPrj_surj_at_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (k : Fin D.R.m) :
    Function.Surjective (Formalism.L2.DIV.lPrj D b.P.A3.A b.P.P0 b.P.ψ0 (b.P.A3.fam3.toSub2 b.P.Zs) k b.P.A3.A.μ0).mulVec :=
  GlobalTheory.Mem.LiftProjOnto.lPrj_surjective D b.P.Gp b.P.Pl0 b.P.T b.P.A3.A b.P.P0 b.P.ψ0 (b.P.A3.fam3.toSub2 b.P.Zs) k
    b.P.A3.A.μ0 _ _ _ b.C.ok1.ok2 (b.P.tied.div.mt.forms k b.P.A3.A.μ0)
theorem zL_of_hPA : ∀ (Q : V4.Slot) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), _root_.GlobalTheory.Fc.R1.SlotPrimitivityCondition Q Lk → _root_.GlobalTheory.Fc.R1.SlotZeroLocusCondition Q Lk := by
  intro Q Lk _
  refine Row.of_sel fun 𝒜 σ _ => ?_
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ hc => ⟨0, fun x hx _ _ i k => ?_⟩⟩⟩
  exact _root_.GlobalTheory.Fc.R1.ZLAt.lPrj_surj_at_alt (σ Fm (GlobalTheory.Cp.d3_a hc) x hx i) k
end GlobalTheory.Fc.R1.ZLAt
end
