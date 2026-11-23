import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseLevelRowOfNonzeroGoodRowsPartStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroRationalLiftMemBasePartStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelFramesHermitianNeZeroOffPlaceStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.RowsLift

theorem rows_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ p, R.EEp3 p ≠ ⊥ → ∀ i, R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ A3.A.v0 → R.PartAt F i p v := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hI hP hH hM hg p hp i
  have hA := GlobalTheory.T.exists_baseLevelRow_of_nonzero_goodRowsPart D G Pl0 I0 T A3 Ks R F cG hI hP hH hM hg p hp
  have hB : (R.toCx3 F).Wp i p ⊓ LinearMap.range ((R.toCx3 F).w0C false i) ≠ ⊥ := by
    intro h0
    apply hA
    rw [← Submodule.finrank_eq_zero, ← hH.prim.dimParts i p, h0, finrank_bot]
  refine ⟨?_, fun v hv => ?_⟩
  · intro h0
    apply hB
    rw [eq_bot_iff]
    intro w hw
    have : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := (R.HW i (sg0 D A3.A)).H) w ∈ R.Wp3 i p := hw.1
    rw [h0] at this
    exact (Submodule.mem_bot ℂ).2 this
  · obtain ⟨x, hx, hx0⟩ := GlobalTheory.T.exists_nonzero_rational_lift_mem_base_part D G Pl0 I0 T A3 Ks R F cG hI hP hH hM hg p hp i hB
    exact ⟨x, hx, GlobalTheory.T.base_level_frames_hermitian_ne_zero_off_place D G Pl0 I0 T A3 Ks R F cG hI hP hH hM hg i v hv x hx0⟩

end GlobalTheory.RowsLift
