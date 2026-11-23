import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemBand
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
import GroundTheory.AutomorphicForms.ReductionSiegel
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff

namespace GlobalTheory.HeightBound

theorem height_le_of_isCompact : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Q : Set (Lie E a)),
    IsCompact Q → Q ⊆ invSet E a →
    ∃ H : ℝ, ∀ y : GL (Fin a) (Cinf E), toL y.val ∈ Q → GlobalTheory.CuspRep.height y ≤ H := by
  intro E _ _ _ a Q hQ hsub
  let f : Lie E a → Lie E a := fun w => toL ((Matrix.of w)⁻¹)
  have hdetc : Continuous (fun x : Lie E a => (Matrix.of x).det) := by
    simp only [Matrix.det_apply', Matrix.of_apply]
    refine continuous_finset_sum _ fun σ _ => continuous_const.mul (continuous_finset_prod _ fun i _ => ?_)
    exact (continuous_apply i).comp (continuous_apply (σ i))
  have hadj : Continuous (fun x : Lie E a => (Matrix.of x).adjugate) :=
    Continuous.matrix_adjugate (continuous_id : Continuous fun x : Lie E a => x)
  have hf : ContinuousOn f (invSet E a) := by
    intro w hw
    apply ContinuousAt.continuousWithinAt
    have hdet : IsUnit (Matrix.of w).det := (Matrix.isUnit_iff_isUnit_det _).1 hw
    have h1 : ContinuousAt (fun x : Lie E a => Ring.inverse (Matrix.of x).det) w := by
      have := NormedRing.inverse_continuousAt hdet.unit
      rw [hdet.unit_spec] at this
      exact this.comp hdetc.continuousAt
    refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => ?_
    simp only [f, toL, Matrix.inv_def, Matrix.smul_apply, Matrix.of_symm_apply, smul_eq_mul]
    exact h1.mul ((continuous_apply j).comp ((continuous_apply i).comp hadj)).continuousAt
  obtain ⟨C1, hC1⟩ := hQ.exists_bound_of_continuousOn (f := fun w : Lie E a => w) continuous_id.continuousOn
  obtain ⟨C2, hC2⟩ := hQ.exists_bound_of_continuousOn (hf.mono hsub)
  refine ⟨1 + C1 + C2, fun y hy => ?_⟩
  have h2 : f (toL y.val) = toL (y⁻¹).val := by
    simp only [f, toL, Equiv.apply_symm_apply, Matrix.coe_units_inv]
  have := hC2 _ hy
  rw [h2] at this
  unfold GlobalTheory.CuspRep.height
  linarith [hC1 _ hy]

end GlobalTheory.HeightBound
