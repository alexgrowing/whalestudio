import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.DualExponentDensity
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ActionCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LocalDensityEuler
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeTensorUnfolding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke
open scoped ENNReal TensorProduct

namespace GlobalTheory.PerpFrameOfMatrix

theorem herm_eq_dot {P Q : ℕ} (u v : ActionCoordinates.Wsp P Q) :
    ActionCoordinates.herm u v = star v ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ u := by
  simp [ActionCoordinates.herm, ActionCoordinates.sgn, Formalism.UG.Jpq, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type,
    mul_comm, neg_mulVec]

theorem isPerpFrame_of_matrix : ∀ (P Q P' Q' : ℕ), P' + Q' + 1 = P + Q → ∀ x : ActionCoordinates.Wsp P Q, ActionCoordinates.qf x ≠ 0 → ∀ C : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ, Cᴴ * Formalism.UG.Jpq P Q * C = Formalism.UG.Jpq P' Q' → (Cᴴ * Formalism.UG.Jpq P Q) *ᵥ x = 0 → ∀ ι : UpqT P' Q' → UpqT P Q, (∀ b, UpqT.mat (ι b) * C = C * UpqT.mat b ∧ UpqT.mat (ι b) *ᵥ x = x) → ActionCoordinates.IsPerpFrame x (Matrix.toLin' C) ι := by
  intro P Q P' Q' hc x hx C h1 h2 ι hι
  have hx' : star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ x ≠ 0 := by
    rw [← herm_eq_dot, ActionCoordinates.herm_self]; exact_mod_cast hx
  have hperp : ∀ v, star x ⬝ᵥ Formalism.UG.Jpq P Q *ᵥ (C *ᵥ v) = 0 := fun v => by
    have h3 : star x ᵥ* (Formalism.UG.Jpq P Q * C) = 0 := by
      have := congrArg star h2
      rwa [star_mulVec, conjTranspose_mul, conjTranspose_conjTranspose,
        GlobalTheory.UnfoldingCompare.Jpq_conjTranspose, star_zero] at this
    rw [mulVec_mulVec, dotProduct_mulVec, h3, zero_dotProduct]
  refine ⟨fun v w => ?_, fun y => ⟨fun hy => ?_, ?_⟩, fun g => ⟨(hι g).2, fun v => ?_⟩⟩
  · rw [herm_eq_dot, herm_eq_dot, toLin'_apply, toLin'_apply, star_mulVec, mulVec_mulVec,
      ← dotProduct_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, h1]
  · obtain ⟨N, B, -, hN, -⟩ := GlobalTheory.UnfoldingCompare.exists_frame_inv hc hx' h1 h2
    have e : y = C *ᵥ ((N *ᵥ y) ∘ Sum.inl) + (N *ᵥ y) (Sum.inr ()) • x := by
      conv_lhs => rw [← one_mulVec y, ← hN, ← mulVec_mulVec, fromCols_mulVec]
      congr 1
      funext i
      simp [mulVec, dotProduct, mul_comm]
    have ha : (N *ᵥ y) (Sum.inr ()) = 0 := by
      rw [herm_eq_dot, e, mulVec_add, mulVec_smul, dotProduct_add, hperp, zero_add,
        dotProduct_smul, smul_eq_mul] at hy
      exact (mul_eq_zero.1 hy).resolve_right hx'
    refine ⟨(N *ᵥ y) ∘ Sum.inl, ?_⟩
    rw [ha, zero_smul, add_zero] at e
    rw [toLin'_apply, ← e]
  · rintro ⟨v, rfl⟩
    rw [herm_eq_dot, toLin'_apply, hperp]
  · simp only [ActionCoordinates.act, toLin'_apply, mulVec_mulVec, (hι g).1]

end GlobalTheory.PerpFrameOfMatrix
