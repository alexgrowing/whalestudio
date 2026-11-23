import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods

namespace GlobalTheory.PELU

open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

theorem hermForm_pullback_matrix {g : ℕ} (Hm B : Matrix (Fin g) (Fin g) ℂ) (u v : Fin g → ℂ) :
    hermForm (Bᵀ * Hm * B.map star) u v = hermForm Hm (B *ᵥ u) (B *ᵥ v) := by
  unfold hermForm
  have e : star (B *ᵥ v) = B.map star *ᵥ star v := by
    ext i
    simp [Matrix.mulVec, dotProduct]
  rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem IsPeriod.comp_linearEquiv (O : Type) [Ring O] (bar : O → O) (D : PLat O bar) (g : ℕ)
    (ρ ρ₂ : O →+* Matrix (Fin g) (Fin g) ℂ) (P : D.La →+ (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hP : GlobalTheory.PELU.IsPeriod D ρ P) (hh : ∀ a z, h (ρ a *ᵥ z) = ρ₂ a *ᵥ h z) :
    GlobalTheory.PELU.IsPeriod D ρ₂ (h.toLinearMap.toAddMonoidHom.comp P) := by
  obtain ⟨h1, h2, h3, h4, Hm, h5, h6, h7⟩ := hP
  have ev : ∀ x, (h.toLinearMap.toAddMonoidHom.comp P) x = h (P x) := fun _ => rfl
  set B : Matrix (Fin g) (Fin g) ℂ := LinearMap.toMatrix' h.symm.toLinearMap with hB
  have hBv : ∀ u, B *ᵥ u = h.symm u := fun u => by
    rw [hB, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']; rfl
  refine ⟨fun a x => ?_, ?_, ?_, ?_, Bᵀ * Hm * B.map star, ?_, fun z hz => ?_, fun x y => ?_⟩
  · rw [ev, ev, h1, hh]
  · exact h.injective.comp h2
  · let f : (h.toLinearMap.toAddMonoidHom.comp P).range → P.range := fun z =>
      ⟨h.symm z.1, by
        obtain ⟨x, hx⟩ := z.2
        exact ⟨x, by rw [← hx, ev, h.symm_apply_apply]⟩⟩
    have hc : Continuous f :=
      Continuous.subtype_mk (h.symm.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val) _
    have hi : Function.Injective f := fun a b e => Subtype.ext (h.symm.injective (congrArg Subtype.val e))
    exact DiscreteTopology.of_continuous_injective hc hi
  · have e : Set.range (h.toLinearMap.toAddMonoidHom.comp P) = (h.toLinearMap.restrictScalars ℝ) '' Set.range P := by
      rw [← Set.range_comp]; rfl
    rw [e, ← Submodule.map_span, h4, Submodule.map_top, LinearMap.range_eq_top]
    exact h.surjective
  · have e1 : (B.map star)ᴴ = Bᵀ := by
      ext i j; simp [Matrix.conjTranspose_apply]
    have e2 : (Bᵀ)ᴴ = B.map star := by
      ext i j; simp [Matrix.conjTranspose_apply]
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, e1, e2, h5.eq, Matrix.mul_assoc]
  · rw [hermForm_pullback_matrix, hBv]
    exact h6 _ (fun e => hz (h.symm.map_eq_zero_iff.mp e))
  · rw [hermForm_pullback_matrix, hBv, hBv, ev, ev, h.symm_apply_apply, h.symm_apply_apply, h7]

end GlobalTheory.PELU
