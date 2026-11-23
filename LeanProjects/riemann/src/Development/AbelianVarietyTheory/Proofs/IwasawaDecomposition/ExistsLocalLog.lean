import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.LocalLog

theorem exists_local_log (n : ℕ) : ∃ L : Mx n → Mx n, ContinuousAt L 1 ∧ L 1 = 0 ∧
    (∀ᶠ g in 𝓝 (1 : Mx n), NormedSpace.exp (L g) = g) ∧
    ∀ᶠ X in 𝓝 (0 : Mx n), L (NormedSpace.exp X) = X := by
  letI : NormedRing (Mx n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Mx n) := Matrix.linftyOpNormedAlgebra
  have h : HasStrictFDerivAt (NormedSpace.exp : Mx n → Mx n)
      ((ContinuousLinearEquiv.refl ℂ (Mx n) : Mx n ≃L[ℂ] Mx n) : Mx n →L[ℂ] Mx n) 0 :=
    hasStrictFDerivAt_exp_zero (𝕂 := ℂ)
  have h0 : NormedSpace.exp (0 : Mx n) = 1 := NormedSpace.exp_zero
  refine ⟨h.localInverse _ _ _, ?_, ?_, ?_, h.eventually_left_inverse⟩
  · have := h.localInverse_continuousAt
    rwa [h0] at this
  · have := h.localInverse_apply_image
    rwa [h0] at this
  · have := h.eventually_right_inverse
    rwa [h0] at this

theorem local_log_UJ : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ L : Mx n → Mx n, ContinuousAt L 1 ∧ L 1 = 0 ∧
    ∀ᶠ g in 𝓝 (1 : Mx n), g ∈ UJset ε → L g ∈ lieSet ε ∧ NormedSpace.exp (L g) = g := by
  intro n ε
  obtain ⟨L, hc, h1, hr, hl⟩ := exists_local_log n
  refine ⟨L, hc, h1, ?_⟩
  have hJ := Jm_mul_self ε
  have ht : Tendsto (fun g => Jm ε * (-(L g)ᴴ) * Jm ε) (𝓝 1) (𝓝 0) := by
    have hcont : Continuous fun X : Mx n => Jm ε * (-Xᴴ) * Jm ε := by fun_prop
    have := (hcont.tendsto 0).comp (h1 ▸ hc.tendsto)
    simpa [Function.comp_def] using this
  filter_upwards [hr, ht.eventually hl] with g hg hg' hU
  refine ⟨?_, hg⟩
  have hU' : gᴴ * Jm ε * g = Jm ε := hU
  have hinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJ
  have he : NormedSpace.exp (Jm ε * (-(L g)ᴴ) * Jm ε) = g := by
    have h2 := Matrix.exp_conj (Jm ε) (-(L g)ᴴ) (isUnit_Jm ε)
    rw [hinv, Matrix.exp_neg, Matrix.exp_conjTranspose, hg] at h2
    rw [h2]
    have h3 : (gᴴ)⁻¹ = Jm ε * g * Jm ε := by
      apply Matrix.inv_eq_right_inv
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU', hJ]
    rw [h3]
    calc Jm ε * (Jm ε * g * Jm ε) * Jm ε = (Jm ε * Jm ε) * g * (Jm ε * Jm ε) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hJ]; simp
  rw [he] at hg'
  show (L g)ᴴ * Jm ε + Jm ε * L g = 0
  nth_rewrite 2 [hg']
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ]
  simp

end GlobalTheory.LocalLog
