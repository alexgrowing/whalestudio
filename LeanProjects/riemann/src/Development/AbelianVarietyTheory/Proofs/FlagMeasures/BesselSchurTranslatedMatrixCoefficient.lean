import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Formalism.FormalDegreeBessel.FinalG
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem schur_translated_coef : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ), Std σ w a μG d → ∀ u u₁ v : H, ∀ t ∈ GG k r, ∫ y, coef σ u v (Matrix.of y) * star (coef σ u₁ v (t * Matrix.of y)) ∂μG = ⟪u₁, u⟫_ℂ * ⟪v, σ t⁻¹ v⟫_ℂ / (d : ℂ) := by
  intro k r H _ _ _ σ w a μG d hStd u u₁ v t ht
  obtain ⟨_, ⟨⟨h1, hmul⟩, hiso, _⟩, _, _, ⟨_, _, hnull, _⟩, ⟨_, hS⟩, _⟩ := hStd
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1
  have hgrp := uHGroup _ (Hpk k r) hH
  have htu : IsUnit t.det := (hgrp.2.2 t ht).1
  have hti : t⁻¹ ∈ GG k r := (hgrp.2.2 t ht).2
  have htt : t * t⁻¹ = 1 := Matrix.mul_nonsing_inv t htu
  let L : H →ₗᵢ[ℂ] H := ⟨(σ t : H →ₗ[ℂ] H), fun x => hiso t ht x⟩
  have hinv : σ t (σ t⁻¹ v) = v := by
    have := hmul t ht t⁻¹ hti
    rw [htt, h1] at this
    have h' := congrArg (fun f : H →L[ℂ] H => f v) this
    simpa using h'.symm
  have hadj : ∀ x : H, ⟪v, σ t x⟫_ℂ = ⟪σ t⁻¹ v, x⟫_ℂ := by
    intro x
    have := L.inner_map_map (σ t⁻¹ v) x
    conv_lhs => rw [← hinv]
    exact this
  have hae : ∀ᵐ y ∂μG, coef σ u v (Matrix.of y) * star (coef σ u₁ v (t * Matrix.of y)) =
      coef σ u v (Matrix.of y) * star (coef σ u₁ (σ t⁻¹ v) (Matrix.of y)) := by
    have hmem : ∀ᵐ y ∂μG, Matrix.of y ∈ GG k r := ae_iff.2 hnull
    filter_upwards [hmem] with y hy
    congr 2
    simp only [coef]
    rw [hmul t ht _ hy, ContinuousLinearMap.comp_apply, hadj]
  rw [integral_congr_ae hae]
  exact (hS u v u₁ (σ t⁻¹ v)).2

end GlobalTheory.SgInf
