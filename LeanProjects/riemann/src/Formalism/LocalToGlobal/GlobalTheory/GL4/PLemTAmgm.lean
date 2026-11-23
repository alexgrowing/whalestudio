import Mathlib

noncomputable section

open NumberField

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT

variable {E : Type} [Field E] [NumberField E]

theorem abs_norm_eq_prod_re (a : E) (hpos : ∀ φ : E →+* ℂ, ∃ c : ℝ, 0 < c ∧ φ a = c) :
    |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∏ φ : E →+* ℂ, (φ a).re := by
  have h2 := Algebra.norm_eq_prod_embeddings ℚ ℂ a
  have h3 : ∏ σ : E →ₐ[ℚ] ℂ, σ a = ∏ φ : E →+* ℂ, φ a :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ fun σ ↦ rfl
  have hre : ∀ φ : E →+* ℂ, ‖φ a‖ = (φ a).re := by
    intro φ
    obtain ⟨c, hc, he⟩ := hpos φ
    rw [he, Complex.norm_real, Real.norm_of_nonneg hc.le, Complex.ofReal_re]
  have h4 : ‖(algebraMap ℚ ℂ (Algebra.norm ℚ a))‖ = |((Algebra.norm ℚ a : ℚ) : ℝ)| := by
    rw [show (algebraMap ℚ ℂ (Algebra.norm ℚ a)) = (((Algebra.norm ℚ a : ℚ) : ℝ) : ℂ) by simp,
      Complex.norm_real, Real.norm_eq_abs]
  rw [← h4, h2, h3, norm_prod]
  exact Finset.prod_congr rfl fun φ _ ↦ hre φ

theorem sum_re_ge (a : E) (hpos : ∀ φ : E →+* ℂ, ∃ c : ℝ, 0 < c ∧ φ a = c) (X : ℝ) (hX : 0 < X)
    (h1 : 1 ≤ |((Algebra.norm ℚ a : ℚ) : ℝ)| * X) :
    (Module.finrank ℚ E : ℝ) * X ^ (-(1 / (Module.finrank ℚ E : ℝ))) ≤ ∑ φ : E →+* ℂ, (φ a).re := by
  set d : ℝ := ((Module.finrank ℚ E : ℕ) : ℝ) with hd
  have hcard : (Fintype.card (E →+* ℂ) : ℝ) = d := by rw [hd, Embeddings.card]
  have hd0 : 0 < d := by rw [hd]; exact_mod_cast Module.finrank_pos
  have hc : ∀ φ : E →+* ℂ, 0 < (φ a).re := by
    intro φ
    obtain ⟨c, hc, he⟩ := hpos φ
    rw [he, Complex.ofReal_re]; exact hc
  have hP : ∏ φ : E →+* ℂ, (φ a).re = |((Algebra.norm ℚ a : ℚ) : ℝ)| := (abs_norm_eq_prod_re a hpos).symm
  have hPX : X⁻¹ ≤ ∏ φ : E →+* ℂ, (φ a).re := by
    rw [hP, inv_le_iff_one_le_mul₀ hX, mul_comm]; linarith
  have hgm := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (E →+* ℂ)) (fun _ ↦ 1 / d)
    (fun φ ↦ (φ a).re) (fun _ _ ↦ by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]; field_simp)
    (fun φ _ ↦ (hc φ).le)
  rw [Real.finsetProd_rpow _ _ (fun φ _ ↦ (hc φ).le), ← Finset.mul_sum] at hgm
  have hmono : X⁻¹ ^ (1 / d) ≤ (∏ φ : E →+* ℂ, (φ a).re) ^ (1 / d) :=
    Real.rpow_le_rpow (by positivity) hPX (by positivity)
  rw [Real.inv_rpow hX.le, ← Real.rpow_neg hX.le] at hmono
  calc d * X ^ (-(1 / d)) ≤ d * (1 / d * ∑ φ : E →+* ℂ, (φ a).re) := by gcongr; exact hmono.trans hgm
    _ = _ := by field_simp

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
