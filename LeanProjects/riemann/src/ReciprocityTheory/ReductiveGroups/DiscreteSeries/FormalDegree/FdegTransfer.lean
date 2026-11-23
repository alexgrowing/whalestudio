import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarMirror

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem isFdeg_smul {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {μ : Measure (Formalism.REAL.UJ ε)} {d c : ℝ} (hc : 0 < c)
    (hd : Formalism.MainNotions.S.IsFdeg μ σ d) : Formalism.MainNotions.S.IsFdeg (ENNReal.ofReal c • μ) σ (d / c) := by
  obtain ⟨hd0, hd⟩ := hd
  refine ⟨div_pos hd0 hc, fun v w v' w' => ?_⟩
  obtain ⟨hi, he⟩ := hd v w v' w'
  refine ⟨hi.smul_measure ENNReal.ofReal_ne_top, ?_⟩
  rw [integral_smul_measure, he, ENNReal.toReal_ofReal hc.le, Complex.real_smul,
    Complex.ofReal_div, div_div_eq_mul_div]
  ring

theorem isFdeg_muCD {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {μ : Measure (Formalism.REAL.UJ ε)} [μ.IsHaarMeasure] {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg μ σ d) : ∃ d' : ℝ, Formalism.MainNotions.S.IsFdeg (muCD ε) σ d' := by
  haveI := muCD_isHaar ε
  obtain ⟨c, hcpos, hsm⟩ : ∃ c : NNReal, 0 < c ∧ muCD ε = c • μ :=
    ⟨_, Measure.haarScalarFactor_pos_of_isHaarMeasure (muCD ε) μ,
      Measure.isMulLeftInvariant_eq_smul (muCD ε) μ⟩
  have hsm' : muCD ε = ((c : NNReal) : ENNReal) • μ := by
    rw [hsm]
    ext s _
    rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def]
  have h := isFdeg_smul (NNReal.coe_pos.mpr hcpos) hd
  rw [ENNReal.ofReal_coe_nnreal, ← hsm'] at h
  exact ⟨_, h⟩

theorem fdegOf_of_isFdeg' {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {μ : Measure (Formalism.REAL.UJ ε)} {d : ℝ}
    (hd : Formalism.MainNotions.S.IsFdeg μ σ d) {w : H} (hw : w ≠ 0) : Formalism.MainNotions.S.fdegOf μ σ w = d := by
  obtain ⟨hd0, hd⟩ := hd
  obtain ⟨-, he⟩ := hd w w w w
  have h1 : (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.coefOn σ w w g * star (Formalism.MainNotions.S.coefOn σ w w g)) =
      fun g : Formalism.REAL.UJ ε => ((‖Formalism.MainNotions.S.coefOn σ w w g‖ ^ 2 : ℝ) : ℂ) := by
    funext g
    rw [← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hw2 : ⟪w, w⟫_ℂ = ((‖w‖ : ℝ) : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K w
  rw [h1, integral_complex_ofReal, hw2] at he
  have hint : (∫ g, ‖Formalism.MainNotions.S.coefOn σ w w g‖ ^ 2 ∂μ) = ‖w‖ ^ 4 / d := by
    have h2 : ((∫ g, ‖Formalism.MainNotions.S.coefOn σ w w g‖ ^ 2 ∂μ : ℝ) : ℂ) = ((‖w‖ ^ 4 / d : ℝ) : ℂ) := by
      rw [he]
      push_cast
      ring
    exact_mod_cast h2
  have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  rw [Formalism.MainNotions.S.fdegOf, hint, div_div_cancel₀ (pow_ne_zero 4 hw')]

end ReciprocityTheory.ChartRestriction.DS
