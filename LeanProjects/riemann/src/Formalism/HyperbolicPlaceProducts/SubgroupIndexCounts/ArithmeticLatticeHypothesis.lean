import Formalism.HyperbolicPlaceProducts.DetIndexProductHyperbolicInequality

namespace Formalism.SLP.GlobalBoundRefinements.P
open Formalism.SLP.GlobalBoundRefinements

theorem matrix_entries_integral (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.conjTranspose * J * M = J) :
    ‖M 0 0‖ ^ 2 - ‖M 1 0‖ ^ 2 = 1 ∧ ‖M 0 1‖ ^ 2 - ‖M 1 1‖ ^ 2 = -1 ∧
      ‖M 0 0‖ * ‖M 0 1‖ = ‖M 1 0‖ * ‖M 1 1‖ := by
  have e00 := congrFun (congrFun hM 0) 0
  have e11 := congrFun (congrFun hM 1) 1
  have e01 := congrFun (congrFun hM 0) 1
  simp [J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] at e00 e11 e01
  rw [Complex.conj_mul', Complex.conj_mul'] at e00 e11
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast e00
  · exact_mod_cast e11
  · have h : (starRingEnd ℂ) (M 0 0) * M 0 1 = (starRingEnd ℂ) (M 1 0) * M 1 1 := by
      linear_combination e01
    have := congrArg norm h
    simpa [norm_mul] using this

theorem unipotent_upper_entries : EntriesOfSignaturePreserving := by
  intro M hM
  obtain ⟨h1, h2, h3⟩ := matrix_entries_integral M hM
  have hsq : ‖M 0 0‖ ^ 2 * ‖M 0 1‖ ^ 2 = ‖M 1 0‖ ^ 2 * ‖M 1 1‖ ^ 2 := by
    rw [← mul_pow, ← mul_pow, h3]
  have hbc : ‖M 0 1‖ ^ 2 = ‖M 1 0‖ ^ 2 := by nlinarith
  have had : ‖M 0 0‖ ^ 2 = ‖M 1 1‖ ^ 2 := by linarith
  have hbc' : ‖M 0 1‖ = ‖M 1 0‖ := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hbc
  have had' : ‖M 0 0‖ = ‖M 1 1‖ := (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 had
  refine ⟨had', hbc', h1, ?_⟩
  intro sh ch hsh hch hchsh hc
  have hsh0 : sh ≠ 0 := hsh.ne'
  have key : ‖M 0 0‖ ^ 2 = (ch / sh) ^ 2 := by
    have : ‖M 0 0‖ ^ 2 = 1 + (1 / sh) ^ 2 := by rw [← hc]; linarith
    rw [this, div_pow, div_pow, hchsh]
    field_simp
  exact (pow_left_inj₀ (norm_nonneg _) (div_nonneg hch hsh.le) two_ne_zero).1 key

theorem arithmetic_lattice_hypothesis : AlHyp := by
  intro M sh ch u u' hM hsh hch hchsh hc hu
  obtain ⟨_, hbc, _, hA⟩ := unipotent_upper_entries M hM
  have ha := hA sh ch hsh hch hchsh hc
  have hb : ‖M 0 1‖ = 1 / sh := hbc.trans hc
  calc ‖M 0 0 * u + M 0 1 * u'‖ ≤ ‖M 0 0 * u‖ + ‖M 0 1 * u'‖ := norm_add_le _ _
    _ = ch / sh * ‖u‖ + 1 / sh * ‖u‖ := by rw [norm_mul, norm_mul, ha, hb, hu]
    _ = ‖u‖ * (1 + ch) / sh := by ring

end Formalism.SLP.GlobalBoundRefinements.P
