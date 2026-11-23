import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat

set_option autoImplicit false

namespace GlobalTheory.CompHt

open Filter Topology
open scoped ENNReal

set_option autoImplicit false in
open Filter Topology in
open scoped ENNReal in
private lemma factorial_mul_div_pow_ennreal_eq_ofReal (D k m : ℕ) (hk : 1 ≤ k) :
    (D.factorial : ℝ≥0∞) * ((m : ℕ∞) : ℝ≥0∞) / (k : ℝ≥0∞) ^ D =
      ENNReal.ofReal ((D.factorial : ℝ) * (m : ℝ) / (k : ℝ) ^ D) := by
  have hk' : (0 : ℝ) < (k : ℝ) ^ D := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  rw [ENNReal.ofReal_div_of_pos hk', ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by positivity)]
  simp

set_option autoImplicit false in
open Filter Topology in
open scoped ENNReal in
private lemma tendsto_eval_div_pow_atTop_coeff_of_degree_le (Q : Polynomial ℝ) (D : ℕ) (hQ : Q.degree ≤ D) :
    Tendsto (fun y : ℝ => Q.eval y / y ^ D) atTop (𝓝 (Q.coeff D)) := by
  have hX : (Polynomial.X ^ D : Polynomial ℝ).degree = D := by simp
  rcases hQ.lt_or_eq with hlt | heq
  · have hc : Q.coeff D = 0 := Polynomial.coeff_eq_zero_of_degree_lt hlt
    rw [hc]
    simpa using Polynomial.div_tendsto_zero_of_degree_lt Q (Polynomial.X ^ D) (by rw [hX]; exact hlt)
  · have hc : Q.leadingCoeff = Q.coeff D := by
      rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some heq]
    have := Polynomial.div_tendsto_leadingCoeff_div_of_degree_eq Q (Polynomial.X ^ D) (by rw [hX, heq])
    simpa [hc] using this

set_option autoImplicit false in
open Filter Topology in
open scoped ENNReal in

theorem _root_.GlobalTheory.CompHt.growth_of_eventually_eq_eval :
    ∀ (D a : ℕ) (h : ℕ → ℕ) (H : Polynomial ℚ), 1 ≤ a → (∀ᶠ n : ℕ in atTop, (h n : ℚ) = H.eval (n : ℚ)) →
      (H.degree ≤ D → ∀ δ : ℕ, (δ : ℚ) = (D.factorial : ℚ) * H.coeff D →
        _root_.GlobalTheory.CompHt.growth D (fun k => (h (a * k) : ℕ∞)) = (a : ℝ≥0∞) ^ D * δ) ∧
      ((D : WithBot ℕ) < H.degree → _root_.GlobalTheory.CompHt.growth D (fun k => (h (a * k) : ℕ∞)) = ⊤) := by
  intro D a h H ha hev
  set Q : Polynomial ℝ := H.map (algebraMap ℚ ℝ) with hQdef
  have hQdeg : Q.degree = H.degree := Polynomial.degree_map _ _

  have hak : Tendsto (fun k : ℕ => a * k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left k ha) tendsto_id
  have hakR : Tendsto (fun k : ℕ => ((a * k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hak

  have hval : ∀ᶠ k : ℕ in atTop, (h (a * k) : ℝ) = Q.eval ((a * k : ℕ) : ℝ) := by
    filter_upwards [hak.eventually hev] with k hk
    have hcast : ((a * k : ℕ) : ℝ) = algebraMap ℚ ℝ ((a * k : ℕ) : ℚ) := by simp
    rw [hQdef, Polynomial.eval_map, hcast, Polynomial.eval₂_at_apply, ← hk]
    simp

  set g : ℕ → ℝ := fun k => (D.factorial : ℝ) * (h (a * k) : ℝ) / (k : ℝ) ^ D with hg
  have hg_eq : ∀ᶠ k : ℕ in atTop, g k = (D.factorial : ℝ) * (a : ℝ) ^ D *
      (Q.eval ((a * k : ℕ) : ℝ) / ((a * k : ℕ) : ℝ) ^ D) := by
    filter_upwards [hval, eventually_ge_atTop 1] with k hk hk1
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
    simp only [hg]
    rw [hk]
    push_cast
    field_simp
    ring
  have hlim : _root_.GlobalTheory.CompHt.growth D (fun k => (h (a * k) : ℕ∞)) = limsup (fun k => ENNReal.ofReal (g k)) atTop := by
    unfold _root_.GlobalTheory.CompHt.growth
    refine limsup_congr ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact factorial_mul_div_pow_ennreal_eq_ofReal D k (h (a * k)) hk
  refine ⟨fun hdeg δ hδ => ?_, fun hdeg => ?_⟩
  · have hT : Tendsto g atTop (𝓝 ((D.factorial : ℝ) * (a : ℝ) ^ D * Q.coeff D)) := by
      refine Tendsto.congr' (EventuallyEq.symm hg_eq) ?_
      exact ((tendsto_eval_div_pow_atTop_coeff_of_degree_le Q D (hQdeg ▸ hdeg)).comp hakR).const_mul _
    rw [hlim, (ENNReal.tendsto_ofReal hT).limsup_eq]
    have hc : (D.factorial : ℝ) * (a : ℝ) ^ D * Q.coeff D = ((a ^ D * δ : ℕ) : ℝ) := by
      rw [hQdef, Polynomial.coeff_map]
      have : ((δ : ℚ) : ℝ) = ((D.factorial : ℚ) * H.coeff D : ℚ) := by rw [hδ]
      push_cast at this ⊢
      rw [this]
      simp only [eq_ratCast]
      ring
    rw [hc, ENNReal.ofReal_natCast]
    push_cast
    rfl
  · have hQdeg' : (D : WithBot ℕ) < Q.degree := hQdeg ▸ hdeg
    have hX : (Polynomial.X ^ D : Polynomial ℝ).degree = D := by simp
    have hlc : 0 < Q.leadingCoeff := by
      by_contra hneg
      push_neg at hneg
      have hpos : 0 < Q.degree := lt_of_le_of_lt (by exact_mod_cast Nat.zero_le D) hQdeg'
      have hbot := (Polynomial.tendsto_atBot_of_leadingCoeff_nonpos Q hpos hneg).comp hakR
      have hneg' := hbot.eventually (eventually_lt_atBot (0 : ℝ))
      obtain ⟨k, hk1, hk2⟩ := (hneg'.and hval).exists
      simp only [Function.comp_apply] at hk1
      rw [← hk2] at hk1
      exact absurd hk1 (not_lt.2 (Nat.cast_nonneg _))
    have hT : Tendsto g atTop atTop := by
      refine Tendsto.congr' (EventuallyEq.symm hg_eq) ?_
      refine Tendsto.const_mul_atTop (by positivity) ?_
      refine (Polynomial.div_tendsto_atTop_of_degree_gt Q (Polynomial.X ^ D) (by rw [hX]; exact hQdeg')
        (by simp) ?_).comp hakR |>.congr fun k => by simp
      simpa using hlc.le
    rw [hlim]
    exact (ENNReal.tendsto_ofReal_atTop.comp hT).limsup_eq

end GlobalTheory.CompHt
