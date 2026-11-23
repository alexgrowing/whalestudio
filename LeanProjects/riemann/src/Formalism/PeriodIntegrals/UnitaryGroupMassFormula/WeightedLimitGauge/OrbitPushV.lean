import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushH

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

variable {k : ℕ}

theorem normSq_real_smul (t : ℝ) (z : ℂ) : Complex.normSq (t • z) = t ^ 2 * Complex.normSq z := by
  rw [Complex.real_smul, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

theorem qf_smul (t : ℝ) (p : (Fin k → ℂ) × ℂ) : qf k (t • p) = t ^ 2 * qf k p := by
  unfold qf
  simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, normSq_real_smul, ← Finset.mul_sum]
  ring

theorem continuous_qf : Continuous (qf k) := by
  unfold qf
  exact (continuous_finsetSum _ fun i _ => Complex.continuous_normSq.comp
    ((continuous_apply i).comp continuous_fst)).sub (Complex.continuous_normSq.comp continuous_snd)

def tau (k : ℕ) (T' : ℝ) (p : (Fin k → ℂ) × ℂ) : ℝ := Real.sqrt (-qf k p / T')

theorem continuous_tau (T' : ℝ) : Continuous (tau k T') :=
  Real.continuous_sqrt.comp (continuous_qf.neg.div_const _)

theorem coneSh_eq {T' : ℝ} (hT' : 0 < T') (E : Set ((Fin k → ℂ) × ℂ)) :
    coneSh k T' E = {p | qf k p < 0 ∧ 1 < tau k T' p ∧ tau k T' p < 2 ∧ (tau k T' p)⁻¹ • p ∈ E} := by
  ext p
  constructor
  · rintro ⟨⟨v, t⟩, ⟨⟨hvE, hvS⟩, ht1, ht2⟩, rfl⟩
    have hv : qf k v = -T' := hvS
    have hq : qf k (t • v) = -(t ^ 2 * T') := by rw [qf_smul, hv]; ring
    have htau : tau k T' (t • v) = t := by
      unfold tau
      rw [hq, neg_neg, mul_div_assoc, div_self hT'.ne', mul_one, Real.sqrt_sq (by have : 1 < t := ht1; linarith)]
    have ht1' : 1 < t := ht1
    have hpos : 0 < t ^ 2 * T' := mul_pos (pow_pos (by linarith) 2) hT'
    refine ⟨by rw [hq]; linarith, by rw [htau]; exact ht1, by rw [htau]; exact ht2, ?_⟩
    rw [htau, smul_smul, inv_mul_cancel₀ (by linarith : t ≠ 0), one_smul]
    exact hvE
  · rintro ⟨hneg, h1, h2, hE⟩
    have hq0 : qf k p ≠ 0 := hneg.ne
    have ht2 : tau k T' p ^ 2 = -qf k p / T' := by
      unfold tau
      rw [Real.sq_sqrt (div_nonneg (by linarith) hT'.le)]
    refine ⟨((tau k T' p)⁻¹ • p, tau k T' p), ⟨⟨hE, ?_⟩, h1, h2⟩, ?_⟩
    · show qf k ((tau k T' p)⁻¹ • p) = -T'
      rw [qf_smul, inv_pow, ht2, inv_div, div_mul_eq_mul_div, div_eq_iff (neg_ne_zero.2 hq0)]
      ring
    · show tau k T' p • ((tau k T' p)⁻¹ • p) = p
      rw [smul_smul, mul_inv_cancel₀ (by linarith : tau k T' p ≠ 0), one_smul]

theorem measurableSet_coneSh {T' : ℝ} (hT' : 0 < T') {E : Set ((Fin k → ℂ) × ℂ)} (hE : MeasurableSet E) :
    MeasurableSet (coneSh k T' E) := by
  rw [coneSh_eq hT']
  have hq := (continuous_qf (k := k)).measurable
  have htau := (continuous_tau (k := k) T').measurable
  simp only [Set.ofPred_and]
  refine (measurableSet_lt hq measurable_const).inter ((measurableSet_lt measurable_const htau).inter
    ((measurableSet_lt htau measurable_const).inter ?_))
  exact (htau.inv.smul measurable_id) hE

def phiR (a T' t : ℝ) : ℝ := Real.sqrt (a + t ^ 2 * T')

theorem slice_mem {T' : ℝ} (hT' : 0 < T') (E : Set ((Fin k → ℂ) × ℂ)) (y : Fin k → ℂ) (θ t : ℝ) (ht : 0 < t) :
    (y, ((phiR (∑ i, Complex.normSq (y i)) T' t : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) ∈ coneSh k T' E ↔
      (1 < t ∧ t < 2 ∧ hq k T' (t⁻¹ • y) θ ∈ E) := by
  set a := ∑ i, Complex.normSq (y i) with ha_def
  have ha : 0 ≤ a := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  set φ := phiR a T' t with hφdef
  have hφ0 : 0 ≤ φ := Real.sqrt_nonneg _
  have hφ2 : φ ^ 2 = a + t ^ 2 * T' := Real.sq_sqrt (by positivity)
  have hqv : qf k (y, (φ : ℂ) * Complex.exp (θ * Complex.I)) = -(t ^ 2 * T') := by
    unfold qf
    simp only
    rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq (Complex.exp _),
      Complex.norm_exp_ofReal_mul_I, ← ha_def]
    linear_combination (-1 : ℝ) * hφ2
  have htau : tau k T' (y, (φ : ℂ) * Complex.exp (θ * Complex.I)) = t := by
    unfold tau
    rw [hqv, neg_neg, mul_div_assoc, div_self hT'.ne', mul_one, Real.sqrt_sq ht.le]
  have hsc : (t⁻¹ : ℝ) • ((y, (φ : ℂ) * Complex.exp (θ * Complex.I)) : (Fin k → ℂ) × ℂ) =
      hq k T' (t⁻¹ • y) θ := by
    unfold hq
    have hs : ∑ i, Complex.normSq ((t⁻¹ • y) i) = t⁻¹ ^ 2 * a := by
      simp only [Pi.smul_apply, normSq_real_smul, ← Finset.mul_sum, ha_def]
    have hr : Real.sqrt (∑ i, Complex.normSq ((t⁻¹ • y) i) + T') = t⁻¹ * φ := by
      rw [hs, show t⁻¹ ^ 2 * a + T' = (t⁻¹ * φ) ^ 2 by
        rw [mul_pow, hφ2]; field_simp]
      exact Real.sqrt_sq (mul_nonneg (inv_nonneg.2 ht.le) hφ0)
    rw [hr, Prod.smul_mk, Complex.real_smul]
    push_cast
    ring_nf
  rw [coneSh_eq hT']
  simp only [Set.mem_ofPred_eq]
  rw [htau, hsc]
  constructor
  · rintro ⟨-, h1, h2, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h1, h2, h3⟩
    rw [hqv]
    have : 0 < t ^ 2 * T' := by positivity
    linarith

end PI.RhsWLim.W
