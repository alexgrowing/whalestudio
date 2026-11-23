import Development.WeilBound.CoreStatements.CentralCharts.TraceMulReNonneg
import Development.WeilBound.CoreStatements.CentralCharts.ContDiffAtLogNorm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodGramSmoothPuncturedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodGramComparisonBoundStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GramMatrixSubScalarPosSemidefStatement

noncomputable section

namespace AnalyticReference.An.H

open ReciprocityTheory.AnForm GlobalTheory.CompanionTheory.Ar Filter Topology Matrix
open scoped ComplexOrder

theorem contDiffAt_logdet {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {r : ℕ} {m : WithTop ℕ∞}
    {Γ : E → Matrix (Fin r) (Fin r) ℂ} {t : E} (h : ∀ p q, ContDiffAt ℝ m (fun u => Γ u p q) t) (hp : (Γ t).PosDef) :
    ContDiffAt ℝ m (fun u => Real.log (Γ u).det.re) t := by
  classical
  have hdet : ContDiffAt ℝ m (fun u => (Γ u).det) t := by
    simp only [Matrix.det_apply]
    refine ContDiffAt.sum fun σ _ => ?_
    refine ContDiffAt.const_smul _ ?_
    exact contDiffAt_prod fun i _ => h (σ i) i
  have hre : ContDiffAt ℝ m (fun u => (Γ u).det.re) t :=
    Complex.reCLM.contDiff.contDiffAt.comp t hdet
  refine hre.log ?_
  have hpos := hp.det_pos
  have h0 : 0 < (Γ t).det.re := (Complex.pos_iff.mp hpos).1
  exact h0.ne'

variable {n a : ℕ}

theorem tame_logdet {a₀ k r : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a₀ k Λ)
    (U : Fin r → (Fin n → ℂ) → Fin k → ℂ) (π : Equiv.Perm (Fin n)) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hU : ∀ j, DifferentiableOn ℂ (U j) (Metric.ball 0 1)) (hli : LinearIndependent ℂ fun j => U j 0)
    (ha : ∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < a) :
    Tame a fun t => Real.log (HodgeMetric.periodGram L U (HodgeMetric.uncentre 0 ρ π t)).det.re := by
  classical
  obtain ⟨ε, c, C, hε, hερ, hc, hC, hB⟩ := GlobalTheory.T.period_gram_comparison_bound n a₀ k r a Λ L U 0 π ρ hρ hρ1 hU hli
    (fun i hi => ⟨ha i hi, rfl⟩)
  set G : (Fin n → ℂ) → Matrix (Fin r) (Fin r) ℂ :=
    fun y => HodgeMetric.periodGram L U (HodgeMetric.uncentre 0 ρ π y) with hGdef
  have hpunct : ∀ y : Fin n → ℂ, ‖y‖ < ε → (∀ i : Fin n, (i : ℕ) < a → y i ≠ 0) →
      HodgeMetric.uncentre 0 ρ π y ∈ Flat.punct n a₀ 1 := by
    intro y hy hy0
    refine ⟨HodgeMetric.uncentre_mem_ball hρ π (by simpa using hy.trans_le hερ), ?_⟩
    intro i hi
    simp only [HodgeMetric.uncentre, Pi.zero_apply, sub_zero]
    exact mul_ne_zero (inv_ne_zero (by exact_mod_cast hρ.ne')) (hy0 _ (ha i hi))
  have hB' : ∀ y : Fin n → ℂ, ‖y‖ < ε → ‖y‖ < 1 → (∀ i : Fin n, (i : ℕ) < a → y i ≠ 0) →
      ((G y)⁻¹ - (c : ℂ) • 1).PosSemidef ∧ (((C * logR a y : ℝ) : ℂ) • 1 - (G y)⁻¹).PosSemidef ∧
      ∀ p q, ‖fderiv ℝ (fun y' => G y' p q) y‖ ≤ C * Real.exp (logR a y / 2) := by
    intro y hy hy1 hy0
    exact hB y (by simpa using hy) hy1 (hpunct y hy hy0)
  have hPD : ∀ y : Fin n → ℂ, ‖y‖ < ε → ‖y‖ < 1 → (∀ i : Fin n, (i : ℕ) < a → y i ≠ 0) →
      (G y).PosDef := fun y hy hy1 hy0 => posDef_of_inv_ge hc (hB' y hy hy1 hy0).1
  have hentry : ∀ y : Fin n → ℂ, ‖y‖ < ε → (∀ i : Fin n, (i : ℕ) < a → y i ≠ 0) →
      ∀ p q, ContDiffAt ℝ (⊤ : ℕ∞) (fun u => G u p q) y := by
    intro y hy hy0 p q
    exact (GlobalTheory.T.period_gram_smooth_punctured n a₀ k r Λ L U hU p q _ (hpunct y hy hy0)).comp y
      (HodgeMetric.contDiff_uncentre 0 ρ π).contDiffAt
  have hgood : ∀ y : Fin n → ℂ, ‖y‖ < ε → ‖y‖ < 1 → (∀ i : Fin n, (i : ℕ) < a → y i ≠ 0) →
      ∀ᶠ z in 𝓝 y, ‖z‖ < ε ∧ ‖z‖ < 1 ∧ ∀ i : Fin n, (i : ℕ) < a → z i ≠ 0 := by
    intro y hy hy1 hy0
    refine (continuous_norm.continuousAt.eventually_lt continuousAt_const hy).and
      ((continuous_norm.continuousAt.eventually_lt continuousAt_const hy1).and ?_)
    refine Filter.eventually_all.2 fun i => ?_
    by_cases hi : (i : ℕ) < a
    · have hc' : ContinuousAt (fun z : Fin n → ℂ => z i) y := (continuous_apply i).continuousAt
      filter_upwards [hc'.eventually_ne (hy0 i hi)] with z hz _ using hz
    · exact Filter.Eventually.of_forall fun z h => absurd h hi
  refine tame_of (C₁ := r * (|Real.log c| + |Real.log C| + 1))
    (C₂ := 3 * r ^ 4 * (max 1 c⁻¹) ^ 2 * max (max 1 c⁻¹) C * C) (e := 1) hε (by positivity)
    (by positivity) zero_le_one ?_
  intro y hy hy1 hy0
  have hB1 := hB' y hy hy1 hy0
  have hpd := hPD y hy hy1 hy0
  have hR1 : 1 ≤ logR a y := one_le_logR hy1 hy0
  have hLL : 1 ≤ Real.log (logR a y) := one_le_log_logR hy1 hy0
  have hK : 0 < C * logR a y := mul_pos hC (by linarith)
  refine ⟨contDiffAt_logdet (Γ := G) (hentry y hy hy0) hpd, ?_, ?_⟩
  · have hlo := logdet_mono (posDef_smul_one (r := r) hc) hpd.inv hB1.1
    have hhi := logdet_mono hpd.inv (posDef_smul_one (r := r) hK) hB1.2.1
    rw [logdet_smul_one hc, logdet_inv hpd] at hlo
    rw [logdet_smul_one hK, logdet_inv hpd, Real.log_mul hC.ne' (by linarith)] at hhi
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have h1 : -|Real.log c| ≤ Real.log c := neg_abs_le _
    have h2 : Real.log C ≤ |Real.log C| := le_abs_self _
    have h3 : -((r : ℝ) * |Real.log c|) ≤ r * Real.log c := by
      have := mul_le_mul_of_nonneg_left h1 hr
      rwa [mul_neg] at this
    have p1 : 0 ≤ (r : ℝ) * |Real.log C| := mul_nonneg hr (abs_nonneg _)
    have p2 : 0 ≤ (r : ℝ) * |Real.log c| := mul_nonneg hr (abs_nonneg _)
    have p3 : (r : ℝ) * (|Real.log c| + |Real.log C|) ≤
        r * (|Real.log c| + |Real.log C|) * Real.log (logR a y) := by
      have : 0 ≤ (r : ℝ) * (|Real.log c| + |Real.log C|) := by positivity
      nlinarith
    have h4 : (r : ℝ) * Real.log C ≤ r * |Real.log C| := mul_le_mul_of_nonneg_left h2 hr
    have h5 : (r : ℝ) * (|Real.log c| + |Real.log C| + 1) ≤
        r * (|Real.log c| + |Real.log C| + 1) * Real.log (logR a y) := by
      have : 0 ≤ (r : ℝ) * (|Real.log c| + |Real.log C| + 1) := by positivity
      nlinarith
    have h6 : (r : ℝ) * Real.log (logR a y) ≤ r * (|Real.log c| + |Real.log C| + 1) * Real.log (logR a y) := by
      have : 0 ≤ Real.log (logR a y) := by linarith
      have : (0 : ℝ) ≤ |Real.log c| + |Real.log C| := by positivity
      nlinarith
    rw [abs_le]
    constructor <;> linarith
  · set P : ℝ := max 1 c⁻¹ with hP
    set Q : ℝ := max P C * Real.exp (logR a y / 2) with hQ
    have hP1 : 1 ≤ P := le_max_left _ _
    have hE : 1 ≤ Real.exp (logR a y / 2) := Real.one_le_exp (by linarith)
    have hPQ : P ≤ Q := by
      have : P ≤ max P C := le_max_left _ _
      have : 0 ≤ max P C := by linarith
      nlinarith
    have hd := GlobalTheory.T.gram_matrix_sub_scalar_posSemidef r r (Fin n → ℂ) G (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) y
      (C * logR a y)⁻¹ P Q (inv_pos.2 hK) (by linarith) hPQ
      (fun p q => ((hentry y hy hy0 p q).differentiableAt (by simp)))
      (fun p q => differentiableAt_const _)
      (by
        filter_upwards [hgood y hy hy1 hy0] with z hz
        refine ⟨hPD z hz.1 hz.2.1 hz.2.2, ?_⟩
        have h1 : (1 : Matrix (Fin r) (Fin r) ℂ) = ⇑(Pi.basisFun ℂ (Fin r)) := by
          ext i j
          simp [Matrix.one_apply, Pi.single_apply, eq_comm]
        rw [Matrix.transpose_one, h1]
        exact (Pi.basisFun ℂ (Fin r)).linearIndependent)
      (by
        rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
        exact ge_of_inv_le hK hpd hB1.2.1)
      (fun p q => ⟨(norm_entry_le hpd.posSemidef (le_of_inv_ge hc hpd hB1.1) p q).trans (le_max_right _ _),
        (hB1.2.2 p q).trans (by
          have : C ≤ max P C := le_max_right _ _
          have : 0 ≤ Real.exp (logR a y / 2) := by positivity
          nlinarith)⟩)
      (fun p q => ⟨by
          rw [Matrix.one_apply]
          split_ifs <;> simp <;> linarith,
        by simp [fderiv_const_apply]; linarith⟩)
    simp only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at hd
    refine hd.trans (le_of_eq ?_)
    rw [Real.rpow_one, hQ, div_inv_eq_mul]
    ring

end AnalyticReference.An.H
