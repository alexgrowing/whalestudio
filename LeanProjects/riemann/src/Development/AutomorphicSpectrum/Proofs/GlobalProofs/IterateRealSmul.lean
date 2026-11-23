import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AnalyticVectorExponentialSeriesStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVectorStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionAdditiveStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraOfLinearGroupClosedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableAtOrbit

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.OneParam

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem mnorm_real_smul (s : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : mnorm (s • X) = |s| * mnorm X := by
  unfold mnorm
  simp only [Matrix.smul_apply, norm_smul, Real.norm_eq_abs, Finset.mul_sum]

theorem mnorm_nonneg (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ mnorm X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem iterate_smooth (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hs : IsSmoothVec G π v)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (m : ℕ) :
    IsSmoothVec G π ((dRep π X)^[m] v) := by
  induction m with
  | zero => simpa using hs
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact (GlobalTheory.T.derived_action_of_smooth_vector hG hrep ih hX).2

theorem iterate_real_smul (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hs : IsSmoothVec G π v)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (s : ℝ) (m : ℕ) :
    (dRep π (s • X))^[m] v = ((s : ℂ) ^ m) • (dRep π X)^[m] v := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsm := iterate_smooth hG hrep hs hX m
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', GlobalTheory.GKLie.dRep_smul,
      (GlobalTheory.T.derived_action_additive hG hrep hsm hsm hX hX).2.2, ← Complex.coe_smul, smul_smul, pow_succ']

theorem analytic_coeff : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hU : IsURepOn G π) {v : H} (hs : IsSmoothVec G π v) (hw : WordBound G π v)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (w : H),
    AnalyticOnNhd ℝ (fun t : ℝ => ⟪w, π (NormedSpace.exp (t • X)) v⟫_ℂ) Set.univ := by
  intro n G H _ _ _ π hG hU v hs hw X hX w t₀ _
  obtain ⟨r, hr, hsum⟩ := GlobalTheory.T.analytic_vector_exponential_series hG hU.1 hU.2.2 hs hw
  have hrep := hU.1
  let L : H →L[ℂ] ℂ := (innerSL ℂ w).comp (π (NormedSpace.exp (t₀ • X)))
  let a : ℕ → ℂ := fun m => ((m.factorial : ℂ)⁻¹) * L ((dRep π X)^[m] v)
  have key : ∀ s : ℝ, |s| * mnorm X < r → HasSum (fun m : ℕ => (s : ℂ) ^ m * a m)
      (⟪w, π (NormedSpace.exp ((t₀ + s) • X)) v⟫_ℂ) := by
    intro s hs'
    have h1 := hsum (s • X) ((GlobalTheory.T.lie_algebra_of_linear_group_closed hG).2.1 s X hX) (by rwa [mnorm_real_smul])
    have h2 := L.hasSum h1
    have e : ⟪w, π (NormedSpace.exp ((t₀ + s) • X)) v⟫_ℂ = L (π (NormedSpace.exp (s • X)) v) := by
      have hc : Commute (t₀ • X) (s • X) := ((Commute.refl X).smul_left t₀).smul_right s
      rw [add_smul, Matrix.exp_add_of_commute _ _ hc, hrep.2 _ (hX t₀) _ (hX s)]
      rfl
    rw [e]
    convert h2 using 2 with m
    rw [iterate_real_smul hG hrep hs hX s m]
    simp only [a, map_smul, smul_eq_mul]
    ring
  let p : FormalMultilinearSeries ℝ ℝ ℂ := fun m => ContinuousMultilinearMap.mkPiRing ℝ (Fin m) (a m)
  have hpa : ∀ (m : ℕ) (s : ℝ), p m (fun _ => s) = (s : ℂ) ^ m * a m := by
    intro m s
    simp [p, ContinuousMultilinearMap.mkPiRing_apply]
  have hM : 0 < mnorm X + 1 := by linarith [mnorm_nonneg X]
  have hsmall : ∀ s : ℝ, |s| < r / (mnorm X + 1) → |s| * mnorm X < r := by
    intro s h
    rw [lt_div_iff₀ hM] at h
    nlinarith [abs_nonneg s]
  set ε : ℝ := r / (mnorm X + 1) with hε
  have hεpos : 0 < ε := div_pos hr hM
  have hrad : 0 < p.radius := by
    have hs0 : |ε / 2| < ε := by rw [abs_of_pos (by linarith)]; linarith
    have hS := (key (ε / 2) (hsmall _ hs0)).summable.norm
    let ρ : NNReal := ⟨ε / 2, by linarith⟩
    have hρ : (0 : NNReal) < ρ := by
      change (0 : ℝ) < ε / 2
      linarith
    have : (ρ : ENNReal) ≤ p.radius := by
      refine p.le_radius_of_summable_norm ?_
      refine hS.congr fun m => ?_
      have hρc : ((ρ : NNReal) : ℝ) = ε / 2 := rfl
      simp [p, hρc, ContinuousMultilinearMap.norm_mkPiRing, abs_of_pos hεpos, mul_comm]
    exact lt_of_lt_of_le (by exact_mod_cast hρ) this
  have han : AnalyticAt ℝ p.sum 0 := (p.hasFPowerSeriesOnBall hrad).analyticAt
  have han2 : AnalyticAt ℝ (fun t : ℝ => p.sum (t - t₀)) t₀ :=
    AnalyticAt.comp_of_eq (g := p.sum) (f := fun t : ℝ => t - t₀) han
      (analyticAt_id.sub analyticAt_const) (by simp)
  refine han2.congr ?_
  filter_upwards [Metric.ball_mem_nhds t₀ hεpos] with t ht
  have hd : |t - t₀| < ε := by simpa [Real.dist_eq] using ht
  have h3 := key (t - t₀) (hsmall _ hd)
  rw [show t₀ + (t - t₀) = t by ring] at h3
  simp only [FormalMultilinearSeries.sum, hpa]
  exact h3.tsum_eq

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.OneParam

end
