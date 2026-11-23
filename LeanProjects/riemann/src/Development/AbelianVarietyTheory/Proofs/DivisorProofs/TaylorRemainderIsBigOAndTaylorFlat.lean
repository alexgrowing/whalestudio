import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts

open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem taylor_eq_partialSum {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) {f : (I → ℂ) → ℂ}
    {p : FormalMultilinearSeries ℂ (I → ℂ) ℂ} (hp : HasFPowerSeriesAt f p 0) (z : I → ℂ) :
    taylor N z f = p.partialSum (N + 1) z := by
  obtain ⟨r, hr⟩ := hp
  unfold taylor FormalMultilinearSeries.partialSum
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have h1 := hr.factorial_smul z k
  have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
  have h2 : (iteratedFDeriv ℂ k f 0 fun _ ↦ z) =
      ∑ s : Fin k → I, (∏ a, z (s a)) • iteratedFDeriv ℂ k f 0 fun a ↦ Pi.single (s a) 1 := by
    have hz : (fun _ : Fin k ↦ z) = fun _ ↦ ∑ i, z i • (Pi.single i (1 : ℂ) : I → ℂ) := by
      funext a j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hz, ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [ContinuousMultilinearMap.map_smul_univ]
  rw [h2, nsmul_eq_mul] at h1
  rw [← inv_mul_cancel_left₀ hk (p k fun _ ↦ z), h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp only [smul_eq_mul]
  ring

theorem diag_eq_zero_of_isBigO {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (N : ℕ) {f : E → ℂ}
    {p : FormalMultilinearSeries ℂ E ℂ} (hp : HasFPowerSeriesAt f p 0)
    (hf : f =O[𝓝 0] fun z : E ↦ ‖z‖ ^ (N + 1)) (k : ℕ) : k ≤ N → ∀ y, (p k fun _ ↦ y) = 0 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have h1 := hp.isBigO_sub_partialSum_pow (k + 1)
    have hs : ∀ y, p.partialSum (k + 1) y = p k fun _ ↦ y := by
      intro y
      rw [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
        Finset.sum_eq_zero fun j hj ↦ ih j (Finset.mem_range.1 hj)
          (le_trans (Finset.mem_range.1 hj).le hk) y, zero_add]
    have h2 : (fun z : E ↦ ‖z‖ ^ (N + 1)) =O[𝓝 0] fun z : E ↦ ‖z‖ ^ (k + 1) := by
      refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [Metric.closedBall_mem_nhds (0 : E) one_pos] with z hz
      rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_of_le_one (norm_nonneg _) (by simpa using hz) (by omega)
    have h3 : (fun y : E ↦ p k fun _ ↦ y) =O[𝓝 0] fun z : E ↦ ‖z‖ ^ (k + 1) := by
      refine ((hf.trans h2).sub h1).congr_left fun y ↦ ?_
      simp [hs]
    exact h3.continuousMultilinearMap_apply_eq_zero

theorem iteratedFDeriv_eq_zero_of_isBigO {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (N : ℕ)
    {f : E → ℂ} (ha : AnalyticAt ℂ f 0) (hf : f =O[𝓝 0] fun z : E ↦ ‖z‖ ^ (N + 1)) {k : ℕ} (hk : k ≤ N)
    (v : Fin k → E) : iteratedFDeriv ℂ k f 0 v = 0 := by
  obtain ⟨p, hp⟩ := ha
  have h := diag_eq_zero_of_isBigO N hp hf k hk
  obtain ⟨r, hr⟩ := hp
  rw [hr.iteratedFDeriv_eq_sum_of_completeSpace, ← (p k).iteratedFDeriv_comp_diagonal 0 v]
  simp [h]

theorem taylor_remainder_and_flat : ∀ {I : Type} [Fintype I] [DecidableEq I] (N : ℕ) (f : (I → ℂ) → ℂ), AnalyticAt ℂ f 0 → ((fun z ↦ f z - GlobalTheory.PeriodFamily.taylor N z f) =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1)) ∧ ((f =O[𝓝 0] fun z : I → ℂ ↦ ‖z‖ ^ (N + 1)) → ∀ {D : Type} [CommRing D] [Algebra ℂ D] (t : I → D), GlobalTheory.PeriodFamily.taylor N t f = 0) := by
  intro I _ _ N f ha
  refine ⟨?_, fun hf D _ _ t ↦ ?_⟩
  · obtain ⟨p, hp⟩ := ha
    refine (hp.isBigO_sub_partialSum_pow (N + 1)).congr_left fun z ↦ ?_
    rw [taylor_eq_partialSum N hp, zero_add]
  · unfold taylor
    refine Finset.sum_eq_zero fun k hk ↦ Finset.sum_eq_zero fun s _ ↦ ?_
    rw [iteratedFDeriv_eq_zero_of_isBigO N ha hf (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)), mul_zero,
      zero_smul]

end GlobalTheory.PeriodFamily
