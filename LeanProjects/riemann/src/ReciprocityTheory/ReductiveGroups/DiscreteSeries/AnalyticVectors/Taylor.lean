import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.IteratedDerivOrbit

noncomputable section

open Finset Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem iteratedDeriv_dual_orbit (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (φ : H →L[ℝ] ℝ) (m : ℕ) : ∀ w : D,
    iteratedDeriv m (fun s : ℝ => φ (σ (NormedSpace.exp ((s : ℂ) • X)) (w : H))) =
      fun s : ℝ => φ (σ (NormedSpace.exp ((s : ℂ) • X)) ((((actM E X) ^ m) w : D) : H)) := by
  induction m with
  | zero => intro w; simp
  | succ m ih =>
    intro w
    rw [iteratedDeriv_succ']
    have hd : deriv (fun s : ℝ => φ (σ (NormedSpace.exp ((s : ℂ) • X)) (w : H))) =
        fun s : ℝ => φ (σ (NormedSpace.exp ((s : ℂ) • X)) ((actM E X w : D) : H)) := by
      funext s
      exact (φ.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_orbit hσ hD hX w s)).deriv
    rw [hd, ih (actM E X w), pow_succ, Module.End.mul_apply]

theorem contDiff_dual_orbit (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (φ : H →L[ℝ] ℝ) (w : D) (N : ℕ) :
    ContDiff ℝ N (fun s : ℝ => φ (σ (NormedSpace.exp ((s : ℂ) • X)) (w : H))) :=
  φ.contDiff.comp (contDiff_orbit hσ hD hX w N)

theorem norm_orbit_sub_partial_le (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : D) (a : ℕ → ℝ)
    (ha : ∀ m, ‖((((actM E X) ^ m) v : D) : H)‖ ≤ a m) (t₀ t : ℝ) (N : ℕ) :
    ‖σ (NormedSpace.exp ((t : ℂ) • X)) (v : H) - ∑ m ∈ range (N + 1),
        (((t - t₀) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) •
          σ (NormedSpace.exp ((t₀ : ℂ) • X)) ((((actM E X) ^ m) v : D) : H)‖ ≤
      a (N + 1) * |t - t₀| ^ (N + 1) / ((N + 1).factorial : ℝ) := by
  rcases eq_or_ne t₀ t with rfl | htt
  · have h0 : σ (NormedSpace.exp ((t₀ : ℂ) • X)) (v : H) - ∑ m ∈ range (N + 1),
        (((t₀ - t₀) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) •
          σ (NormedSpace.exp ((t₀ : ℂ) • X)) ((((actM E X) ^ m) v : D) : H) = 0 := by
      rw [Finset.sum_range_succ']
      simp
    rw [h0, norm_zero]
    simp
  set R := σ (NormedSpace.exp ((t : ℂ) • X)) (v : H) - ∑ m ∈ range (N + 1),
        (((t - t₀) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) •
          σ (NormedSpace.exp ((t₀ : ℂ) • X)) ((((actM E X) ^ m) v : D) : H) with hR
  obtain ⟨φ, hφ1, hφR⟩ := exists_dual_vector'' ℝ R
  set g : ℝ → ℝ := fun s => φ (σ (NormedSpace.exp ((s : ℂ) • X)) (v : H)) with hg
  have hgd := iteratedDeriv_dual_orbit hσ hD hX φ
  have hu : UniqueDiffOn ℝ (Set.uIcc t₀ t) := uniqueDiffOn_uIcc htt
  have hwithin : ∀ k : ℕ, iteratedDerivWithin k g (Set.uIcc t₀ t) t₀ =
      φ (σ (NormedSpace.exp ((t₀ : ℂ) • X)) ((((actM E X) ^ k) v : D) : H)) := by
    intro k
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin,
      iteratedFDerivWithin_eq_iteratedFDeriv hu
        ((contDiff_dual_orbit hσ hD hX φ v k).contDiffAt) Set.left_mem_uIcc,
      ← iteratedDeriv_eq_iteratedFDeriv, hgd k v]
  have hf : ContDiffOn ℝ (N + 1) g (Set.uIcc t₀ t) := by
    have := contDiff_dual_orbit hσ hD hX φ v (N + 1)
    exact_mod_cast this.contDiffOn
  obtain ⟨x', -, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv htt hf
  have hφsum : φ R = g t - taylorWithinEval g N (Set.uIcc t₀ t) t₀ t := by
    rw [taylor_within_apply, hR, map_sub, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.coe_smul, φ.map_smul, hwithin k, smul_eq_mul, smul_eq_mul, div_eq_inv_mul]
  have hD1 : |iteratedDeriv (N + 1) g x'| ≤ a (N + 1) := by
    rw [hgd (N + 1) v]
    calc |φ (σ (NormedSpace.exp ((x' : ℂ) • X)) ((((actM E X) ^ (N + 1)) v : D) : H))|
        ≤ ‖φ‖ * ‖σ (NormedSpace.exp ((x' : ℂ) • X)) ((((actM E X) ^ (N + 1)) v : D) : H)‖ :=
          φ.le_opNorm _
      _ ≤ 1 * ‖((((actM E X) ^ (N + 1)) v : D) : H)‖ := by
          rw [norm_orbit_apply hσ hX]
          exact mul_le_mul_of_nonneg_right hφ1 (norm_nonneg _)
      _ ≤ a (N + 1) := by rw [one_mul]; exact ha _
  calc ‖R‖ = φ R := hφR.symm
    _ = iteratedDeriv (N + 1) g x' * (t - t₀) ^ (N + 1) / ((N + 1).factorial : ℝ) := by
        rw [hφsum, heq]
    _ ≤ |iteratedDeriv (N + 1) g x' * (t - t₀) ^ (N + 1) / ((N + 1).factorial : ℝ)| :=
        le_abs_self _
    _ = |iteratedDeriv (N + 1) g x'| * |t - t₀| ^ (N + 1) / ((N + 1).factorial : ℝ) := by
        rw [abs_div, abs_mul, abs_pow, Nat.abs_cast]
    _ ≤ a (N + 1) * |t - t₀| ^ (N + 1) / ((N + 1).factorial : ℝ) := by gcongr

theorem hasSum_orbit_of_bound (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : D) (a : ℕ → ℝ)
    (ha : ∀ m, ‖((((actM E X) ^ m) v : D) : H)‖ ≤ a m) (t₀ t : ℝ)
    (hs : Summable fun m : ℕ => a m * |t - t₀| ^ m / (m.factorial : ℝ)) :
    HasSum (fun m : ℕ => (((t - t₀) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) •
        σ (NormedSpace.exp ((t₀ : ℂ) • X)) ((((actM E X) ^ m) v : D) : H))
      (σ (NormedSpace.exp ((t : ℂ) • X)) (v : H)) := by
  have hterm : ∀ m, ‖(((t - t₀) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) •
      σ (NormedSpace.exp ((t₀ : ℂ) • X)) ((((actM E X) ^ m) v : D) : H)‖ ≤
        a m * |t - t₀| ^ m / (m.factorial : ℝ) := by
    intro m
    rw [norm_smul, norm_orbit_apply hσ hX, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow,
      Nat.abs_cast]
    have hp : 0 ≤ |t - t₀| ^ m / (m.factorial : ℝ) := by positivity
    have := mul_le_mul_of_nonneg_left (ha m) hp
    calc |t - t₀| ^ m / (m.factorial : ℝ) * ‖((((actM E X) ^ m) v : D) : H)‖
        ≤ |t - t₀| ^ m / (m.factorial : ℝ) * a m := this
      _ = a m * |t - t₀| ^ m / (m.factorial : ℝ) := by ring
  have hsumm := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hs
  rw [hasSum_iff_tendsto_nat_of_summable_norm hsumm, ← Filter.tendsto_add_atTop_iff_nat 1,
    tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_)
    ((Filter.tendsto_add_atTop_iff_nat 1).2 hs.tendsto_atTop_zero)
  rw [norm_sub_rev]
  exact norm_orbit_sub_partial_le hσ hD hX v a ha t₀ t N

end Rep

end ReciprocityTheory.ChartRestriction.DS
