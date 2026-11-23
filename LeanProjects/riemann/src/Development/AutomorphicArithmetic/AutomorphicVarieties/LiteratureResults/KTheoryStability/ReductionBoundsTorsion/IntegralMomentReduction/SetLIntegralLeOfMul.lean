import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.AbsLeA
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.UnitaryConeEstimates.ContVal

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal

namespace PositivityTheory.KB.TwSMInt2

open PositivityTheory.KB.MomentRationality.Cz.Pk

variable {ι : Type} {N : ℕ}

theorem setLIntegral_le_of_mul {α : Type*} [MeasurableSpace α] (μ : Measure α) {X : Set α} (hX : MeasurableSet X)
    (f : α → ℝ≥0∞) (D : ℝ≥0∞) (h : ∀ x ∈ X, f x * μ X ≤ D) : ∫⁻ x in X, f x ∂μ ≤ D := by
  rcases eq_or_ne (μ X) 0 with h0 | h0
  · simp [Measure.restrict_eq_zero.mpr h0]
  rcases eq_or_ne D ⊤ with hD | hD
  · simp [hD]
  rcases eq_or_ne (μ X) ⊤ with htop | htop
  · have hz : ∀ x ∈ X, f x = 0 := by
      intro x hx
      by_contra hne
      have := h x hx
      rw [htop, ENNReal.mul_top hne] at this
      exact hD (top_le_iff.mp this)
    calc ∫⁻ x in X, f x ∂μ = ∫⁻ _ in X, 0 ∂μ := setLIntegral_congr_fun hX hz
      _ = 0 := lintegral_zero
      _ ≤ D := bot_le
  · have hle : ∀ x ∈ X, f x ≤ D / μ X := fun x hx =>
      (ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl htop)).mpr (h x hx)
    calc ∫⁻ x in X, f x ∂μ ≤ ∫⁻ _ in X, D / μ X ∂μ := setLIntegral_mono' hX hle
      _ = D / μ X * μ X := setLIntegral_const X _
      _ = D := ENNReal.div_mul_cancel h0 htop

theorem main_of_pack (hN : 2 ≤ N) [Fintype ι] [Nonempty ι] [MeasurableSpace (G ι N)] [BorelSpace (G ι N)]
    (μ : Measure (G ι N)) [μ.IsHaarMeasure] {P : Set (G ι N)} (hPc : IsCompact P)
    (T B : ℝ) (hpk : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (m : Fin N → ℤ) (s0 : Fin N → ℝ), ∑ i, s0 i = 0 → Cone T s0 →
      (∀ i, (m i : ℝ) ≤ s0 i ∧ s0 i ≤ m i + 1) →
      μ (Xb P T m) ≤ K * ENNReal.ofReal (Real.exp (-2 * Phi s0))) (hB : B < 2 * ((N : ℝ) - 1)) (C : ℝ≥0∞) (hC : C ≠ ⊤) (f : G ι N → ℝ≥0∞)
    (hf : ∀ p ∈ P, ∀ (s : Fin N → ℝ) (hs : ∑ i, s i = 0), Cone T s → ∀ k ∈ KS,
      f (p * dg s hs * k) ≤ C * ENNReal.ofReal (Real.exp (B * W s))) :
    ∫⁻ x in Sg P T, f x ∂μ < ⊤ := by
  obtain ⟨K, hK, hμ⟩ := hpk
  obtain ⟨c, ε, hε, hexp⟩ := ineq hN T B hB
  set D : (Fin N → ℤ) → ℝ≥0∞ := fun m => C * K * (ENNReal.ofReal (Real.exp (c + ε * N)) *
    ENNReal.ofReal (Real.exp (-(ε * ∑ i, |((m i : ℤ) : ℝ)|)))) with hD
  have hcov : Sg P T ⊆ ⋃ m, Xb P T m := by
    rintro x ⟨p, hp, s, hs, hcone, k, hk, rfl⟩
    refine Set.mem_iUnion.mpr ⟨fun i => ⌊s i⌋, p, hp, s, hs, hcone, fun i => ⟨Int.floor_le _, (Int.lt_floor_add_one _).le⟩, k, hk, rfl⟩
  have hpiece : ∀ m, ∫⁻ x in Xb P T m, f x ∂μ ≤ D m := by
    intro m
    refine setLIntegral_le_of_mul μ (cpt_X hPc T m).measurableSet f (D m) ?_
    rintro x ⟨p, hp, s, hs, hcone, hb, k, hk, rfl⟩
    have h1 := hf p hp s hs hcone k hk
    have h2 := hμ m s hs hcone hb
    have habs : ∑ i, |((m i : ℤ) : ℝ)| ≤ ∑ i, |s i| + N := by
      have : ∀ i, |((m i : ℤ) : ℝ)| ≤ |s i| + 1 := by
        intro i
        have := (hb i).1
        have := (hb i).2
        calc |((m i : ℤ) : ℝ)| = |s i - (s i - m i)| := by ring_nf
          _ ≤ |s i| + |s i - m i| := abs_sub _ _
          _ ≤ |s i| + 1 := by
            gcongr
            rw [abs_le]
            constructor <;> linarith
      calc ∑ i, |((m i : ℤ) : ℝ)| ≤ ∑ i, (|s i| + 1) := Finset.sum_le_sum fun i _ => this i
        _ = ∑ i, |s i| + N := by simp [Finset.sum_add_distrib]
    have hreal : Real.exp (B * W s) * Real.exp (-2 * Phi s) ≤
        Real.exp (c + ε * N) * Real.exp (-(ε * ∑ i, |((m i : ℤ) : ℝ)|)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := hexp s hs hcone
      nlinarith
    calc f (p * dg s hs * k) * μ (Xb P T m)
        ≤ (C * ENNReal.ofReal (Real.exp (B * W s))) * (K * ENNReal.ofReal (Real.exp (-2 * Phi s))) :=
          mul_le_mul' h1 h2
      _ = C * K * ENNReal.ofReal (Real.exp (B * W s) * Real.exp (-2 * Phi s)) := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
          ring
      _ ≤ C * K * ENNReal.ofReal (Real.exp (c + ε * N) * Real.exp (-(ε * ∑ i, |((m i : ℤ) : ℝ)|))) := by
          gcongr
      _ = D m := by
          rw [hD, ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hsum : ∑' m, D m ≠ ⊤ := by
    simp only [hD]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hC hK)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (summ ε hε))
  calc ∫⁻ x in Sg P T, f x ∂μ ≤ ∫⁻ x in ⋃ m, Xb P T m, f x ∂μ := lintegral_mono_set hcov
    _ ≤ ∑' m, ∫⁻ x in Xb P T m, f x ∂μ := lintegral_iUnion_le _ _
    _ ≤ ∑' m, D m := ENNReal.tsum_le_tsum hpiece
    _ < ⊤ := lt_top_iff_ne_top.mpr hsum

end PositivityTheory.KB.TwSMInt2

end
