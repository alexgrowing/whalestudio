import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogisticFactorMem
open GlobalTheory Matrix Filter Topology Set GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.InterpCurv
open scoped ComplexOrder ContDiff

theorem GlobalTheory.cutoff_deriv_bounds : ∀ χ : ℝ → ℝ, IsCutoff χ → ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, 0 < y →
    |deriv χ y| ≤ M ∧ |deriv (deriv χ) y| ≤ M ∧ deriv χ y ^ 2 ≤ M * χ y := by
  intro χ h
  have hs : ContDiffOn ℝ ∞ χ (Ioi 0) := h.smooth.mono Ioi_subset_Ici_self
  have hq : ContDiffOn ℝ ∞ (fun y => √(χ y)) (Ioi 0) := h.smooth_sqrt.mono Ioi_subset_Ici_self
  have h11 : (1 : WithTop ℕ∞) + 1 ≤ ∞ := by norm_cast
  have h1 : (1 : WithTop ℕ∞) ≤ ∞ := by norm_cast
  have hd1 : ContDiffOn ℝ 1 (deriv χ) (Ioi 0) := hs.deriv_of_isOpen isOpen_Ioi h11
  have c1 : ContinuousOn (deriv χ) (Ioi 0) := hs.continuousOn_deriv_of_isOpen isOpen_Ioi h1
  have c2 : ContinuousOn (deriv (deriv χ)) (Ioi 0) := hd1.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  have c3 : ContinuousOn (deriv (fun y => √(χ y))) (Ioi 0) := hq.continuousOn_deriv_of_isOpen isOpen_Ioi h1
  have hK : Icc (2:ℝ) 3 ⊆ Ioi 0 := fun y hy => by simp only [mem_Ioi]; linarith [hy.1]
  obtain ⟨B1, hB1⟩ := isCompact_Icc.exists_bound_of_continuousOn (c1.mono hK)
  obtain ⟨B2, hB2⟩ := isCompact_Icc.exists_bound_of_continuousOn (c2.mono hK)
  obtain ⟨B3, hB3⟩ := isCompact_Icc.exists_bound_of_continuousOn (c3.mono hK)

  have zero_out : ∀ y, 0 < y → (y < 2 ∨ 3 < y) → deriv χ y = 0 ∧ deriv (deriv χ) y = 0 := by
    intro y hy hyo
    rcases hyo with hyo | hyo
    · have hloc : deriv χ =ᶠ[𝓝 y] fun _ => (0:ℝ) := by
        filter_upwards [Ioo_mem_nhds hy hyo] with z hz
        have hev : χ =ᶠ[𝓝 z] fun _ => (1:ℝ) := by
          filter_upwards [Ioo_mem_nhds hz.1 hz.2] with w hw
          exact h.eq_one w ⟨hw.1.le, hw.2.le⟩
        rw [hev.deriv_eq]; simp
      refine ⟨hloc.eq_of_nhds, ?_⟩
      rw [hloc.deriv_eq]; simp
    · have hloc : deriv χ =ᶠ[𝓝 y] fun _ => (0:ℝ) := by
        filter_upwards [Ioi_mem_nhds hyo] with z hz
        have hev : χ =ᶠ[𝓝 z] fun _ => (0:ℝ) := by
          filter_upwards [Ioi_mem_nhds (show (3:ℝ) < z from hz)] with w hw
          exact h.eq_zero w hw.le
        rw [hev.deriv_eq]; simp
      refine ⟨hloc.eq_of_nhds, ?_⟩
      rw [hloc.deriv_eq]; simp
  refine ⟨max (max B1 B2) (max (4 * B3 ^ 2) 0), le_max_of_le_right (le_max_right _ _), ?_⟩
  intro y hy
  have hχ0 : 0 ≤ χ y := (h.mem y hy.le).1
  by_cases hin : y ∈ Icc (2:ℝ) 3
  · have e1 := hB1 y hin
    have e2 := hB2 y hin
    have e3 := hB3 y hin
    rw [Real.norm_eq_abs] at e1 e2 e3
    refine ⟨?_, ?_, ?_⟩
    · exact e1.trans (le_max_of_le_left (le_max_left _ _))
    · exact e2.trans (le_max_of_le_left (le_max_right _ _))
    ·
      have hev : χ =ᶠ[𝓝 y] fun z => (√(χ z)) ^ 2 := by
        filter_upwards [Ioi_mem_nhds hy] with z hz
        rw [Real.sq_sqrt (h.mem z (le_of_lt hz)).1]
      have hdq : DifferentiableAt ℝ (fun z => √(χ z)) y :=
        (hq.contDiffAt (Ioi_mem_nhds hy)).differentiableAt (by simp)
      have hder : deriv χ y = 2 * √(χ y) * deriv (fun z => √(χ z)) y := by
        rw [hev.deriv_eq]
        have := (hdq.hasDerivAt.pow 2).deriv
        rw [show (fun z => √(χ z) ^ 2) = (fun z => √(χ z)) ^ 2 from rfl, this]; push_cast; ring
      rw [hder]
      have : (2 * √(χ y) * deriv (fun z => √(χ z)) y) ^ 2
          = 4 * (deriv (fun z => √(χ z)) y) ^ 2 * χ y := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hχ0]; ring
      rw [this]
      apply mul_le_mul_of_nonneg_right _ hχ0
      have hsq : (deriv (fun z => √(χ z)) y) ^ 2 ≤ B3 ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) e3 2
      exact (by nlinarith : 4 * (deriv (fun z => √(χ z)) y) ^ 2 ≤ 4 * B3 ^ 2).trans
        (le_max_of_le_right (le_max_left _ _))
  · have hyo : y < 2 ∨ 3 < y := by
      by_contra hc; push_neg at hc; exact hin ⟨hc.1, hc.2⟩
    obtain ⟨z1, z2⟩ := zero_out y hy hyo
    have hM0 : 0 ≤ max (max B1 B2) (max (4 * B3 ^ 2) 0) := le_max_of_le_right (le_max_right _ _)
    refine ⟨by rw [z1]; simpa using hM0, by rw [z2]; simpa using hM0, ?_⟩
    rw [z1]; simpa using mul_nonneg hM0 hχ0
