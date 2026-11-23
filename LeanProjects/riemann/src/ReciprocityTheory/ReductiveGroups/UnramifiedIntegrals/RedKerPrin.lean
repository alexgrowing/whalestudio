import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedKerPoly
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem sqD_eq (d r : ℕ) :
    (r : ℂ) + redSqD d = (((r : ℤ) - 1 : ℤ) : ℂ) + ((2 : ℤ) : ℂ) * omegaK d := by
  unfold redSqD
  push_cast
  ring

theorem sqD_normSq (d r : ℕ) : Complex.normSq ((r : ℂ) + redSqD d) = ((r ^ 2 + d : ℕ) : ℝ) := by
  unfold redSqD omegaK
  have h : (r : ℂ) + (2 * ((1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2) - 1)
      = ⟨(r : ℝ), Real.sqrt d⟩ := by
    apply Complex.ext <;> simp <;> ring
  rw [h, Complex.normSq_mk, Real.mul_self_sqrt (Nat.cast_nonneg d)]
  push_cast
  ring

theorem sqD_mulStable (d : ℕ) (L : PeriodPair) (hCM : HasCMBy d L) (r : ℕ) : MulStable L ((r : ℂ) + redSqD d) := by
  rw [sqD_eq]
  exact (hasCMByStable d L hCM _ _).1

theorem kerProdAt_of_norm (d : ℕ) (L : PeriodPair) (hCM : HasCMBy d L) (l e r : ℕ) (hodd : Odd (r ^ 2 + d))
    (hl : ¬ l ∣ r ^ 2 + d) (he : ¬ e ∣ r ^ 2 + d) (he' : ¬ e ∣ (r ^ 2 + d - 1) / 2) :
    KerProdAt d L l e := by
  have hN := sqD_normSq d r
  have hs := sqD_mulStable d L hCM r
  have hα : (r : ℂ) + redSqD d ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hN
    have h1 : r ^ 2 + d = 0 := by exact_mod_cast hN.symm
    rw [h1] at hodd
    exact absurd hodd (by decide)
  obtain ⟨T, hT⟩ := halfReps_exist L _ hα hs _ hN hodd
  have hcard : 2 * T.card + 1 = r ^ 2 + d := by
    have h1 := hT.card hα hs
    rw [hN] at h1
    exact_mod_cast h1
  have hcard' : T.card = (r ^ 2 + d - 1) / 2 := by omega
  refine ⟨r ^ 2 + d, T, hl, he, by rw [hcard']; exact he', ?_, ?_⟩
  · intro z hz
    exact ⟨hT.notMem hz, ker_norm hs hN (hT.1 z hz).1⟩
  · intro k h2 h3 hk
    have hαk : (r : ℂ) + redSqD d ∈ k := by
      unfold redSqD
      exact k.add_mem (natCast_mem k r)
        (k.sub_mem (k.mul_mem (by exact_mod_cast natCast_mem k 2) hk) k.one_mem)
    have h4 := prod_mem_of_rootPoly k (xsOf L T) (kerPoly_mem L _ T hα hs hT k h2 h3 hαk)
    unfold xsOf at h4
    rwa [Finset.prod_image (fun a ha b hb hab => hT.injOn ha hb hab)] at h4

theorem kerProd_prin (d : ℕ) (L : PeriodPair) (hd4 : d % 4 = 3) (hCM : HasCMBy d L) (l : ℕ) (hl : l.Prime)
    (h5 : 5 ≤ l) (hld : ¬ l ∣ d) (e : ℕ) (he : e = 2 ∨ e = 3 ∧ ¬ 3 ∣ d) : KerProdAt d L l e := by
  rcases he with rfl | ⟨rfl, h3⟩
  · refine kerProdAt_of_norm d L hCM l 2 0 ?_ ?_ ?_ ?_
    · rw [Nat.odd_iff]; omega
    · simpa using hld
    · omega
    · omega
  · have hmod : d % 3 = 1 ∨ d % 3 = 2 := by omega
    rcases hmod with h1 | h2
    · by_cases hl2 : l ∣ 2 ^ 2 + d
      · have hl4 : ¬ l ∣ 4 ^ 2 + d := by
          intro h
          have h12 : l ∣ 12 := by
            have := Nat.dvd_sub h hl2
            have e12 : 4 ^ 2 + d - (2 ^ 2 + d) = 12 := by omega
            rwa [e12] at this
          have hle : l ≤ 12 := Nat.le_of_dvd (by norm_num) h12
          interval_cases l <;> omega
        refine kerProdAt_of_norm d L hCM l 3 4 ?_ hl4 ?_ ?_
        · rw [Nat.odd_iff]; omega
        · omega
        · omega
      · refine kerProdAt_of_norm d L hCM l 3 2 ?_ hl2 ?_ ?_
        · rw [Nat.odd_iff]; omega
        · omega
        · omega
    · refine kerProdAt_of_norm d L hCM l 3 0 ?_ ?_ ?_ ?_
      · rw [Nat.odd_iff]; omega
      · simpa using hld
      · omega
      · omega

end ReciprocityTheory.ChartRestriction.L1
