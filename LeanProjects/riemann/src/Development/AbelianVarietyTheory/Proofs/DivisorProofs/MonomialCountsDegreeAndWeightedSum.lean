import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.HSShort

theorem nat_card_monoDeg_fin (D a : ℕ) (hD : 1 ≤ D) :
    Nat.card (MonoDeg (Fin D) a) = (a + D - 1).choose (D - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  classical
  rw [Nat.card_eq_fintype_card, MonoDeg.card_eq_card_finsuppAntidiag,
    Finset.card_finsuppAntidiag_nat_eq_choose]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [show a + (d + 1) - 1 = a + d by omega, show d + 1 + a - 1 = a + d by omega,
    show d + 1 - 1 = d by omega]
  exact Nat.choose_symm_add

theorem sum_range_choose_mul_sub (d n : ℕ) :
    ∑ a ∈ Finset.range n, (a + d).choose d * (n - a) = (n + d + 1).choose (d + 2) := by
  induction n with
  | zero => simp [Nat.choose_eq_zero_of_lt]
  | succ n ih =>
    have h1 : ∑ a ∈ Finset.range n, (a + d).choose d * (n + 1 - a) =
        ∑ a ∈ Finset.range n, (a + d).choose d * (n - a) +
          ∑ a ∈ Finset.range n, (a + d).choose d := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      have : a < n := Finset.mem_range.mp ha
      rw [show n + 1 - a = (n - a) + 1 by omega, Nat.mul_succ]
    rw [Finset.sum_range_succ, h1, ih, show n + 1 - n = 1 by omega, mul_one, add_assoc,
      ← Finset.sum_range_succ, Nat.sum_range_add_choose,
      show n + 1 + d + 1 = (n + d + 1) + 1 by omega, Nat.choose_succ_succ' (n + d + 1) (d + 1)]
    ring_nf

theorem monomial_counts : ∀ D T : ℕ, 1 ≤ D → D + 1 ≤ T →
    (∀ a : ℕ, Nat.card (MonoDeg (Fin D) a) = (a + D - 1).choose (D - 1)) ∧
    Nat.card (Σ a : Fin (T - D), MonoDeg (Fin D) a) = (T - 1).choose D ∧
    (D + 1) * ∑ a ∈ Finset.range (T - D), (a + D - 1).choose (D - 1) * (T - a) =
      (T - 1).choose D * (T + D * (D + 1)) := by
  intro D T hD hT
  have h1 := fun a => nat_card_monoDeg_fin D a hD
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, T = d + 2 + m := ⟨T - (d + 2), by omega⟩
  have hTD : d + 2 + m - (d + 1) = m + 1 := by omega
  have hT1 : d + 2 + m - 1 = m + d + 1 := by omega
  have hsub : ∀ a, a + (d + 1) - 1 = a + d := fun a => by omega
  simp only [hsub, show d + 1 - 1 = d by omega] at h1 ⊢
  have hsum : ∑ a ∈ Finset.range (m + 1), (a + d).choose d = (m + d + 1).choose (d + 1) :=
    Nat.sum_range_add_choose m d
  refine ⟨h1, ?_, ?_⟩
  · rw [Nat.card_sigma, hT1]
    simp only [h1]
    rw [← hsum, hTD, Finset.sum_range (fun a => (a + d).choose d)]
  · rw [hTD, hT1]
    have hw : ∑ a ∈ Finset.range (m + 1), (a + d).choose d * (d + 2 + m - a) =
        ∑ a ∈ Finset.range (m + 1), (a + d).choose d * (m + 1 - a) +
          (d + 1) * ∑ a ∈ Finset.range (m + 1), (a + d).choose d := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      have : a < m + 1 := Finset.mem_range.mp ha
      rw [show d + 2 + m - a = (m + 1 - a) + (d + 1) by omega]
      ring
    rw [hw, sum_range_choose_mul_sub, hsum]
    have key := Nat.add_one_mul_choose_eq (m + d + 1) (d + 1)
    rw [show m + 1 + d + 1 = m + d + 1 + 1 by omega]
    nlinarith [key]

end GlobalTheory.HSShort
