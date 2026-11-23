import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem RootFieldNumerics.partial_sum_ordered_bounds : ∀ (N j : ℕ) (u : Fin N → ℝ), j ≤ N → 0 < N → (∀ a b : Fin N, a ≤ b → u b ≤ u a) → 0 ≤ (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u i) - j * ((∑ i, u i) / N) ∧ (∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u i) - j * ((∑ i, u i) / N) ≤ ∑ i, |u i| ∧ |∑ i, u i| ≤ ∑ i, |u i| := by
  intro N j u hj hN hu
  refine ⟨?_, ?_, Finset.abs_sum_le_sum_abs _ _⟩
  all_goals
    set A := Finset.univ.filter (fun i : Fin N => (i : ℕ) < j) with hA
    set B := Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j) with hB
    have hsplit : ∀ g : Fin N → ℝ, ∑ i, g i = ∑ i ∈ A, g i + ∑ i ∈ B, g i := fun g =>
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hjN : (j : ℝ) ≤ N := by exact_mod_cast hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  · have hcA : A.card = j := by
      rw [hA, Fin.card_filter_val_lt]; omega
    have hcB : (B.card : ℝ) = N - j := by
      have := hsplit (fun _ => 1)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hcA] at this
      linarith
    have key : ∑ i ∈ A, ∑ k ∈ B, u k ≤ ∑ i ∈ A, ∑ k ∈ B, u i := by
      refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun k hk => hu i k ?_
      rw [hA, Finset.mem_filter] at hi
      rw [hB, Finset.mem_filter] at hk
      rw [Fin.le_def]; omega
    simp only [Finset.sum_const, nsmul_eq_mul, hcA, hcB, ← Finset.mul_sum] at key
    rw [hsplit u, sub_nonneg, ← mul_div_assoc, div_le_iff₀ hNpos]
    nlinarith
  · rw [hsplit u, hsplit (fun i => |u i|)]
    have h1 := (abs_le.mp (Finset.abs_sum_le_sum_abs u A))
    have h2 := (abs_le.mp (Finset.abs_sum_le_sum_abs u B))
    have h3 : 0 ≤ ∑ i ∈ A, |u i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h4 : 0 ≤ ∑ i ∈ B, |u i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have ht0 : 0 ≤ (j : ℝ) / N := div_nonneg hj0 hNpos.le
    have ht1 : (j : ℝ) / N ≤ 1 := (div_le_one hNpos).mpr hjN
    have e : ∀ x : ℝ, (j : ℝ) * (x / N) = (j : ℝ) / N * x := fun x => by ring
    rw [e]
    generalize (j : ℝ) / N = t at *
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (sub_nonneg.mpr h1.2),
      mul_nonneg ht0 (sub_nonneg.mpr h2.1), mul_nonneg ht0 h3, mul_nonneg (sub_nonneg.mpr ht1) h4]
