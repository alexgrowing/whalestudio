import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl

open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory.FlagPoly

theorem pderiv_pSum_eq {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (τ σ : ι) (i : Fin N) (k : ℕ) :
    pderiv (τ, i) (pSum σ k : Pol ι N) =
      if σ = τ then C (k : ℝ) * X (τ, i) ^ (k - 1) else 0 := by
  unfold pSum
  rw [map_sum]
  simp only [Derivation.leibniz_pow, pderiv_X, Pi.single_apply, Prod.mk.injEq]
  by_cases h : σ = τ
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  · simp [h]

theorem degFl_pderiv_powerComb {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}
    (Q : ι → ℕ → Pol ι N) (τ : ι) (s : Finset (Fin N)) :
    degFl ι N (∑ i ∈ s, pderiv (τ, i) (∑ σ : ι, ∑ k ∈ Finset.Icc 1 N, pSum σ k * Q σ k)) =
      ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * degFl ι N ((∑ i ∈ s, X (τ, i) ^ (k - 1)) * Q τ k) := by
  have h1 : ∀ i : Fin N, degFl ι N (pderiv (τ, i) (∑ σ : ι, ∑ k ∈ Finset.Icc 1 N, pSum σ k * Q σ k)) =
      ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * degFl ι N (X (τ, i) ^ (k - 1) * Q τ k) := by
    intro i
    rw [map_sum, PPowSum.degFl_sum, Finset.sum_eq_single τ]
    · rw [map_sum, PPowSum.degFl_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hz : degFl ι N (pSum τ k * pderiv (τ, i) (Q τ k)) = 0 :=
        PPowSum.degFlPowerSum ι N τ k _ hk1
      rw [pderiv_mul, PPowSum.degFl_add, hz, add_zero, pderiv_pSum_eq, if_pos rfl, mul_assoc,
        PPowSum.degFl_C_mul]
    · intro σ _ hσ
      rw [map_sum, PPowSum.degFl_sum]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hz : degFl ι N (pSum σ k * pderiv (τ, i) (Q σ k)) = 0 :=
        PPowSum.degFlPowerSum ι N σ k _ hk1
      rw [pderiv_mul, PPowSum.degFl_add, hz, add_zero, pderiv_pSum_eq, if_neg hσ, zero_mul,
        PPowSum.degFl_zero]
    · simp
  rw [PPowSum.degFl_sum, Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul, PPowSum.degFl_sum, Finset.mul_sum]

theorem shF_totF_powerComb : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (j : ℕ) (Q : ι → ℕ → Pol ι N) (τ : ι), 1 ≤ N → shF j τ (∑ σ : ι, ∑ k ∈ Finset.Icc 1 N, pSum σ k * Q σ k) = ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * degFl ι N (pLow j τ (k - 1) * Q τ k) ∧ totF τ (∑ σ : ι, ∑ k ∈ Finset.Icc 1 N, pSum σ k * Q σ k) = (N : ℝ) * degFl ι N (Q τ 1) := by
  intro ι _ _ N j Q τ hN
  refine ⟨degFl_pderiv_powerComb Q τ _, ?_⟩
  unfold totF
  rw [degFl_pderiv_powerComb Q τ Finset.univ, Finset.sum_eq_single 1]
  · have : (∑ i : Fin N, X (τ, i) ^ (1 - 1) : Pol ι N) = C (N : ℝ) := by simp
    rw [this, PPowSum.degFl_C_mul]
    simp
  · intro k hk hk1
    have hk2 : 1 ≤ k - 1 := by have := (Finset.mem_Icc.mp hk).1; omega
    rw [PPowSum.degFlPowerSum ι N τ (k - 1) _ hk2, mul_zero]
  · intro h
    exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩) h

end GlobalTheory.FlagPoly
