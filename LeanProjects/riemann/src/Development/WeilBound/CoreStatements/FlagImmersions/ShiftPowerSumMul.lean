import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
import Development.WeilBound.CoreStatements.FlagImmersions.FlagDegreeLinearFunctionals
import Development.WeilBound.CoreStatements.FlagImmersions.DegFlPowerSumMul
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem pa_pderiv_pk {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (τ σ : Ψ) (i : Fin N) (k : ℕ) :
    pderiv (σ, i) (pk τ k : RP Ψ N) = if σ = τ then C (k : ℝ) * X (τ, i) ^ (k - 1) else 0 := by
  classical
  unfold pk
  rw [map_sum]
  by_cases h : σ = τ
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single i]
    · rw [Derivation.leibniz_pow, pderiv_X_self, smul_eq_mul, mul_one, nsmul_eq_mul,
        ← map_natCast C]
    · intro b _ hb
      rw [Derivation.leibniz_pow, pderiv_X_of_ne (by simp [hb]), smul_zero, smul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Derivation.leibniz_pow, pderiv_X_of_ne (by simp [Ne.symm h]), smul_zero, smul_zero]

theorem pa_degFl_sum_pderiv {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (s : Finset (Fin N)) (τ σ : Ψ) (k : ℕ)
    (Q : RP Ψ N) (hk : 1 ≤ k) :
    degFl (∑ i ∈ s, pderiv (σ, i) (pk τ k * Q)) =
      if σ = τ then k * degFl ((∑ i ∈ s, X (τ, i) ^ (k - 1)) * Q) else 0 := by
  have hlin : ∀ F : RP Ψ N, degFl F = pa_degFlL Ψ N F := fun F => (pa_degFlL_apply F).symm
  have hd : ∀ i, pderiv (σ, i) (pk τ k * Q) =
      pderiv (σ, i) (pk τ k : RP Ψ N) * Q + pk τ k * pderiv (σ, i) Q := by
    intro i
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  simp_rw [hd, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hlin, map_add, ← hlin, ← hlin, degFl_power_sum_mul Ψ N τ k _ hk, add_zero]
  by_cases h : σ = τ
  · subst h
    simp only [pa_pderiv_pk, if_true]
    have hsum : (∑ i ∈ s, C (k : ℝ) * X (σ, i) ^ (k - 1) * Q : RP Ψ N) =
        (k : ℝ) • ((∑ i ∈ s, X (σ, i) ^ (k - 1)) * Q) := by
      rw [MvPolynomial.smul_eq_C_mul, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hsum, hlin, map_smul, ← hlin, smul_eq_mul]
  · simp only [pa_pderiv_pk, if_neg h, zero_mul, Finset.sum_const_zero]
    rw [hlin, map_zero]

theorem shift_power_sum_mul : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ σ : Ψ) (k : ℕ) (Q : RP Ψ N), 1 ≤ k → Sh j σ (pk τ k * Q) = (if σ = τ then k * degFl (pkLow j τ (k - 1) * Q) else 0) ∧ Tot σ (pk τ k * Q) = (if σ = τ ∧ k = 1 then N * degFl Q else 0) := by
  intro Ψ _ _ N j τ σ k Q hk
  constructor
  · rw [Sh, pa_degFl_sum_pderiv _ τ σ k Q hk]
    rfl
  · rw [Tot, pa_degFl_sum_pderiv _ τ σ k Q hk]
    by_cases h : σ = τ
    · rw [if_pos h]
      rcases Nat.lt_or_ge 1 k with hk2 | hk1
      · have h0 : degFl ((∑ i : Fin N, X (τ, i) ^ (k - 1)) * Q : RP Ψ N) = 0 :=
          degFl_power_sum_mul Ψ N τ (k - 1) Q (by omega)
        rw [h0, mul_zero, if_neg (by omega)]
      · have hk' : k = 1 := le_antisymm hk1 hk
        subst hk'
        rw [if_pos ⟨h, rfl⟩]
        have hsum : ((∑ i : Fin N, X (τ, i) ^ (1 - 1)) * Q : RP Ψ N) = (N : ℝ) • Q := by
          simp [MvPolynomial.smul_eq_C_mul]
        rw [hsum, ← pa_degFlL_apply, map_smul, pa_degFlL_apply, smul_eq_mul]
        push_cast
        ring
    · rw [if_neg h, if_neg (fun h' => h h'.1)]

end RootFieldNumerics
