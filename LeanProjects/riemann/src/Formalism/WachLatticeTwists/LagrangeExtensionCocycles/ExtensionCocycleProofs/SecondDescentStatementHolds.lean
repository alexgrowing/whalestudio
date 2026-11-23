import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

theorem second_descent_statement_holds : Stat2 := by
  intro ℓ _ hℓ2 A _ D D' _ _ _ _ S Mi hi s H h1 h2 h3 h4 h5 n hn
  set t := (s + (ℓ - 2)) / (ℓ - 1) with ht
  set c := cW ℓ H with hc
  have hℓ3 : 3 ≤ ℓ := by
    have := (Fact.out : ℓ.Prime).two_le
    omega
  have hts : s ≤ (ℓ - 1) * t := by
    have e1 := Nat.div_add_mod (s + (ℓ - 2)) (ℓ - 1)
    have e2 := Nat.mod_lt (s + (ℓ - 2)) (show 0 < ℓ - 1 by omega)
    rw [← ht] at e1
    generalize (ℓ - 1) * t = X at *
    omega
  have hℓR : (3 : ℝ) ≤ ℓ := by exact_mod_cast hℓ3
  have hℓ1 : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  have htsR : (s : ℝ) ≤ ((ℓ : ℝ) - 1) * t := by
    have := (Nat.cast_le (α := ℝ)).2 hts
    push_cast [hℓ1] at this
    rw [← hℓ1]
    exact_mod_cast hts
  have hkey : ∀ r ∈ S.R, (S.π ^ t * S.q ^ (c + 2 + t)) • r ∈ S.R' := by
    intro r hr
    rw [S.hq, add_pow, Finset.mul_sum, Finset.sum_smul]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [Finset.mem_range] at hi
    obtain ⟨U, hU⟩ : ∃ U, c + 2 + t - i = U := ⟨_, rfl⟩
    have hU' : c + 2 + t = i + U := by omega
    rw [hU]
    have e : S.π ^ t * (((ℓ : A) * S.w) ^ i * (S.π ^ (ℓ - 1)) ^ U * ((c + 2 + t).choose i : A)) =
        (S.w ^ i * ((c + 2 + t).choose i : A)) * ((ℓ : A) ^ i * S.π ^ ((ℓ - 1) * U + t)) := by
      rw [← pow_mul, pow_add, mul_pow]
      ring
    rw [e, mul_smul]
    refine Submodule.smul_mem _ _ ?_
    by_cases hj : s ≤ (ℓ - 1) * U + t
    · rw [← Nat.sub_add_cancel hj, pow_add, ← mul_assoc, mul_smul]
      exact Submodule.smul_mem _ _ (h4 r hr)
    · refine h5 i ((ℓ - 1) * U + t) ?_ r hr
      have hU0 : (0 : ℝ) ≤ U := by positivity
      have ht0 : (0 : ℝ) ≤ t := by positivity
      have hiR : (i : ℝ) = c + 2 + t - U := by
        have := congrArg (Nat.cast : ℕ → ℝ) hU'
        push_cast at this
        linarith
      have hpos : (0 : ℝ) < ((ℓ : ℝ) - 1) ^ 2 := by nlinarith
      have hsl : (s : ℝ) * ℓ ≤ ((ℓ : ℝ) - 1) * t * ℓ := mul_le_mul_of_nonneg_right htsR (by linarith)
      have hcU : (0 : ℝ) ≤ U * ((ℓ : ℝ) - 1) := mul_nonneg hU0 (by linarith)
      have hj' : (((ℓ - 1) * U + t : ℕ) : ℝ) = ((ℓ : ℝ) - 1) * U + t := by
        push_cast [hℓ1]
        ring
      rw [hj', hiR]
      have hdiv : ((s : ℝ) - (((ℓ : ℝ) - 1) * U + t)) * ℓ / ((ℓ : ℝ) - 1) ^ 2 ≤ 2 + t - U := by
        rw [div_le_iff₀ hpos]
        nlinarith
      linarith
  have hR1 := hkey _ (h1 n hn)
  have hR2 : (S.π ^ (Mi + hi + c + 2) * (S.π ^ t * S.q ^ (c + 2 + t))) • (S.q ^ Mi • S.φ n) ∈ S.R' := by
    rw [mul_smul]
    exact Submodule.smul_mem _ _ hR1
  have hsp := h2 _ hR2
  have hφ : S.φ (S.π ^ (Mi + hi + c + 2 + t) • n) = S.q ^ hi •
      ((S.π ^ (Mi + hi + c + 2) * (S.π ^ t * S.q ^ (c + 2 + t))) • (S.q ^ Mi • S.φ n)) := by
    rw [S.φ_smul, map_pow, S.φπ, smul_smul, smul_smul]
    congr 1
    ring
  apply h3 _ (Submodule.smul_mem _ _ hn)
  rw [hφ]
  exact hsp

end Formalism.RepresentationBoundsCohomology.N2
