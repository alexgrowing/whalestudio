import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem GlobalTheory.lipschitz_of_contraction_per_level : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (P : ℕ → Γ → Prop) (lam : Γ →* Multiplicative ℤ_[l]), (∀ m g, P (m + 1) g → P m g) → (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ g, P N g → ‖(lam g).toAdd‖ ≤ ε) → (∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ g, P (m + 1) g → ∃ h g' : Γ, P m h ∧ P (m + 2) g' ∧ g = h ^ l * g') → ∃ C : ℝ, ∀ (m : ℕ) (g : Γ), P m g → ‖(lam g).toAdd‖ ≤ C * ((l : ℝ)⁻¹) ^ m := by
  intro l hl Γ _ P lam hmono hsmall hdec
  obtain ⟨m₀, hdec⟩ := hdec
  have hmono' : ∀ a b g, P (a + b) g → P a g := by
    intro a b g h
    induction b with
    | zero => simpa using h
    | succ b ih => exact ih (hmono _ _ h)
  have hlpos : (0:ℝ) < l := by exact_mod_cast hl.out.pos
  have key : ∀ x y : Γ, ‖(lam (x ^ l * y)).toAdd‖ ≤
      max ((l:ℝ)⁻¹ * ‖(lam x).toAdd‖) ‖(lam y).toAdd‖ := by
    intro x y
    rw [map_mul, map_pow, toAdd_mul, toAdd_pow]
    refine (PadicInt.nonarchimedean _ _).trans (le_of_eq ?_)
    rw [nsmul_eq_mul, norm_mul, PadicInt.norm_p]
  have step : ∀ m, m₀ ≤ m → ∀ t : ℝ, 0 ≤ t → (∀ g, P m g → ‖(lam g).toAdd‖ ≤ t) →
      ∀ g, P (m + 1) g → ‖(lam g).toAdd‖ ≤ (l:ℝ)⁻¹ * t := by
    intro m hm t ht hyp g hg
    have chain : ∀ k : ℕ, ∃ g', P (m + 1 + k) g' ∧
        ‖(lam g).toAdd‖ ≤ max ((l:ℝ)⁻¹ * t) ‖(lam g').toAdd‖ := by
      intro k
      induction k with
      | zero => exact ⟨g, by simpa using hg, le_max_right _ _⟩
      | succ k ih =>
        obtain ⟨g', hg', hle⟩ := ih
        have hg'2 : P (m + k + 1) g' := by
          rw [show m + k + 1 = m + 1 + k by omega]; exact hg'
        obtain ⟨h, g'', hh, hg'', rfl⟩ := hdec (m + k) (by omega) g' hg'2
        refine ⟨g'', ?_, hle.trans (max_le (le_max_left _ _) ((key h g'').trans
          (max_le_max ?_ le_rfl)))⟩
        · rw [show m + 1 + (k + 1) = m + k + 2 by omega]; exact hg''
        · exact mul_le_mul_of_nonneg_left (hyp h (hmono' m k h hh)) (inv_nonneg.2 hlpos.le)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := hsmall ε hε
    obtain ⟨g', hg', hle⟩ := chain N
    have hsm := hN g' (hmono' N (m + 1) g' (by rw [show N + (m + 1) = m + 1 + N by omega]; exact hg'))
    exact hle.trans (max_le (le_add_of_nonneg_right hε.le)
      (hsm.trans (le_add_of_nonneg_left (mul_nonneg (inv_nonneg.2 hlpos.le) ht))))
  have levels : ∀ j : ℕ, ∀ g, P (m₀ + j) g → ‖(lam g).toAdd‖ ≤ ((l:ℝ)⁻¹) ^ j := by
    intro j
    induction j with
    | zero => intro g _; rw [pow_zero]; exact PadicInt.norm_le_one _
    | succ j ih =>
      intro g hg
      rw [pow_succ']
      exact step (m₀ + j) (by omega) _ (pow_nonneg (inv_nonneg.2 hlpos.le) _) ih g hg
  refine ⟨(l:ℝ) ^ m₀, fun m g hg => ?_⟩
  rcases le_or_gt m₀ m with h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
    calc ‖(lam g).toAdd‖ ≤ ((l:ℝ)⁻¹) ^ j := levels j g hg
      _ = (l:ℝ) ^ m₀ * ((l:ℝ)⁻¹) ^ (m₀ + j) := by
        rw [pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hlpos.ne', one_pow, one_mul]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt h
    have e : (l:ℝ) ^ (m + j + 1) * ((l:ℝ)⁻¹) ^ m = (l:ℝ) ^ (j + 1) := by
      rw [show m + j + 1 = m + (j + 1) by omega, pow_add, mul_comm ((l:ℝ) ^ m), mul_assoc,
        ← mul_pow, mul_inv_cancel₀ hlpos.ne', one_pow, mul_one]
    rw [e]
    exact (PadicInt.norm_le_one _).trans (one_le_pow₀ (by exact_mod_cast hl.out.one_lt.le))
