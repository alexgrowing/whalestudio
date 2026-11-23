import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqOneOfStrictMono

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

theorem UpperTheory.V.AlgebraTools.hkInd :
    ∀ (n : ℕ) (p : Perm (Fin n) → Prop), p 1 →
      (∀ (a c : Fin n), a.val + 1 = c.val → ∀ w : Perm (Fin n), w⁻¹ a < w⁻¹ c → p w → p (swap a c * w)) → ∀ w, p w := by
  intro n p h1 hstep
  obtain ⟨hA, hB, -, -, -⟩ := UpperTheory.V.AlgebraTools.hkInv n
  have red : ∀ w : Perm (Fin n), w ≠ 1 → ∃ w', invN w = invN w' + 1 ∧ (p w' → p w) := by
    intro w hw
    obtain ⟨a, c, hac, hlt⟩ := hB w hw
    have hlt' : (swap a c * w)⁻¹ a < (swap a c * w)⁻¹ c := by
      rw [mul_inv_rev, swap_inv, Perm.mul_apply, Perm.mul_apply, swap_apply_left,
        swap_apply_right]
      exact hlt
    have hw' : swap a c * (swap a c * w) = w := swap_mul_self_mul a c w
    refine ⟨swap a c * w, ?_, fun hp => ?_⟩
    · have := (hA a c hac _ hlt').2.2
      rwa [hw'] at this
    · have := hstep a c hac _ hlt' hp
      rwa [hw'] at this
  have key : ∀ k, ∀ w : Perm (Fin n), invN w = k → p w := by
    intro k
    induction k with
    | zero =>
      intro w hw
      by_cases h : w = 1
      · subst h
        exact h1
      · obtain ⟨w', e, -⟩ := red w h
        exfalso
        omega
    | succ k ih =>
      intro w hw
      by_cases h : w = 1
      · subst h
        exact h1
      · obtain ⟨w', e, hp⟩ := red w h
        exact hp (ih w' (by omega))
  exact fun w => key _ w rfl
