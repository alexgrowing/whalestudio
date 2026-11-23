import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.RepNewformOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Sl2Low

open private bound cas wt_low from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Sl2Low

namespace UpperTheory.V.Af.Rn

section

variable {V : Type} [AddCommGroup V] [Module ℂ V] {W R L : Module.End ℂ V} {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ}

private theorem descend2 (hL : W * L - L * W = (-2 : ℂ) • L)
    (hC : (4 : ℂ) • (R * L) = -(W * W - (2 : ℂ) • W))
    (h0 : ∀ x, H x x = 0 → x = 0) (hW : ∀ x y, H (W x) y = H x (W y)) (hH : ∀ x y, H (L x) y = -H x (R y))
    (j : ℕ) : ∀ x : V, x ≠ 0 → W x = ((j : ℤ) : ℂ) • x →
      ∃ x, x ≠ 0 ∧ (W x = (2 : ℂ) • x ∨ W x = 0) ∧ L x = 0 := by
  have hC' : (4 : ℂ) • (R * L) = (((0 : ℕ) : ℂ) * (((0 : ℕ) : ℂ) - 2)) • 1 - (W * W - (2 : ℂ) • W) := by
    simpa using hC
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro x hx hWx
  have hRL := cas hC' hWx
  have hLz : (((0 : ℕ) : ℤ) * (((0 : ℕ) : ℤ) - 2) - (j : ℤ) * ((j : ℤ) - 2) = 0) → L x = 0 := by
    intro hz
    rw [hz] at hRL
    simp only [Int.cast_zero, zero_div, zero_smul] at hRL
    apply h0
    rw [hH, hRL, map_zero, neg_zero]
  by_cases hLx : L x = 0
  · refine ⟨x, hx, ?_, hLx⟩
    rw [hLx, map_zero] at hRL
    have hc := (smul_eq_zero.1 hRL.symm).resolve_right hx
    have hz : (j : ℤ) * ((j : ℤ) - 2) = 0 := by
      have : (((0 * (0 - 2) - (j : ℤ) * ((j : ℤ) - 2) : ℤ) : ℂ)) = 0 := by
        simpa using hc
      have := Int.cast_eq_zero.1 this
      linarith
    rcases mul_eq_zero.1 hz with h | h
    · right
      rw [hWx, h]
      simp
    · left
      rw [hWx]
      have : (j : ℤ) = 2 := by linarith
      rw [this]
      simp
  · rcases j with _ | _ | _ | j
    · exact absurd (hLz (by norm_num)) hLx
    · have := bound hL hC' h0 hW hH hx hWx
      norm_num at this
    · exact absurd (hLz (by norm_num)) hLx
    · have hw := wt_low hL hWx
      refine ih (j + 1) (by omega) (L x) hLx ?_
      rw [hw]
      push_cast
      ring_nf

end

end UpperTheory.V.Af.Rn

theorem UpperTheory.V.Af.Rn.sl2Two :
    UpperTheory.V.Af.Rn.Sl2Two := by
  intro V _ _ W R L H hWR hWL hRL hLR h0 hW hHR hHL hex
  obtain ⟨x, hx, n, hn⟩ := hex
  rcases le_or_gt 0 n with hn0 | hn0
  · obtain ⟨y, hy, hWy, hLy⟩ := descend2 hWL hRL h0 hW hHL n.toNat x hx
      (by rw [hn, Int.toNat_of_nonneg hn0])
    rcases hWy with h | h
    · exact ⟨y, hy, Or.inl ⟨h, hLy⟩⟩
    · exact ⟨y, hy, Or.inr (Or.inr ⟨h, hLy⟩)⟩
  · have hL' : (-W) * R - R * (-W) = (-2 : ℂ) • R := by
      rw [neg_mul, mul_neg, sub_neg_eq_add, neg_add_eq_sub, ← neg_sub, hWR, neg_smul]
    have hC' : (4 : ℂ) • (L * R) = -((-W) * (-W) - (2 : ℂ) • (-W)) := by
      rw [hLR, neg_mul_neg, smul_neg, sub_neg_eq_add]
    have hW' : ∀ a b, H ((-W) a) b = H a ((-W) b) := by
      intro a b
      simp only [LinearMap.neg_apply, map_neg, LinearMap.neg_apply, hW]
    obtain ⟨y, hy, hWy, hRy⟩ := descend2 hL' hC' h0 hW' hHR (-n).toNat x hx
      (by rw [LinearMap.neg_apply, hn, Int.toNat_of_nonneg (by omega)]; push_cast; rw [neg_smul])
    rcases hWy with h | h
    · refine ⟨y, hy, Or.inr (Or.inl ⟨?_, hRy⟩)⟩
      rw [LinearMap.neg_apply, neg_eq_iff_eq_neg] at h
      rw [h, neg_smul]
    · refine ⟨y, hy, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
      · rw [LinearMap.neg_apply, neg_eq_zero] at h
        exact h
      · rw [LinearMap.neg_apply, neg_eq_zero] at h
        have hR : R (L y) = 0 := by
          have := congrArg (fun T : Module.End ℂ V => T y) hRL
          simp only [LinearMap.smul_apply, Module.End.mul_apply, LinearMap.neg_apply,
            LinearMap.sub_apply, h, map_zero, smul_zero, sub_zero, neg_zero] at this
          exact (smul_eq_zero.1 this).resolve_left (by norm_num)
        apply h0
        rw [hHL, hR, map_zero, neg_zero]
