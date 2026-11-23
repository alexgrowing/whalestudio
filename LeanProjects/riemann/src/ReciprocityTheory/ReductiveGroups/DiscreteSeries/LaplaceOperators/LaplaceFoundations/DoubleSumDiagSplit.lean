import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities

noncomputable section

open Finset
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

theorem double_sum_diag_split {n : ℕ} (f : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, f a b = ∑ a, f a a + ∑ a, ∑ b, (if a < b then f a b + f b a else 0) := by
  have h1 : ∀ a b, f a b = (if a < b then f a b else 0) + (if a = b then f a b else 0)
      + (if b < a then f a b else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.mpr h.le]
  have h2 : ∑ a, ∑ b, (if b < a then f a b else 0) = ∑ a, ∑ b, (if a < b then f b a else 0) :=
    Finset.sum_comm
  calc ∑ a, ∑ b, f a b
      = ∑ a, ∑ b, ((if a < b then f a b else 0) + (if a = b then f a b else 0)
          + (if b < a then f a b else 0)) :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => h1 a b))
    _ = ∑ a, ∑ b, (if a < b then f a b else 0) + ∑ a, f a a
          + ∑ a, ∑ b, (if b < a then f a b else 0) := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = _ := by
        rw [h2, add_comm (∑ a, ∑ b, (if a < b then f a b else 0)) (∑ a, f a a), add_assoc,
          ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl (fun a _ => ?_)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        split_ifs <;> simp

theorem b2Id : RaisingLoweringNormIdentities := by
  intro n ε M _ _ E lam w hD
  obtain ⟨hGl, hU, hw1, ⟨hdiag, hup⟩, hcas⟩ := hD
  set Λ := lowK ε lam with hΛ
  let sR : Fin n → Fin n → ℝ := fun a b => if ε a = ε b then 1 else -1
  have hsC : ∀ a b, adjSign ε a b = ((sR a b : ℝ) : ℂ) := by
    intro a b; simp only [adjSign, sR]; split_ifs <;> simp
  have hsymm : ∀ a b, sR a b = sR b a := by
    intro a b; simp only [sR]
    by_cases h : ε a = ε b
    · simp [h]
    · simp [h, Ne.symm h]
  have hsq : ∀ a b, sR a b * sR a b = 1 := by
    intro a b; simp only [sR]; split_ifs <;> norm_num
  have hww : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw1]; simp
  have hQ : ∀ a b, ⟪w, E a b (E b a w)⟫_ℂ = ((sR a b * ‖E b a w‖ ^ 2 : ℝ) : ℂ) := by
    intro a b
    have h := hU b a w (E b a w)
    rw [inner_self_eq_norm_sq_to_K, hsC] at h
    have h1 : ((sR b a : ℝ) : ℂ) * ((sR b a : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hsq]; simp
    calc ⟪w, E a b (E b a w)⟫_ℂ
        = ((sR b a : ℝ) : ℂ) * (((sR b a : ℝ) : ℂ) * ⟪w, E a b (E b a w)⟫_ℂ) := by
          rw [← mul_assoc, h1, one_mul]
      _ = _ := by
          rw [← h, hsymm b a]; try simp only [RCLike.ofReal_eq_complex_ofReal]
          push_cast; ring
  have hC : ∀ a b, ⟪w, E a b (E b a w)⟫_ℂ - ⟪w, E b a (E a b w)⟫_ℂ = (((Λ a - Λ b : ℝ)) : ℂ) := by
    intro a b
    have h := hGl a b b a
    rw [if_pos rfl, if_pos rfl] at h
    have h2 := congrArg (fun T : Module.End ℂ M => T w) h
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h2
    rw [← inner_sub_right, h2, hdiag a, hdiag b, ← sub_smul, inner_smul_right, hww, mul_one]
    push_cast; ring
  have hR1 : ∀ a b, sR a b * ‖E b a w‖ ^ 2 - sR b a * ‖E a b w‖ ^ 2 = Λ a - Λ b := by
    intro a b
    have h := hC a b
    rw [hQ a b, hQ b a, ← Complex.ofReal_sub] at h
    exact_mod_cast h
  have hR2 : ∀ a, ‖E a a w‖ ^ 2 = Λ a ^ 2 := by
    intro a
    rw [hdiag a, norm_smul, hw1, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hR3 : ∀ a b, a < b → ε a = ε b → ‖E a b w‖ ^ 2 = 0 := by
    intro a b hab he; rw [hup a b hab he]; simp
  have hcasR : casVal lam = ∑ a, ∑ b, sR a b * ‖E b a w‖ ^ 2 := by
    have h1 : ⟪w, casimir E w⟫_ℂ = ∑ a, ∑ b, ⟪w, E a b (E b a w)⟫_ℂ := by
      simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply, inner_sum]
    rw [hcas, inner_smul_right, hww, mul_one] at h1
    simp only [hQ] at h1
    exact_mod_cast h1
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab he
    have h := hR1 a b
    have hs1 : sR a b = 1 := if_pos he
    have hs2 : sR b a = 1 := if_pos he.symm
    rw [hs1, hs2, hR3 a b hab he] at h
    linarith
  · intro a b hab he
    have h := hR1 a b
    have hs1 : sR a b = -1 := if_neg he
    have hs2 : sR b a = -1 := if_neg (Ne.symm he)
    rw [hs1, hs2] at h
    linarith
  · have hpt : ∀ a b, (if a < b then sR a b * ‖E b a w‖ ^ 2 + sR b a * ‖E a b w‖ ^ 2 else 0) =
        (if a < b ∧ ε b = ε a then Λ a else 0) - (if a < b ∧ ε a = ε b then Λ b else 0)
        - ((if a < b ∧ ε b ≠ ε a then Λ a else 0) - (if a < b ∧ ε a ≠ ε b then Λ b else 0))
        - 2 * (if a < b ∧ ε a ≠ ε b then ‖E b a w‖ ^ 2 else 0) := by
      intro a b
      by_cases hab : a < b
      · have h := hR1 a b
        by_cases he : ε a = ε b
        · have hs1 : sR a b = 1 := if_pos he
          have hs2 : sR b a = 1 := if_pos he.symm
          have h0 := hR3 a b hab he
          rw [hs1, hs2, h0] at h
          simp [hab, he, hs1, hs2, h0]
          linarith
        · have hs1 : sR a b = -1 := if_neg he
          have hs2 : sR b a = -1 := if_neg (Ne.symm he)
          rw [hs1, hs2] at h
          simp [hab, he, Ne.symm he, hs1, hs2]
          linarith
      · simp [hab]
    have hsw1 : ∑ a, ∑ b, (if b < a ∧ ε b = ε a then Λ a else 0) =
        ∑ a, ∑ b, (if a < b ∧ ε a = ε b then Λ b else 0) := Finset.sum_comm
    have hsw2 : ∑ a, ∑ b, (if b < a ∧ ε b ≠ ε a then Λ a else 0) =
        ∑ a, ∑ b, (if a < b ∧ ε a ≠ ε b then Λ b else 0) := Finset.sum_comm
    have hA : 2 * ∑ a, Λ a * rhoC ε a = ∑ a, ∑ b, (if a < b ∧ ε b = ε a then Λ a else 0)
        - ∑ a, ∑ b, (if a < b ∧ ε a = ε b then Λ b else 0) := by
      rw [← hsw1, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      have e1 : ∑ b, (if a < b ∧ ε b = ε a then Λ a else 0) =
          Λ a * ∑ b, (if a < b ∧ ε b = ε a then (1:ℝ) else 0) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by split_ifs <;> simp)
      have e2 : ∑ b, (if b < a ∧ ε b = ε a then Λ a else 0) =
          Λ a * ∑ b, (if b < a ∧ ε b = ε a then (1:ℝ) else 0) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by split_ifs <;> simp)
      rw [e1, e2]
      simp only [rhoC, Finset.natCast_card_filter]
      ring
    have hB : 2 * ∑ a, Λ a * rhoN ε a = ∑ a, ∑ b, (if a < b ∧ ε b ≠ ε a then Λ a else 0)
        - ∑ a, ∑ b, (if a < b ∧ ε a ≠ ε b then Λ b else 0) := by
      rw [← hsw2, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      have e1 : ∑ b, (if a < b ∧ ε b ≠ ε a then Λ a else 0) =
          Λ a * ∑ b, (if a < b ∧ ε b ≠ ε a then (1:ℝ) else 0) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by split_ifs <;> simp)
      have e2 : ∑ b, (if b < a ∧ ε b ≠ ε a then Λ a else 0) =
          Λ a * ∑ b, (if b < a ∧ ε b ≠ ε a then (1:ℝ) else 0) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by split_ifs <;> simp)
      rw [e1, e2]
      simp only [rhoN, Finset.natCast_card_filter]
      ring
    have hdiagsum : ∑ a, sR a a * ‖E a a w‖ ^ 2 = ∑ a, Λ a ^ 2 :=
      Finset.sum_congr rfl (fun a _ => by rw [hR2 a, show sR a a = 1 from if_pos rfl, one_mul])
    have hspl := double_sum_diag_split (fun a b => sR a b * ‖E b a w‖ ^ 2)
    have hcasv : casVal lam = ∑ a, Λ a ^ 2 + (∑ a, ∑ b, (if a < b ∧ ε b = ε a then Λ a else 0)
        - ∑ a, ∑ b, (if a < b ∧ ε a = ε b then Λ b else 0)
        - (∑ a, ∑ b, (if a < b ∧ ε b ≠ ε a then Λ a else 0)
          - ∑ a, ∑ b, (if a < b ∧ ε a ≠ ε b then Λ b else 0))
        - 2 * ∑ a, ∑ b, (if a < b ∧ ε a ≠ ε b then ‖E b a w‖ ^ 2 else 0)) := by
      rw [hcasR, hspl, hdiagsum]
      congr 1
      rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hpt a b))]
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hz : ∑ a, (Λ a ^ 2 + 2 * (Λ a * rhoC ε a) - 2 * (Λ a * rhoN ε a) - lam a * lam a
        + (rhoN ε - rhoC ε) a * (rhoN ε - rhoC ε) a) = 0 :=
      Finset.sum_eq_zero (fun a _ => by simp only [hΛ, lowK, Pi.add_apply, Pi.sub_apply]; ring)
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hz
    simp only [Finset.sum_filter]
    simp only [casVal, nsq, dot] at hcasv ⊢
    linarith [hcasv, hz, hA, hB]

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
