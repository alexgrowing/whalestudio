import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.EdgeLatticeAdaptedBasis
import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.RestCloudOfX

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning MvPolynomial

theorem ord_pos {n' m : ℕ} (r : ℕ) (lam : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant lam) (s : Fin n') :
    ∑ a : Fin (m + 1) with a.val < r, (lamAt lam s a - lamAt lam s (Fin.last m)) ≤
      (r : ℤ) * (lam s 0 - lam s (Fin.last m)) := by
  have hsp : 0 ≤ lam s 0 - lam s (Fin.last m) := sub_nonneg.2 (hd s (Fin.zero_le _))
  have hterm : ∀ a : Fin (m + 1), lamAt lam s a - lamAt lam s (Fin.last m) ≤ lam s 0 - lam s (Fin.last m) := by
    intro a
    unfold lamAt
    split_ifs
    · have := hd s (Fin.zero_le a)
      omega
    · have h1 := hd s (Fin.le_last a.rev)
      simp only [Fin.rev_last]
      omega
  have hcard : ((Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card : ℤ) ≤ r := by
    have : (Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card ≤ r := by
      calc (Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card
          ≤ (Finset.range r).card := by
            apply Finset.card_le_card_of_injOn (fun a => a.val)
            · intro a ha
              simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha
              simpa using ha
            · intro a _ b _ hab
              exact Fin.ext hab
        _ = r := Finset.card_range r
    exact_mod_cast this
  calc ∑ a : Fin (m + 1) with a.val < r, (lamAt lam s a - lamAt lam s (Fin.last m))
      ≤ ∑ _a : Fin (m + 1) with _a.val < r, (lam s 0 - lam s (Fin.last m)) := Finset.sum_le_sum fun a _ => hterm a
    _ = ((Finset.univ.filter fun a : Fin (m + 1) => a.val < r).card : ℤ) * (lam s 0 - lam s (Fin.last m)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hsp

theorem ordMax_rest {n' m : ℕ} (hm : 2 ≤ m) {TT : Finset (Fin n')} {aT bT : Fin n' → ℤ} {cpp c0 : ℕ} {a : ℝ}
    {lam0 : Fin n' → Fin (m + 1) → ℤ} (hW : tableLineDegreeFive.WeightHyp TT aT bT cpp c0 a lam0) (r : ℕ) :
    ordMax r (restW TT lam0) ≤ ((r * TT.card * c0 + 2 * r * n' * cpp : ℕ) : ℤ) := by
  obtain ⟨hb, hdom, hw⟩ := hW
  have hdr := restW_dom (by omega) TT lam0 hdom
  have hl0 : Fin.last m ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hv1 : ((1 : Fin (m + 1)) : ℕ) = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have key : ∀ s, restW TT lam0 s 0 - restW TT lam0 s (Fin.last m) ≤
      (if s ∈ TT then (c0 : ℤ) else 0) + 2 * cpp := by
    intro s
    have e1 : restW TT lam0 s (Fin.last m) = lam0 s (Fin.last m) := by
      unfold restW flW
      simp [Pi.single_apply, hl0]
    have e0 : restW TT lam0 s 0 = lam0 s 0 - (dT TT lam0 s : ℤ) := by
      unfold restW flW
      simp
    rw [e0, e1]
    by_cases hs : s ∈ TT
    · obtain ⟨_, elast, hc⟩ := (hb s).1 hs
      obtain ⟨_, _, hb0, hbc⟩ := hw s hs
      have h01 : lam0 s 1 ≤ lam0 s 0 := hdom s (Fin.zero_le _)
      have hc1 := abs_le.1 (hc 1 (by omega) (by omega))
      unfold dT flatDeg
      rw [if_pos hs, if_pos hs, Int.toNat_of_nonneg (by omega), elast]
      omega
    · have h1 := abs_le.1 ((hb s).2 hs 0)
      have h2 := abs_le.1 ((hb s).2 hs (Fin.last m))
      unfold dT
      rw [if_neg hs, if_neg hs]
      push_cast
      omega
  unfold ordMax
  have hr0 : (0 : ℤ) ≤ r := Int.natCast_nonneg _
  calc ∑ s : Fin n', ∑ a : Fin (m + 1) with a.val < r,
        (lamAt (restW TT lam0) s a - lamAt (restW TT lam0) s (Fin.last m))
      ≤ ∑ s : Fin n', (r : ℤ) * ((if s ∈ TT then (c0 : ℤ) else 0) + 2 * cpp) :=
        Finset.sum_le_sum fun s _ => le_trans (ord_pos r _ hdr s) (mul_le_mul_of_nonneg_left (key s) hr0)
    _ = ((r * TT.card * c0 + 2 * r * n' * cpp : ℕ) : ℤ) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        push_cast
        simp only [nsmul_eq_mul]
        ring

end Formalism.MainNotions.Pf14
