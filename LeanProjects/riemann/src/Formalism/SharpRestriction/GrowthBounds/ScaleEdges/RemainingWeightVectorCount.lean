import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.WeylDimShift

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.CountingSumsFrames

theorem dimV_eq (D : Formalism.BasicNotions.D7) (h35 : tableLineDegreeFive.FewBadOrbits D) (Kf : Type) [Field Kf] {n' m : ℕ}
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lam0) :
    ((dimV Kf lam0 : ℕ) : ℚ) = ∏ s : Fin n', weylDim (m + 1) (lam0 s) := by
  rw [h35 Kf n' m lam0 hdom]
  refine Finset.prod_congr rfl fun s _ => ?_
  have e1 : (∏ i : Fin (m + 1), ∏ j : Fin (m + 1),
      if i < j then (((lamAt lam0 s i : ℤ) : ℚ) - ((lamAt lam0 s j : ℤ) : ℚ) + ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) /
        (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) else 1) = weylDim (m + 1) (lamAt lam0 s) := by
    unfold weylDim
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    push_cast
    rfl
  rw [e1]
  unfold lamAt
  split_ifs
  · rfl
  · exact weylDim_dual (m + 1) (lam0 s)

def remainingWeightVectorCount {n' m : ℕ} (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (m + 1) → ℤ) : ℚ :=
  (∏ t ∈ TT, weylDim m (fun i : Fin m => lam0 t i.succ)) * ∏ s ∈ TTᶜ, weylDim (m + 1) (lam0 s)

theorem top_count {n' m : ℕ} (hm : 2 ≤ m) {TT : Finset (Fin n')} {aT bT : Fin n' → ℤ} {cpp c0 : ℕ} {a : ℝ} (ha : 0 < a)
    {lam0 : Fin n' → Fin (m + 1) → ℤ} (hW : tableLineDegreeFive.WeightHyp TT aT bT cpp c0 a lam0) (t : Fin n') (ht : t ∈ TT) :
    (1 - ((m + 1 : ℕ) : ℝ) * c0 / a) * (weylDim (m + 1) (lam0 t) : ℝ) ≤
      ((Nat.choose (flatDeg lam0 t + (m + 1) - 1) (m + 1 - 1) : ℕ) : ℝ) *
        (weylDim m (fun i : Fin m => lam0 t i.succ) : ℝ) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hfd := flatDeg_bounds (by omega) ha.le hW t ht
  obtain ⟨hb, hdom, hw⟩ := hW
  obtain ⟨e0, elast, hc⟩ := (hb t).1 ht
  obtain ⟨_, _, hb0, hbc⟩ := hw t ht
  have hanti := hdom t
  set mu : Fin (m' + 1) → ℤ := fun i => lam0 t i.succ + bT t with hmu
  have hmuA : Antitone mu := by
    intro i j hij
    have := hanti (Fin.succ_le_succ_iff.2 hij)
    simp only [hmu]
    omega
  have hmuB : ∀ i, 0 ≤ mu i ∧ mu i ≤ c0 := by
    intro i
    constructor
    · have := hanti (Fin.le_last i.succ)
      simp only [hmu]
      omega
    · simp only [hmu]
      by_cases hi : i.succ.val < m' + 1
      · have := hc i.succ (by simp) hi
        have h2 := abs_le.1 this
        omega
      · have : i.succ = Fin.last (m' + 1) := by
          apply Fin.ext
          have := i.succ.isLt
          simp only [Fin.val_last]
          omega
        rw [this, elast]
        omega
  have h01 : lam0 t 1 ≤ lam0 t 0 := hanti (Fin.zero_le _)
  have hs0 : (Fin.succ (0 : Fin (m' + 1))) = (1 : Fin (m' + 1 + 1)) := rfl
  have hcons : (fun i => lam0 t i + bT t) = (Fin.cons ((flatDeg lam0 t : ℤ) + mu 0) mu : Fin (m' + 2) → ℤ) := by
    funext i
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp only [Fin.cons_zero, hmu, hs0]
      unfold flatDeg
      rw [Int.toNat_of_nonneg (by omega)]
      ring
    · simp only [Fin.cons_succ, hmu]
  have h1 := weylDim_cons_le_choose_mul m' mu (flatDeg lam0 t) c0 a ha hmuA hmuB hfd.1
  rw [← hcons, weylDim_shift, weylDim_shift] at h1
  have e1 : ((m' + 1 + 1 : ℕ) : ℝ) = (m' : ℝ) + 2 := by push_cast; ring
  have e2 : flatDeg lam0 t + (m' + 1 + 1) - 1 = flatDeg lam0 t + m' + 1 := by omega
  have e3 : m' + 1 + 1 - 1 = m' + 1 := by omega
  rw [e1, e2, e3]
  exact h1

theorem count_of_exact (D : Formalism.BasicNotions.D7) (h35 : tableLineDegreeFive.FewBadOrbits D) {C : ℝ} (hC : 2 ≤ C) {p n' m r : ℕ}
    {TT : Finset (Fin n')} {L₁ L₂ : ℕ} {de h x : ℝ} {lam0 : Fin n' → Fin (m + 1) → ℤ} {aT bT : Fin n' → ℤ} {a Y : ℝ}
    {cpp c0 Dp cStar : ℕ} (H : Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar)
    (Kf : Type) [Field Kf] (n2 : ℕ) (hn2 : (n2 : ℚ) = remainingWeightVectorCount TT lam0) :
    (1 - ((m + 1 : ℕ) : ℝ) * c0 / a) ^ TT.card * (dimV Kf lam0 : ℝ) ≤
      (∏ t ∈ TT, ((Nat.choose (flatDeg lam0 t + (m + 1) - 1) (m + 1 - 1) : ℕ) : ℝ)) * n2 := by
  have hB := hyps_basic (C := C) (by linarith) H
  have hk := rank_mul_conductor_div_le_one hC H
  have hW : tableLineDegreeFive.WeightHyp TT aT bT cpp c0 a lam0 := H.2.2.2.2.1
  have hdom : IsDominant lam0 := hW.2.1
  have ha : 0 < a := by linarith [hB.two_le_a]
  have hd : (dimV Kf lam0 : ℝ) = (∏ t ∈ TT, (weylDim (m + 1) (lam0 t) : ℝ)) * ∏ s ∈ TTᶜ, (weylDim (m + 1) (lam0 s) : ℝ) := by
    have h1 := dimV_eq D h35 Kf lam0 hdom
    have h2 : ((dimV Kf lam0 : ℕ) : ℝ) = (((dimV Kf lam0 : ℕ) : ℚ) : ℝ) := by push_cast; rfl
    rw [h2, h1, ← Finset.prod_mul_prod_compl TT]
    push_cast
    rfl
  have hn : (n2 : ℝ) = (∏ t ∈ TT, (weylDim m (fun i : Fin m => lam0 t i.succ) : ℝ)) *
      ∏ s ∈ TTᶜ, (weylDim (m + 1) (lam0 s) : ℝ) := by
    have h2 : (n2 : ℝ) = ((n2 : ℚ) : ℝ) := by push_cast; rfl
    rw [h2, hn2]
    unfold remainingWeightVectorCount
    push_cast
    rfl
  have hS : 0 ≤ ∏ s ∈ TTᶜ, (weylDim (m + 1) (lam0 s) : ℝ) := by
    refine Finset.prod_nonneg fun s _ => ?_
    exact_mod_cast (gram_weylDim_pos (m + 1) (lam0 s) (hdom s)).le
  have hT : ∏ t ∈ TT, ((1 - ((m + 1 : ℕ) : ℝ) * c0 / a) * (weylDim (m + 1) (lam0 t) : ℝ)) ≤
      ∏ t ∈ TT, (((Nat.choose (flatDeg lam0 t + (m + 1) - 1) (m + 1 - 1) : ℕ) : ℝ) *
        (weylDim m (fun i : Fin m => lam0 t i.succ) : ℝ)) := by
    refine Finset.prod_le_prod (fun t _ => ?_) fun t ht => top_count (by have := hB.m_ge; omega) ha hW t ht
    refine mul_nonneg (by linarith) ?_
    exact_mod_cast (gram_weylDim_pos (m + 1) (lam0 t) (hdom t)).le
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const] at hT
  rw [hd, hn]
  have := mul_le_mul_of_nonneg_right hT hS
  calc _ = (1 - ((m + 1 : ℕ) : ℝ) * c0 / a) ^ TT.card * (∏ t ∈ TT, (weylDim (m + 1) (lam0 t) : ℝ)) *
        ∏ s ∈ TTᶜ, (weylDim (m + 1) (lam0 s) : ℝ) := by ring
    _ ≤ _ := this
    _ = _ := by ring

end Formalism.MainNotions.Pf14
