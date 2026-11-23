import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.NotKept
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.WdimUp

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

section Shape

variable {s r : ℕ} {A : ℕ} {Ai Ci : Fin s → ℕ} {mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ} {lam : Fin r → ℤ}

def wbK (mu : Fin (2 * s + 1 + 1) → Fin (r + 1) → ℤ) (n t : ℕ) : ℤ :=
  if h : n < 2 * s + 2 ∧ t < r then mu ⟨n, h.1⟩ ⟨t + 1, by omega⟩ else 0

theorem wb_vstep (hP : IsPair A Ai Ci mu lam) (a : ℕ) (ha : a < 2 * s + 1) (hv : a = 0 ∨ a % 2 = 1) :
    (∀ t, t < r → wbK mu a t ≤ wbK mu (a + 1) t) ∧ (∀ t, t + 1 < r → wbK mu (a + 1) (t + 1) ≤ wbK mu a t) := by
  have h := hP.1.2 ⟨a, ha⟩
  have hvec : (kLetters A Ai Ci).vec ⟨a, ha⟩ = true := by
    unfold kLetters; simp only [decide_eq_true_eq]; exact hv
  rw [if_pos hvec] at h
  obtain ⟨h1, h2, -⟩ := h
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have := h1 ⟨t + 1, by omega⟩
    unfold wbK
    rw [dif_pos (⟨by omega, by omega⟩ : _ ∧ _), dif_pos (⟨by omega, by omega⟩ : _ ∧ _)]
    exact this
  · have := h2 ⟨t + 1, by omega⟩ ⟨t + 2, by omega⟩ rfl
    unfold wbK
    rw [dif_pos (⟨by omega, by omega⟩ : _ ∧ _), dif_pos (⟨by omega, by omega⟩ : _ ∧ _)]
    exact this

theorem wb_cstep (hP : IsPair A Ai Ci mu lam) (a : ℕ) (ha : a < 2 * s + 1) (hc : ¬ (a = 0 ∨ a % 2 = 1)) :
    (∀ t, t < r → wbK mu (a + 1) t ≤ wbK mu a t) ∧ (∀ t, t + 1 < r → wbK mu a (t + 1) ≤ wbK mu (a + 1) t) := by
  have h := hP.1.2 ⟨a, ha⟩
  have hvec : (kLetters A Ai Ci).vec ⟨a, ha⟩ = false := by
    unfold kLetters; simp only [decide_eq_false_iff_not]; exact hc
  rw [if_neg (by rw [hvec]; exact Bool.false_ne_true)] at h
  obtain ⟨h1, h2, -⟩ := h
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have := h1 ⟨t + 1, by omega⟩
    unfold wbK
    rw [dif_pos (⟨by omega, by omega⟩ : _ ∧ _), dif_pos (⟨by omega, by omega⟩ : _ ∧ _)]
    exact this
  · have := h2 ⟨t + 1, by omega⟩ ⟨t + 2, by omega⟩ rfl
    unfold wbK
    rw [dif_pos (⟨by omega, by omega⟩ : _ ∧ _), dif_pos (⟨by omega, by omega⟩ : _ ∧ _)]
    exact this

theorem wb_one (hP : IsPair A Ai Ci mu lam) (t : ℕ) : wbK mu 1 t = 0 := by
  have h0 := hP.1.1
  have h := hP.1.2 ⟨0, by omega⟩
  have hvec : (kLetters A Ai Ci).vec ⟨0, by omega⟩ = true := by unfold kLetters; simp
  rw [if_pos hvec] at h
  obtain ⟨h1, h2, -⟩ := h
  unfold wbK
  split_ifs with hh
  · have a1 := h1 ⟨t + 1, by omega⟩
    have a2 := h2 ⟨t, by omega⟩ ⟨t + 1, by omega⟩ rfl
    have e0 : (Fin.castSucc (⟨0, by omega⟩ : Fin (2 * s + 1))) = 0 := rfl
    have e1 : (Fin.succ (⟨0, by omega⟩ : Fin (2 * s + 1))) = ⟨1, by omega⟩ := rfl
    rw [e0, h0, e1] at a1 a2
    simp only [Pi.zero_apply] at a1 a2
    exact le_antisymm a2 a1
  · rfl

theorem wb_shape (hP : IsPair A Ai Ci mu lam) (hr : 2 * s + 1 ≤ r) (i : ℕ) (hi : i ≤ s) :
    (∀ t, t < i → 0 ≤ wbK mu (2 * i + 1) t) ∧ (∀ t, i ≤ t → t + i < r → wbK mu (2 * i + 1) t = 0) ∧
      (∀ t, r ≤ t + i → wbK mu (2 * i + 1) t ≤ 0) := by
  induction i with
  | zero =>
    refine ⟨fun t ht => absurd ht (by omega), fun t _ _ => wb_one hP t, fun t _ => ?_⟩
    rw [wb_one hP t]
  | succ i ih =>
    obtain ⟨p1, p2, p3⟩ := ih (by omega)
    have hv := wb_vstep hP (2 * i + 1) (by omega) (Or.inr (by omega))
    have hc := wb_cstep hP (2 * i + 2) (by omega) (by omega)
    have e1 : 2 * i + 1 + 1 = 2 * i + 2 := rfl
    have e2 : 2 * (i + 1) + 1 = 2 * i + 2 + 1 := by ring
    rw [e1] at hv
    rw [e2]

    have v1 : ∀ t, t ≤ i → 0 ≤ wbK mu (2 * i + 2) t := fun t ht => by
      rcases Nat.lt_or_ge t i with h | h
      · exact le_trans (p1 t h) (hv.1 t (by omega))
      · have : t = i := by omega
        subst this; exact le_trans (le_of_eq (p2 t le_rfl (by omega)).symm) (hv.1 t (by omega))
    have v2 : ∀ t, i + 1 ≤ t → t + i < r → wbK mu (2 * i + 2) t = 0 := fun t h1 h2 => by
      apply le_antisymm
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        exact le_trans (hv.2 t' (by omega)) (le_of_eq (p2 t' (by omega) (by omega)))
      · exact le_trans (le_of_eq (p2 t (by omega) h2).symm) (hv.1 t (by omega))
    have v3 : ∀ t, r ≤ t + i → wbK mu (2 * i + 2) t ≤ 0 := fun t h1 => by
      by_cases ht : t < r
      · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        refine le_trans (hv.2 t' (by omega)) ?_
        by_cases h3 : r ≤ t' + i
        · exact p3 t' h3
        · exact le_of_eq (p2 t' (by omega) (by omega))
      · unfold wbK; rw [dif_neg (by omega)]
    refine ⟨fun t ht => ?_, fun t h1 h2 => ?_, fun t h1 => ?_⟩
    · rcases Nat.lt_or_ge (t + 1) (i + 1) with h | h
      · exact le_trans (v1 (t + 1) (by omega)) (hc.2 t (by omega))
      · have : t = i := by omega
        subst this
        exact le_trans (le_of_eq (v2 (t + 1) (by omega) (by omega)).symm) (hc.2 t (by omega))
    · apply le_antisymm
      · exact le_trans (hc.1 t (by omega)) (le_of_eq (v2 t h1 (by omega)))
      · exact le_trans (le_of_eq (v2 (t + 1) (by omega) (by omega)).symm) (hc.2 t (by omega))
    · by_cases ht : t < r
      · refine le_trans (hc.1 t ht) ?_
        by_cases h3 : r ≤ t + i
        · exact v3 t h3
        · exact le_of_eq (v2 t (by omega) (by omega))
      · unfold wbK; rw [dif_neg (by omega)]

theorem wb_follow (hP : IsPair A Ai Ci mu lam) (i0 : ℕ) (i : ℕ) (h0 : i0 ≤ i) (hi : i < s) (hr : s ≤ r) :
    wbK mu (2 * i + 3) (i - i0) ≤ wbK mu (2 * i0 + 2) 0 := by
  induction i with
  | zero =>
    have : i0 = 0 := by omega
    subst this
    exact (wb_cstep hP 2 (by omega) (by omega)).1 0 (by omega)
  | succ i ih =>
    rcases Nat.lt_or_ge i0 (i + 1) with h | h
    · have ih' := ih (by omega) (by omega)
      have hv := (wb_vstep hP (2 * i + 3) (by omega) (Or.inr (by omega))).2 (i - i0) (by omega)
      have hc := (wb_cstep hP (2 * i + 4) (by omega) (by omega)).1 (i + 1 - i0) (by omega)
      have e : i + 1 - i0 = (i - i0) + 1 := by omega
      have e2 : 2 * (i + 1) + 3 = 2 * i + 4 + 1 := by ring
      rw [e2]
      rw [e] at hc ⊢
      exact le_trans hc (le_trans hv ih')
    · have : i0 = i + 1 := by omega
      subst this
      have e2 : 2 * (i + 1) + 3 = 2 * (i + 1) + 2 + 1 := by ring
      rw [e2, Nat.sub_self]
      exact (wb_cstep hP (2 * (i + 1) + 2) (by omega) (by omega)).1 0 (by omega)

theorem wb_last (t : ℕ) (ht : t < r) : wbK mu (2 * s + 1) t = mu (Fin.last _) ⟨t + 1, by omega⟩ := by
  unfold wbK; rw [dif_pos ⟨by omega, ht⟩]; rfl

end Shape

theorem wb_sdXi_mono (r : ℕ) {a b : ℕ} (h : a ≤ b) : (sdXi r a : ℚ) ≤ (sdXi r b : ℚ) := by
  unfold sdXi
  exact_mod_cast Nat.choose_le_choose _ (by omega)

theorem wb_sdXi_nonneg (r a : ℕ) : (0 : ℚ) ≤ (sdXi r a : ℚ) := Nat.cast_nonneg _

theorem wtBound_of (hCD : ChainDimAt) : WtBoundAt := by
  intro s r _ A Ai Ci mu lam hr hP
  have hanti : Antitone lam := inter_anti hP.2
  have hup := wdimUp_of hCD r lam hanti
  refine le_trans hup ?_
  obtain ⟨q1, q2, q3⟩ := wb_shape hP hr s le_rfl

  have hI := hP.2
  have lo : ∀ t (ht : t < r), wbK mu (2 * s + 1) t ≤ lam ⟨t, ht⟩ := fun t ht => by
    rw [wb_last t ht]; exact (hI ⟨t, ht⟩).1
  have hi : ∀ t (ht : t + 1 < r), lam ⟨t + 1, ht⟩ ≤ wbK mu (2 * s + 1) t := fun t ht => by
    rw [wb_last t (by omega)]; exact (hI ⟨t + 1, ht⟩).2

  let g : ℕ → ℚ := fun t =>
    if t = 0 then (sdXi r (lam ⟨0, by omega⟩).toNat : ℚ)
    else if t ≤ s then (sdXi r (pairRho mu (s - t)).toNat : ℚ)
    else if t + s < r then 1
    else (sdXi r (pairN (s := s) lam (t - (r - s))).toNat : ℚ)
  have hle : ∀ t : Fin r, (sdXi r (lam t).natAbs : ℚ) ≤ g t := by
    intro ⟨t, ht⟩
    simp only [g]
    by_cases h0 : t = 0
    · subst h0
      rw [if_pos rfl]
      have : 0 ≤ lam ⟨0, ht⟩ := le_trans (by
        rcases Nat.eq_zero_or_pos s with hs | hs
        · exact le_of_eq (q2 0 (by omega) (by omega)).symm
        · exact q1 0 hs) (lo 0 ht)
      apply le_of_eq; congr 2; omega
    rw [if_neg h0]
    by_cases h1 : t ≤ s
    · rw [if_pos h1]
      have hnn : 0 ≤ lam ⟨t, ht⟩ := le_trans (by
        rcases Nat.lt_or_ge t s with hs | hs
        · exact q1 t hs
        · exact le_of_eq (q2 t hs (by omega)).symm) (lo t ht)
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      have hf := wb_follow hP (s - (t' + 1)) (s - 1) (by omega) (by omega) (by omega)
      have e1 : 2 * (s - 1) + 3 = 2 * s + 1 := by omega
      have e2 : s - 1 - (s - (t' + 1)) = t' := by omega
      rw [e1, e2] at hf
      have hl := le_trans (hi t' ht) hf
      have hrho : pairRho mu (s - (t' + 1)) = wbK mu (2 * (s - (t' + 1)) + 2) 0 := by
        unfold pairRho wbK finPos
        rw [dif_pos ⟨by omega, by omega⟩]
        congr 1
        · apply Fin.ext; simp only; omega
      rw [hrho]
      apply wb_sdXi_mono
      omega
    · rw [if_neg h1]
      by_cases h2 : t + s < r
      · rw [if_pos h2]
        have hz : lam ⟨t, ht⟩ = 0 := by
          apply le_antisymm
          · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
            exact le_trans (hi t' ht) (le_of_eq (q2 t' (by omega) (by omega)))
          · exact le_trans (le_of_eq (q2 t (by omega) h2).symm) (lo t ht)
        rw [hz]; simp [sdXi_zero]
      · rw [if_neg h2]
        have hnp : lam ⟨t, ht⟩ ≤ 0 := by
          obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
          refine le_trans (hi t' ht) ?_
          by_cases h3 : r ≤ t' + s
          · exact q3 t' h3
          · exact le_of_eq (q2 t' (by omega) (by omega))
        have hN : pairN (s := s) lam (t - (r - s)) = -lam ⟨t, ht⟩ := by
          unfold pairN
          rw [dif_pos (by omega)]
          congr 2
          apply Fin.ext; simp only; omega
        rw [hN]
        apply le_of_eq; congr 2; omega
  have hprod : ∏ t : Fin r, (sdXi r (lam t).natAbs : ℚ) ≤ ∏ t : Fin r, g t :=
    Finset.prod_le_prod (fun t _ => wb_sdXi_nonneg _ _) (fun t _ => hle t)
  refine le_trans hprod (le_of_eq ?_)
  rw [Fin.prod_univ_eq_prod_range (fun t => g t) r]
  have hsplit1 : Finset.range r = Finset.range 1 ∪ Finset.Ico 1 r := by
    ext x; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
  rw [← Finset.prod_range_mul_prod_Ico _ (show 1 ≤ r by omega), Finset.prod_range_one,
    ← Finset.prod_Ico_consecutive _ (show 1 ≤ s + 1 by omega) (show s + 1 ≤ r by omega),
    ← Finset.prod_Ico_consecutive _ (show s + 1 ≤ r - s by omega) (show r - s ≤ r by omega)]
  have a0 : g 0 = (sdXi r (lam 0).toNat : ℚ) := by simp only [g, if_pos rfl]; rfl
  have a1 : ∏ t ∈ Finset.Ico 1 (s + 1), g t = ∏ i : Fin s, (sdXi r (pairRho mu i).toNat : ℚ) := by
    rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel, ← Finset.prod_range_reflect,
      ← Fin.prod_univ_eq_prod_range (fun i => g (1 + (s - 1 - i))) s]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi := i.2
    simp only [g]
    rw [if_neg (by omega), if_pos (by omega), show s - (1 + (s - 1 - (i : ℕ))) = (i : ℕ) by omega]
  have a2 : ∏ t ∈ Finset.Ico (s + 1) (r - s), g t = 1 := by
    refine Finset.prod_eq_one fun t ht => ?_
    simp only [Finset.mem_Ico] at ht
    simp only [g]
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have a3 : ∏ t ∈ Finset.Ico (r - s) r, g t = ∏ i : Fin s, (sdXi r (pairN (s := s) lam i).toNat : ℚ) := by
    rw [Finset.prod_Ico_eq_prod_range, show r - (r - s) = s by omega,
      ← Fin.prod_univ_eq_prod_range (fun i => g (r - s + i)) s]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi := i.2
    simp only [g]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), show r - s + (i : ℕ) - (r - s) = (i : ℕ) by omega]
  rw [a0, a1, a2, a3, one_mul, mul_assoc]

end Formalism.MainNotions.ColumnSystems.Pf
