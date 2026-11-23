import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.AtypicalPathSmallWeight

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {n N : ℕ} {LL : Letters (Fin N)} {dd : Fin N → ℕ}

theorem step_vec (P : PPath n N LL dd) (i : Fin N) (h : LL.vec i = true) :
    HStrip (P.mu i.castSucc) (P.mu i.succ) (dd i) := by
  simpa [h] using P.step i

theorem step_cov (P : PPath n N LL dd) (i : Fin N) (h : LL.vec i = false) :
    HStrip (P.mu i.succ) (P.mu i.castSucc) (dd i) := by
  simpa [h] using P.step i

theorem mu_nonneg (P : PPath n N LL dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin n), m.val + s < n → 0 ≤ P.mu ⟨s, hs⟩ m := by
  intro s
  induction s with
  | zero =>
    intro hs m _
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
    rw [h0, P.zero]
    simp
  | succ s ih =>
    intro hs m hm
    have hsN : s < N := by omega
    cases hv : LL.vec ⟨s, hsN⟩
    · have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      have hm1 : m.val + 1 < n := by omega
      calc (0 : ℤ) ≤ P.mu ⟨s, by omega⟩ ⟨m.val + 1, hm1⟩ :=
            ih (by omega) ⟨m.val + 1, hm1⟩ (show m.val + 1 + s < n by omega)
        _ ≤ P.mu ⟨s + 1, hs⟩ m := hstr.2.1 m hm1
    · have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      calc (0 : ℤ) ≤ P.mu ⟨s, by omega⟩ m := ih (by omega) m (by omega)
        _ ≤ P.mu ⟨s + 1, hs⟩ m := hstr.1 m

theorem mu_nonpos (P : PPath n N LL dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin n), s ≤ m.val → P.mu ⟨s, hs⟩ m ≤ 0 := by
  intro s
  induction s with
  | zero =>
    intro hs m _
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
    rw [h0, P.zero]
    simp
  | succ s ih =>
    intro hs m hm
    have hsN : s < N := by omega
    obtain ⟨mv, hmv⟩ := m
    have hm' : s + 1 ≤ mv := hm
    cases hv : LL.vec ⟨s, hsN⟩
    · have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      calc P.mu ⟨s + 1, hs⟩ ⟨mv, hmv⟩ ≤ P.mu ⟨s, by omega⟩ ⟨mv, hmv⟩ := hstr.1 _
        _ ≤ 0 := ih (by omega) ⟨mv, hmv⟩ (show s ≤ mv by omega)
    · have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      obtain _ | mv := mv
      · omega
      · calc P.mu ⟨s + 1, hs⟩ ⟨mv + 1, hmv⟩ ≤ P.mu ⟨s, by omega⟩ ⟨mv, by omega⟩ := hstr.2.1 ⟨mv, by omega⟩ hmv
          _ ≤ 0 := ih (by omega) ⟨mv, by omega⟩ (show s ≤ mv by omega)

def dplus (LL : Letters (Fin N)) (dd : Fin N → ℕ) (s : ℕ) : ℕ :=
  ∑ l : Fin N, if l.val < s ∧ LL.vec l = true then dd l else 0

def dminus (LL : Letters (Fin N)) (dd : Fin N → ℕ) (s : ℕ) : ℕ :=
  ∑ l : Fin N, if l.val < s ∧ LL.vec l = false then dd l else 0

theorem dsum_succ (f : Fin N → Prop) [DecidablePred f] (dd : Fin N → ℕ) (s : ℕ) (hs : s < N) :
    (∑ l : Fin N, if l.val < s + 1 ∧ f l then dd l else 0) =
      (∑ l : Fin N, if l.val < s ∧ f l then dd l else 0) + if f ⟨s, hs⟩ then dd ⟨s, hs⟩ else 0 := by
  have key : ∀ l : Fin N, (if l.val < s + 1 ∧ f l then dd l else 0) =
      (if l.val < s ∧ f l then dd l else 0) + (if l = ⟨s, hs⟩ then (if f ⟨s, hs⟩ then dd ⟨s, hs⟩ else 0) else 0) := by
    intro l
    by_cases h1 : l = ⟨s, hs⟩
    · subst h1
      simp
    · have hne : l.val ≠ s := fun h => h1 (Fin.ext h)
      have hiff : (l.val < s + 1 ∧ f l) ↔ (l.val < s ∧ f l) :=
        ⟨fun ⟨a, b⟩ => ⟨by omega, b⟩, fun ⟨a, b⟩ => ⟨by omega, b⟩⟩
      simp only [hiff, h1, if_false, add_zero]
  rw [Finset.sum_congr rfl (fun l _ => key l), Finset.sum_add_distrib]
  simp

theorem strip_le_add {nu mu : Fin n → ℤ} {b : ℕ} (h : HStrip nu mu b) (m : Fin n) : mu m ≤ nu m + b := by
  have h1 : mu m - nu m ≤ ∑ a, (mu a - nu a) :=
    Finset.single_le_sum (f := fun a => mu a - nu a) (fun a _ => sub_nonneg.mpr (h.1 a)) (Finset.mem_univ m)
  rw [h.2.2] at h1
  linarith

theorem mu_le_dplus (P : PPath n N LL dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin n), P.mu ⟨s, hs⟩ m ≤ (dplus LL dd s : ℤ) := by
  intro s
  induction s with
  | zero =>
    intro hs m
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
    rw [h0, P.zero]
    simp
  | succ s ih =>
    intro hs m
    have hsN : s < N := by omega
    have hd : (∑ l : Fin N, if l.val < s + 1 ∧ LL.vec l = true then dd l else 0) =
        (∑ l : Fin N, if l.val < s ∧ LL.vec l = true then dd l else 0) +
          if LL.vec ⟨s, hsN⟩ = true then dd ⟨s, hsN⟩ else 0 :=
      dsum_succ (fun l : Fin N => LL.vec l = true) dd s hsN
    have h1 := ih (by omega) m
    cases hv : LL.vec ⟨s, hsN⟩
    · have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      have h2 : dplus LL dd (s + 1) = dplus LL dd s := by
        unfold dplus
        rw [hd, hv]
        simp
      rw [h2]
      exact (hstr.1 m).trans h1
    · have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      have h2 : dplus LL dd (s + 1) = dplus LL dd s + dd ⟨s, hsN⟩ := by
        unfold dplus
        rw [hd, hv]
        simp
      have h3 := strip_le_add hstr m
      rw [h2]
      push_cast
      linarith

theorem neg_dminus_le_mu (P : PPath n N LL dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin n), -(dminus LL dd s : ℤ) ≤ P.mu ⟨s, hs⟩ m := by
  intro s
  induction s with
  | zero =>
    intro hs m
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
    rw [h0, P.zero]
    simp
  | succ s ih =>
    intro hs m
    have hsN : s < N := by omega
    have hd : (∑ l : Fin N, if l.val < s + 1 ∧ LL.vec l = false then dd l else 0) =
        (∑ l : Fin N, if l.val < s ∧ LL.vec l = false then dd l else 0) +
          if LL.vec ⟨s, hsN⟩ = false then dd ⟨s, hsN⟩ else 0 :=
      dsum_succ (fun l : Fin N => LL.vec l = false) dd s hsN
    have h1 := ih (by omega) m
    cases hv : LL.vec ⟨s, hsN⟩
    · have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      have h2 : dminus LL dd (s + 1) = dminus LL dd s + dd ⟨s, hsN⟩ := by
        unfold dminus
        rw [hd, hv]
        simp
      have h3 := strip_le_add hstr m
      rw [h2]
      push_cast
      linarith
    · have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      have h2 : dminus LL dd (s + 1) = dminus LL dd s := by
        unfold dminus
        rw [hd, hv]
        simp
      rw [h2]
      exact h1.trans (hstr.1 m)

def vcount (LL : Letters (Fin N)) (t s : ℕ) : ℕ :=
  (Finset.univ.filter fun l : Fin N => t ≤ l.val ∧ l.val < s ∧ LL.vec l = true).card

theorem vcount_self (LL : Letters (Fin N)) (t : ℕ) : vcount LL t t = 0 := by
  unfold vcount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro l _ h
  obtain ⟨h1, h2, -⟩ := h
  omega

theorem vcount_succ (LL : Letters (Fin N)) (t s : ℕ) (hts : t ≤ s) (hs : s < N) :
    vcount LL t (s + 1) = vcount LL t s + if LL.vec ⟨s, hs⟩ = true then 1 else 0 := by
  unfold vcount
  by_cases hv : LL.vec ⟨s, hs⟩ = true
  · rw [if_pos hv]
    have hset : (Finset.univ.filter fun l : Fin N => t ≤ l.val ∧ l.val < s + 1 ∧ LL.vec l = true) =
        insert ⟨s, hs⟩ (Finset.univ.filter fun l : Fin N => t ≤ l.val ∧ l.val < s ∧ LL.vec l = true) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2, h3⟩
        by_cases hl : l.val = s
        · left
          exact Fin.ext hl
        · right
          exact ⟨h1, by omega, h3⟩
      · rintro (rfl | ⟨h1, h2, h3⟩)
        · exact ⟨hts, Nat.lt_succ_self s, hv⟩
        · exact ⟨h1, by omega, h3⟩
    rw [hset, Finset.card_insert_of_notMem]
    simp
  · rw [if_neg hv, add_zero]
    congr 1
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, h3⟩
      by_contra hc
      have hl : l = ⟨s, hs⟩ := Fin.ext (show l.val = s by omega)
      subst hl
      exact hv h3
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by omega, h3⟩

theorem row_back (P : PPath n N LL dd) (t : ℕ) :
    ∀ (s : ℕ) (_hts : t ≤ s) (hs : s < N + 1) (m m' : Fin n), m'.val = m.val + vcount LL t s →
      P.mu ⟨s, hs⟩ m' ≤ P.mu ⟨t, by omega⟩ m := by
  intro s hts
  induction s, hts using Nat.le_induction with
  | base =>
    intro hs m m' hm
    rw [vcount_self, add_zero] at hm
    have he : m' = m := Fin.ext hm
    subst he
    exact le_refl _
  | succ s hts ih =>
    intro hs m m' hm
    have hsN : s < N := by omega
    rw [vcount_succ LL t s hts hsN] at hm
    cases hv : LL.vec ⟨s, hsN⟩
    · rw [hv] at hm
      simp only [Bool.false_eq_true, if_false, add_zero] at hm
      have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      exact (hstr.1 m').trans (ih (by omega) m m' hm)
    · rw [hv] at hm
      simp only [if_true] at hm
      have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      have hlt := m'.isLt
      have ha : m.val + vcount LL t s < n := by omega
      have he : m' = ⟨m.val + vcount LL t s + 1, by omega⟩ := Fin.ext hm
      rw [he]
      exact (hstr.2.1 ⟨m.val + vcount LL t s, ha⟩ (by simp only; omega)).trans
        (ih (by omega) m ⟨m.val + vcount LL t s, ha⟩ rfl)

end Formalism.MainNotions.SelectionLemmas.Pf.T
