import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.RestCountUpOfSTop

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Function

variable {s r : ℕ}

theorem strip_first [NeZero r] {nu mu : Fin r → ℤ} {g : ℕ} (h : Strip nu mu g) : nu 0 ≤ mu 0 + g := by
  obtain ⟨h1, -, h3⟩ := h
  have hs : ∑ i, (nu i - mu i) = g := by
    rw [Finset.sum_sub_distrib]
    exact h3
  have h0 := Finset.single_le_sum (f := fun i => nu i - mu i) (fun i _ => sub_nonneg.mpr (h1 i))
    (Finset.mem_univ (0 : Fin r))
  linarith

theorem sum_lt_succ (f : Fin s → ℤ) (i : Fin s) :
    (∑ x : Fin s, if x.val < i.val + 1 then f x else 0) = (∑ x : Fin s, if x.val < i.val then f x else 0) + f i := by
  have hpt : ∀ x : Fin s, (if x.val < i.val + 1 then f x else 0) =
      (if x.val < i.val then f x else 0) + (if x = i then f x else 0) := by
    intro x
    by_cases h1 : x.val < i.val
    · have h2 : x ≠ i := fun h => by rw [h] at h1; exact lt_irrefl _ h1
      have h5 : x.val < i.val + 1 := by omega
      simp [h1, h2, h5]
    · by_cases h3 : x = i
      · subst h3
        simp
      · have h4 : ¬ x.val < i.val + 1 := by
          intro h
          apply h3
          apply Fin.ext
          omega
        simp [h1, h3, h4]
  rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem eventually_abs_le_half_add_of_doubling_bounds [NeZero r] {LLv : ChainLetters (2 * s + 1)} {ka : Fin (2 * s + 1 + 1) → Fin r → ℤ}
    (hv : ∀ a, LLv.vec a = decide (a.val % 2 = 0)) (hch : IsChain LLv ka) (m : ℕ) (hm : m < 2 * s + 1) :
    ka ⟨m + 1, by omega⟩ 0 ≤ ka ⟨m, by omega⟩ 0 + (if m % 2 = 0 then (LLv.deg ⟨m, hm⟩ : ℤ) else 0) := by
  have h := hch.2 ⟨m, hm⟩
  have e1 : (⟨m, hm⟩ : Fin (2 * s + 1)).succ = ⟨m + 1, by omega⟩ := rfl
  have e2 : (⟨m, hm⟩ : Fin (2 * s + 1)).castSucc = ⟨m, by omega⟩ := rfl
  rw [e1, e2, hv] at h
  by_cases hpar : m % 2 = 0
  · simp [hpar] at h ⊢
    exact strip_first h
  · simp [hpar] at h ⊢
    exact h.1 0

theorem row_even [NeZero r] {LLv : ChainLetters (2 * s + 1)} {ka : Fin (2 * s + 1 + 1) → Fin r → ℤ}
    (hv : ∀ a, LLv.vec a = decide (a.val % 2 = 0)) (hch : IsChain LLv ka) :
    ∀ (n : ℕ) (hn : n ≤ s), ka ⟨2 * n, by omega⟩ 0 ≤
      ∑ l : Fin s, if l.val < n then (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ) else 0 := by
  intro n
  induction n with
  | zero =>
    intro hn
    have h0 : ka ⟨2 * 0, by omega⟩ = 0 := hch.1
    rw [h0]
    simp
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have hs1 := hch.2 ⟨2 * n, by omega⟩
    rw [if_pos (by rw [hv]; simp)] at hs1
    have hs2 := hch.2 ⟨2 * n + 1, by omega⟩
    rw [if_neg (by rw [hv]; simp)] at hs2
    have a1 : ka ⟨2 * n + 1, by omega⟩ 0 ≤ ka ⟨2 * n, by omega⟩ 0 + (LLv.deg ⟨2 * n, by omega⟩ : ℤ) := strip_first hs1
    have a2 : ka ⟨2 * (n + 1), by omega⟩ 0 ≤ ka ⟨2 * n + 1, by omega⟩ 0 := hs2.1 0
    have hsum : (∑ l : Fin s, if l.val < n + 1 then (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ) else 0) =
        (∑ l : Fin s, if l.val < n then (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ) else 0) +
          (LLv.deg ⟨2 * n, by omega⟩ : ℤ) :=
      sum_lt_succ (fun l : Fin s => (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ)) ⟨n, by omega⟩
    rw [hsum]
    linarith

theorem row_odd [NeZero r] {LLv : ChainLetters (2 * s + 1)} {ka : Fin (2 * s + 1 + 1) → Fin r → ℤ}
    (hv : ∀ a, LLv.vec a = decide (a.val % 2 = 0)) (hch : IsChain LLv ka) (i : Fin s) :
    ka ⟨2 * i.val + 1, by omega⟩ 0 ≤
      ∑ l : Fin s, if l.val < i.val + 1 then (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ) else 0 := by
  have h1 := eventually_abs_le_half_add_of_doubling_bounds hv hch (2 * i.val) (by omega)
  rw [if_pos (by omega)] at h1
  have h3 := row_even hv hch i.val (by omega)
  have hsum : (∑ l : Fin s, if l.val < i.val + 1 then (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ) else 0) =
      (∑ l : Fin s, if l.val < i.val then (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ) else 0) +
        (LLv.deg ⟨2 * i.val, by omega⟩ : ℤ) :=
    sum_lt_succ (fun l : Fin s => (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ)) i
  rw [hsum]
  linarith

def SecondKernelAtLevel (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      ∀ i : Fin (segS X.TT j), i.val < (X.seg C0 CE1 CE2 j).sigma →
        (∑ l : Fin (segS X.TT j), if l.val < i.val + 1 then (b.w l : ℤ) else 0) ≤
          cap X.p (X.seg C0 CE1 CE2 j) b i.val ∧
        (∑ l : Fin (segS X.TT j), if l.val < i.val + 1 then (b.w l : ℤ) else 0) ≤
          cap X.p (X.seg C0 CE1 CE2 j) b (i.val + 1)

theorem sTopRows_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hK : SecondKernelAtLevel C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    STopRowsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD hH hc j m hm rz ry hd z hz i hi
  have h1 := row_odd (LLv := (BD C0 CE1 CE2 X j m z.1).lettersAt z.2.1.1 z.2.1.2) (fun a => rfl) hz.2.2.1 i
  have e : (∑ l : Fin (segS X.TT j), if l.val < i.val + 1 then
        (((BD C0 CE1 CE2 X j m z.1).lettersAt z.2.1.1 z.2.1.2).deg ⟨2 * l.val, by omega⟩ : ℤ) else 0) =
      ∑ l : Fin (segS X.TT j), if l.val < i.val + 1 then (z.1.w l : ℤ) else 0 := by
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l.val < i.val + 1
    · rw [if_pos hl, if_pos hl, levW, if_pos (by omega), jE_S _ _ (by omega), Nat.sub_zero]
    · rw [if_neg hl, if_neg hl]
  rw [e] at h1
  have h2 := hK X hD hH hc j z.1 hz.1.1 i hi
  exact ⟨le_trans h1 h2.1, le_trans h1 h2.2⟩

def LeadingRowsBeyondThreshold : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => SecondKernelAtLevel C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem restSTopRows_of (h : LeadingRowsBeyondThreshold) : RestSTopRows :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ hK => sTopRows_of hK) h

theorem upper_count_of_top_rows (hCD : ChainDimAt) (hNB : NumBranchAt) (h : LeadingRowsBeyondThreshold) : RestCountUp :=
  restCountUp_of_STop hCD hNB (restSTopRows_of h)

end Formalism.MainNotions.ColumnSystems.Pf
