import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.SignChain

theorem sum_toggle_eq_zero {α : Type*} [DecidableEq α] (T : Finset (Finset α)) (t : Finset α → α)
    (h1 : ∀ c ∈ T, insert (t c) c ∈ T) (h2 : ∀ c ∈ T, c.erase (t c) ∈ T)
    (h3 : ∀ c ∈ T, t (insert (t c) c) = t c) (h4 : ∀ c ∈ T, t (c.erase (t c)) = t c) :
    ∑ c ∈ T, (-1 : ℝ) ^ c.card = 0 := by
  refine Finset.sum_involution (fun c _ => if t c ∈ c then c.erase (t c) else insert (t c) c)
    ?_ ?_ ?_ ?_
  · intro c hc
    by_cases h : t c ∈ c
    · have hpos : 0 < c.card := Finset.card_pos.mpr ⟨_, h⟩
      obtain ⟨n, hn⟩ : ∃ n, c.card = n + 1 := ⟨c.card - 1, by omega⟩
      simp only [h, if_true]
      rw [Finset.card_erase_of_mem h, hn]
      simp [pow_succ]
    · simp only [h, if_false]
      rw [Finset.card_insert_of_notMem h]
      simp [pow_succ]
  · intro c hc _ heq
    by_cases h : t c ∈ c
    · simp only [h, if_true] at heq
      have h' : t c ∈ c.erase (t c) := by rw [heq]; exact h
      exact Finset.notMem_erase (t c) c h'
    · simp only [h, if_false] at heq
      have h' : t c ∈ insert (t c) c := Finset.mem_insert_self _ _
      rw [heq] at h'
      exact h h'
  · intro c hc
    by_cases h : t c ∈ c
    · simp only [h, if_true]; exact h2 c hc
    · simp only [h, if_false]; exact h1 c hc
  · intro c hc
    by_cases h : t c ∈ c
    · simp only [h, if_true]
      rw [h4 c hc]
      simp [Finset.insert_erase h]
    · simp only [h, if_false]
      rw [h3 c hc]
      simp [Finset.erase_insert h]

variable {m : ℕ}

def rk (e : Fin m → SignType) : ℕ := (Finset.univ.filter fun j => e j ≠ 0).card

theorem rk_le {x y : Fin m → SignType} (h : SLe x y) : rk x ≤ rk y := by
  refine Finset.card_le_card fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  rw [h j hj]; exact hj

theorem eq_of_rk_le {x y : Fin m → SignType} (h : SLe x y) (h' : rk y ≤ rk x) : x = y := by
  have hsub : (Finset.univ.filter fun j => x j ≠ 0) ⊆ Finset.univ.filter fun j => y j ≠ 0 := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rw [h j hj]; exact hj
  have hs := Finset.eq_of_subset_of_card_le hsub h'
  funext j
  by_cases hx : x j = 0
  · have hj : j ∉ Finset.univ.filter fun j => y j ≠ 0 := by rw [← hs]; simp [hx]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
    rw [hx, hj]
  · exact (h j hx).symm

theorem sle_refl (x : Fin m → SignType) : SLe x x := fun _ _ => rfl

theorem sle_trans {x y z : Fin m → SignType} (h : SLe x y) (h' : SLe y z) : SLe x z := by
  intro j hj
  have := h j hj
  rw [h' j (by rw [this]; exact hj), this]

theorem zero_sle (x : Fin m → SignType) : SLe 0 x := fun _ h => absurd rfl h

open Classical in

noncomputable def lo (S : Finset (Fin m → SignType)) : Fin m → SignType :=
  if h : S.Nonempty then (S.exists_min_image rk h).choose else 0

open Classical in

noncomputable def hi (S : Finset (Fin m → SignType)) : Fin m → SignType :=
  if h : S.Nonempty then (S.exists_max_image rk h).choose else 0

theorem lo_mem {S : Finset (Fin m → SignType)} (h : S.Nonempty) : lo S ∈ S := by
  rw [lo, dif_pos h]; exact (S.exists_min_image rk h).choose_spec.1

theorem hi_mem {S : Finset (Fin m → SignType)} (h : S.Nonempty) : hi S ∈ S := by
  rw [hi, dif_pos h]; exact (S.exists_max_image rk h).choose_spec.1

theorem lo_sle {S : Finset (Fin m → SignType)} (h : S.Nonempty)
    (hc : IsChain SLe (↑S : Set (Fin m → SignType))) {x} (hx : x ∈ S) : SLe (lo S) x := by
  have hmin : rk (lo S) ≤ rk x := by
    rw [lo, dif_pos h]; exact (S.exists_min_image rk h).choose_spec.2 x hx
  by_cases hne : lo S = x
  · rw [hne]; exact sle_refl x
  · rcases hc (Finset.mem_coe.mpr (lo_mem h)) (Finset.mem_coe.mpr hx) hne with h' | h'
    · exact h'
    · rw [eq_of_rk_le h' hmin]; exact sle_refl _

theorem sle_hi {S : Finset (Fin m → SignType)} (h : S.Nonempty)
    (hc : IsChain SLe (↑S : Set (Fin m → SignType))) {x} (hx : x ∈ S) : SLe x (hi S) := by
  have hmax : rk x ≤ rk (hi S) := by
    rw [hi, dif_pos h]; exact (S.exists_max_image rk h).choose_spec.2 x hx
  by_cases hne : hi S = x
  · rw [hne]; exact sle_refl x
  · rcases hc (Finset.mem_coe.mpr (hi_mem h)) (Finset.mem_coe.mpr hx) hne with h' | h'
    · rw [eq_of_rk_le h' hmax]; exact sle_refl _
    · exact h'

theorem sdot_update (e : Fin m → SignType) (a : Fin m → ℝ) (i : Fin m) (w : SignType) :
    sdot (Function.update e i w) a = sdot e a + ((w : ℝ) * a i - (e i : ℝ) * a i) := by
  unfold sdot
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
    ← Finset.add_sum_erase (a := i) _ (fun j => (e j : ℝ) * a j) (Finset.mem_univ i)]
  have : ∑ x ∈ Finset.univ.erase i, ((Function.update e i w x : SignType) : ℝ) * a x =
      ∑ x ∈ Finset.univ.erase i, (e x : ℝ) * a x :=
    Finset.sum_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [this, Function.update_self]
  ring

theorem sdot_zero (a : Fin m → ℝ) : sdot (0 : Fin m → SignType) a = 0 := by
  simp [sdot]

noncomputable def tg (ε : SignType) (i : Fin m) (c : Finset (Fin m → SignType)) : Fin m → SignType :=
  if (c.filter fun e => e i = -ε).Nonempty then Function.update (lo (c.filter fun e => e i = -ε)) i 0
  else Function.update (hi (insert 0 (c.filter fun e => e i = 0))) i ε

theorem tg_congr (ε : SignType) (i : Fin m) {c c' : Finset (Fin m → SignType)}
    (h1 : (c.filter fun e => e i = -ε) = c'.filter fun e => e i = -ε)
    (h2 : ¬ (c.filter fun e => e i = -ε).Nonempty →
      (c.filter fun e => e i = 0) = c'.filter fun e => e i = 0) : tg ε i c = tg ε i c' := by
  unfold tg
  by_cases h : (c.filter fun e => e i = -ε).Nonempty
  · rw [if_pos h, if_pos (h1 ▸ h), h1]
  · rw [if_neg h, if_neg (h1 ▸ h), h2 h]

theorem neg_ne_self {ε : SignType} (h : ε ≠ 0) : ε ≠ -ε := by
  revert h; cases ε <;> decide

theorem neg_ne_zero' {ε : SignType} (h : ε ≠ 0) : -ε ≠ 0 := by
  revert h; cases ε <;> decide

theorem eq_of_ne {ε x : SignType} (h : ε ≠ 0) (h0 : x ≠ 0) (h1 : x ≠ -ε) : x = ε := by
  revert h h0 h1; cases ε <;> cases x <;> decide

theorem tg_spec_neg {ε : SignType} (hε : ε ≠ 0) {i : Fin m} {c : Finset (Fin m → SignType)}
    (hc : IsChain SLe (↑c : Set (Fin m → SignType))) (hN : (c.filter fun e => e i = -ε).Nonempty) :
    ∃ e ∈ c, e i = -ε ∧ tg ε i c = Function.update e i 0 ∧
      ∀ x ∈ c, SLe (tg ε i c) x ∨ SLe x (tg ε i c) := by
  have hcN : IsChain SLe (↑(c.filter fun e => e i = -ε) : Set (Fin m → SignType)) :=
    hc.mono (by intro x hx; exact (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1)
  obtain ⟨hec, hei⟩ := Finset.mem_filter.mp (lo_mem hN)
  have hmin := fun x (hx : x ∈ c.filter fun e => e i = -ε) => lo_sle hN hcN hx
  set e := lo (c.filter fun e => e i = -ε) with he
  have ht : tg ε i c = Function.update e i 0 := by rw [tg, if_pos hN]
  refine ⟨e, hec, hei, ht, fun x hx => ?_⟩
  rw [ht]
  have hte : SLe (Function.update e i 0) e := by
    intro j hj
    by_cases hji : j = i
    · subst hji; simp at hj
    · rw [Function.update_of_ne hji]
  by_cases hxi : x i = -ε
  · exact Or.inl (sle_trans hte (hmin x (Finset.mem_filter.mpr ⟨hx, hxi⟩)))
  · have hxe : SLe x e := by
      by_cases hne : e = x
      · rw [hne]; exact sle_refl x
      · rcases hc (Finset.mem_coe.mpr hec) (Finset.mem_coe.mpr hx) hne with h' | h'
        · exact absurd ((h' i (by rw [hei]; exact neg_ne_zero' hε)).trans hei) hxi
        · exact h'
    refine Or.inr fun j hj => ?_
    by_cases hji : j = i
    · subst hji
      exact absurd ((hxe j hj).symm.trans hei) hxi
    · rw [Function.update_of_ne hji]; exact hxe j hj

theorem tg_spec_pos {ε : SignType} (hε : ε ≠ 0) {i : Fin m} {c : Finset (Fin m → SignType)}
    (hc : IsChain SLe (↑c : Set (Fin m → SignType))) (hN : ¬ (c.filter fun e => e i = -ε).Nonempty) :
    ∃ e, (e = 0 ∨ e ∈ c) ∧ e i = 0 ∧ tg ε i c = Function.update e i ε ∧
      ∀ x ∈ c, SLe (tg ε i c) x ∨ SLe x (tg ε i c) := by
  have hZ : (insert 0 (c.filter fun e => e i = 0)).Nonempty := Finset.insert_nonempty _ _
  have hcZ : IsChain SLe (↑(insert 0 (c.filter fun e => e i = 0)) : Set (Fin m → SignType)) := by
    rw [Finset.coe_insert]
    refine IsChain.insert (hc.mono (by
      intro x hx; exact (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1)) fun b _ _ => Or.inl (zero_sle b)
  have hmem := hi_mem hZ
  have hmax := fun x (hx : x ∈ insert 0 (c.filter fun e => e i = 0)) => sle_hi hZ hcZ hx
  set e := hi (insert 0 (c.filter fun e => e i = 0)) with he
  have ht : tg ε i c = Function.update e i ε := by rw [tg, if_neg hN]
  have hor : e = 0 ∨ (e ∈ c ∧ e i = 0) := by
    rcases Finset.mem_insert.mp hmem with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_filter.mp h)
  have hei : e i = 0 := by
    rcases hor with h | h
    · rw [h]; rfl
    · exact h.2
  refine ⟨e, hor.imp id And.left, hei, ht, fun x hx => ?_⟩
  rw [ht]
  have het : SLe e (Function.update e i ε) := by
    intro j hj
    have hji : j ≠ i := by rintro rfl; exact hj hei
    rw [Function.update_of_ne hji]
  by_cases hx0 : x i = 0
  · exact Or.inr (sle_trans (hmax x (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hx, hx0⟩))) het)
  · have hxn : x i ≠ -ε := fun h =>
      hN ⟨x, Finset.mem_filter.mpr ⟨hx, h⟩⟩
    have hxε : x i = ε := eq_of_ne hε hx0 hxn
    have hex : SLe e x := by
      rcases hor with h | h
      · rw [h]; exact zero_sle x
      · have hne : e ≠ x := by
          intro h'; rw [h'] at hei; exact hx0 hei
        rcases hc (Finset.mem_coe.mpr h.1) (Finset.mem_coe.mpr hx) hne with h' | h'
        · exact h'
        · exact absurd ((h' i hx0).symm.trans hei) hx0
    refine Or.inl fun j hj => ?_
    by_cases hji : j = i
    · subst hji; rw [Function.update_self]; exact hxε
    · rw [Function.update_of_ne hji] at hj ⊢; exact hex j hj

theorem gam_eq_zero (y : (Fin m → SignType) → ℝ) (M : ℝ) (a : Fin m → ℝ) (hy : ∀ e, |y e| ≤ M)
    (i : Fin m) (hi' : 2 * M < |a i|) : gam y a = 0 := by
  classical
  have hM : 0 ≤ M := (abs_nonneg _).trans (hy 0)
  obtain ⟨ε, hε, hp, hn⟩ : ∃ ε : SignType, ε ≠ 0 ∧ (ε : ℝ) * a i = |a i| ∧
      ((-ε : SignType) : ℝ) * a i = -|a i| := by
    rcases lt_trichotomy (a i) 0 with h | h | h
    · exact ⟨-1, by decide, by simp [abs_of_neg h], by simp [abs_of_neg h]⟩
    · rw [h] at hi'; simp at hi'; linarith
    · exact ⟨1, by decide, by simp [abs_of_pos h], by simp [abs_of_pos h]⟩
  have hb := fun e => abs_le.mp (hy e)

  have era : ∀ e : Fin m → SignType, e i = -ε → y e < sdot e a →
      y (Function.update e i 0) < sdot (Function.update e i 0) a := by
    intro e he hv
    rw [sdot_update, he, hn]
    have h1 := hb e
    have h2 := hb (Function.update e i 0)
    simp only [SignType.coe_zero, zero_mul]
    linarith [h1.1, h1.2, h2.1, h2.2]
  have era0 : ∀ e : Fin m → SignType, e i = -ε → y e < sdot e a → Function.update e i 0 ≠ 0 := by
    intro e he hv h0
    have h1 := sdot_update e a i 0
    rw [h0, sdot_zero, he, hn] at h1
    simp only [SignType.coe_zero, zero_mul] at h1
    have h2 := hb e
    linarith [h2.1, h2.2]
  have up : ∀ e : Fin m → SignType, e i = 0 → (e = 0 ∨ y e < sdot e a) →
      y (Function.update e i ε) < sdot (Function.update e i ε) a := by
    intro e he hv
    rw [sdot_update, he, hp]
    simp only [SignType.coe_zero, zero_mul]
    have h2 := hb (Function.update e i ε)
    rcases hv with h | h
    · subst h; rw [sdot_zero]; linarith [h2.1, h2.2]
    · have h1 := hb e
      linarith [h1.1, h1.2, h2.1, h2.2]
  have up0 : ∀ e : Fin m → SignType, Function.update e i ε ≠ 0 := by
    intro e h0
    have := congrFun h0 i
    rw [Function.update_self] at this
    exact hε this
  let T : Finset (Finset (Fin m → SignType)) :=
    ((Finset.univ : Finset (Finset (Fin m → SignType))).filter
      (fun s : Finset (Fin m → SignType) =>
        0 ∉ s ∧ IsChain SLe (↑s : Set (Fin m → SignType)) ∧ True)).filter
      fun s => ∀ e ∈ s, y e < sdot e a
  have memT : ∀ c, c ∈ T ↔ (0 ∉ c ∧ IsChain SLe (↑c : Set (Fin m → SignType))) ∧
      ∀ e ∈ c, y e < sdot e a := by
    intro c; simp [T]
  have hgam : gam y a = ∑ c ∈ T, (-1 : ℝ) ^ c.card := by
    simp only [T]
    rw [Finset.sum_filter]
    unfold gam gamOn
    refine Finset.sum_congr (by ext s; simp) fun c _ => ?_
    rw [Finset.prod_ite_zero]
    by_cases h : ∀ e ∈ c, y e < sdot e a
    · simp [h]
    · simp [h]

  have key : ∀ c ∈ T, tg ε i c ≠ 0 ∧ y (tg ε i c) < sdot (tg ε i c) a ∧ tg ε i c i ≠ -ε ∧
      (¬ (c.filter fun e => e i = -ε).Nonempty → tg ε i c i ≠ 0) ∧
      ∀ x ∈ c, SLe (tg ε i c) x ∨ SLe x (tg ε i c) := by
    intro c hc
    obtain ⟨⟨h0, hch⟩, hv⟩ := (memT c).mp hc
    by_cases hN : (c.filter fun e => e i = -ε).Nonempty
    · obtain ⟨e, hec, hei, ht, hcmp⟩ := tg_spec_neg hε hch hN
      refine ⟨?_, ?_, ?_, fun h => absurd hN h, hcmp⟩
      · rw [ht]; exact era0 e hei (hv e hec)
      · rw [ht]; exact era e hei (hv e hec)
      · rw [ht, Function.update_self]; exact (neg_ne_zero' hε).symm
    · obtain ⟨e, hec, hei, ht, hcmp⟩ := tg_spec_pos hε hch hN
      refine ⟨?_, ?_, ?_, fun _ => ?_, hcmp⟩
      · rw [ht]; exact up0 e
      · rw [ht]; exact up e hei (hec.imp id (hv e))
      · rw [ht, Function.update_self]; exact neg_ne_self hε
      · rw [ht, Function.update_self]; exact hε
  rw [hgam]
  refine sum_toggle_eq_zero T (tg ε i) ?_ ?_ ?_ ?_
  · intro c hc
    obtain ⟨hne, hvt, -, -, hcmp⟩ := key c hc
    obtain ⟨⟨h0, hch⟩, hv⟩ := (memT c).mp hc
    refine (memT _).mpr ⟨⟨?_, ?_⟩, ?_⟩
    · intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hne h.symm
      · exact h0 h
    · rw [Finset.coe_insert]
      exact hch.insert fun b hb _ => hcmp b (Finset.mem_coe.mp hb)
    · intro e he
      rcases Finset.mem_insert.mp he with h | h
      · rw [h]; exact hvt
      · exact hv e h
  · intro c hc
    obtain ⟨⟨h0, hch⟩, hv⟩ := (memT c).mp hc
    refine (memT _).mpr ⟨⟨fun h => h0 (Finset.mem_of_mem_erase h), ?_⟩,
      fun e he => hv e (Finset.mem_of_mem_erase he)⟩
    exact hch.mono (by
      intro x hx; exact Finset.mem_coe.mpr (Finset.mem_of_mem_erase (Finset.mem_coe.mp hx)))
  · intro c hc
    obtain ⟨-, -, hneg, hzero, -⟩ := key c hc
    refine (tg_congr ε i ?_ ?_).symm.symm
    · rw [Finset.filter_insert, if_neg hneg]
    · intro hN
      rw [Finset.filter_insert, if_neg hneg] at hN
      rw [Finset.filter_insert, if_neg (hzero hN)]
  · intro c hc
    obtain ⟨-, -, hneg, hzero, -⟩ := key c hc
    have hf : ∀ (p : (Fin m → SignType) → Prop) [DecidablePred p], ¬ p (tg ε i c) →
        (c.erase (tg ε i c)).filter p = c.filter p := by
      intro p _ hp
      rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
      simp [hp]
    refine tg_congr ε i ?_ ?_
    · exact hf _ hneg
    · intro hN
      rw [hf _ hneg] at hN
      exact hf _ (hzero hN)

theorem gam_support : ∀ m : ℕ, ∀ (y : (Fin m → SignType) → ℝ) (M : ℝ) a, (∀ e, |y e| ≤ M) →
    gam y a ≠ 0 → ∀ i, |a i| ≤ 2 * M := by
  intro m y M a hy h i
  by_contra hi'
  exact h (gam_eq_zero y M a hy i (not_le.mp hi'))

end GlobalTheory.CompanionTheory.SignChain
