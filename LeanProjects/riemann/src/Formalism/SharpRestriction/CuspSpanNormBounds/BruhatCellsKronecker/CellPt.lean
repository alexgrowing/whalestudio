import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellDef

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.MainNotions.S

theorem cpt_nat {K : Type} [Field K] : ∀ (n : ℕ) (σ : ℕ → ℕ) (τ : ℕ → K),
    (∀ i, i < n → σ i < n) → (∀ i, i < n → ∀ j, j < n → σ i = σ j → i = j) → (∀ v, v < n → ∃ i, i < n ∧ σ i = v) →
    (∀ i, i < n → τ i ≠ 0) →
    (∀ c b, c < b → b < n → σ c = σ b + 1 → b = c + 1 ∧ τ b = τ c) →
    ∃ bs : List (K × ℕ), (∀ x ∈ bs, x.1 ≠ 0 ∧ 1 ≤ x.2) ∧ (bs.map Prod.snd).sum = n ∧
      ∀ a, a < n → ∀ b, b < n → ptEntry bs a b = if a = σ b then τ b else 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ τ hmap hinj hsurj hτ hP
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      exact ⟨[], by simp, by simp, fun a ha => absurd ha (Nat.not_lt_zero a)⟩
    · obtain ⟨s, hs⟩ : ∃ s, s = σ 0 + 1 := ⟨_, rfl⟩
      have hsn : s ≤ n := by have := hmap 0 hpos; omega
      have hs1 : 1 ≤ s := by omega

      have c1 : ∀ i, i < s → σ i = s - 1 - i ∧ τ i = τ 0 := by
        intro i
        induction i using Nat.strong_induction_on with
        | _ i ihi =>
          intro hi
          rcases Nat.eq_zero_or_pos i with hi0 | hipos
          · subst hi0
            exact ⟨by omega, rfl⟩
          · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
            obtain ⟨e1, e2⟩ := ihi i' (by omega) (by omega)
            obtain ⟨b, hbn, hb⟩ := hsurj (s - 1 - (i' + 1)) (by omega)
            have hbi : i' + 1 ≤ b := by
              by_contra hlt
              have := (ihi b (by omega) (by omega)).1
              omega
            obtain ⟨f1, f2⟩ := hP i' b (by omega) hbn (by omega)
            subst f1
            exact ⟨hb, f2.trans e2⟩

      have c2 : ∀ i, s ≤ i → i < n → s ≤ σ i := by
        intro i hi hin
        by_contra hlt
        have hj : s - 1 - σ i < s := by omega
        have e := (c1 (s - 1 - σ i) hj).1
        have := hinj i hin (s - 1 - σ i) (by omega) (by omega)
        omega
      obtain ⟨bs, hb1, hb2, hb3⟩ := ih (n - s) (by omega) (fun i => σ (i + s) - s) (fun i => τ (i + s))
        (fun i hi => by
          have h1 := hmap (i + s) (by omega)
          have h2 := c2 (i + s) (by omega) (by omega)
          show σ (i + s) - s < n - s
          omega)
        (fun i hi j hj hij => by
          have h1 := c2 (i + s) (by omega) (by omega)
          have h2 := c2 (j + s) (by omega) (by omega)
          have h3 : σ (i + s) - s = σ (j + s) - s := hij
          have := hinj (i + s) (by omega) (j + s) (by omega) (by omega)
          omega)
        (fun v hv => by
          obtain ⟨i, hin, hi⟩ := hsurj (v + s) (by omega)
          have his : s ≤ i := by
            by_contra hlt
            have := (c1 i (by omega)).1
            omega
          refine ⟨i - s, by omega, ?_⟩
          show σ (i - s + s) - s = v
          rw [Nat.sub_add_cancel his, hi]
          omega)
        (fun i hi => hτ (i + s) (by omega))
        (fun c b hcb hbn hv => by
          have h1 := c2 (c + s) (by omega) (by omega)
          have h2 := c2 (b + s) (by omega) (by omega)
          have h3 : σ (c + s) - s = σ (b + s) - s + 1 := hv
          obtain ⟨f1, f2⟩ := hP (c + s) (b + s) (by omega) (by omega) (by omega)
          exact ⟨by omega, f2⟩)
      refine ⟨(τ 0, s) :: bs, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨hτ 0 hpos, hs1⟩
        · exact hb1 x hx
      · simp only [List.map_cons, List.sum_cons, hb2]
        omega
      · intro a ha b hb
        simp only [ptEntry]
        by_cases h1 : a < s ∧ b < s
        · rw [if_pos h1]
          obtain ⟨e1, e2⟩ := c1 b h1.2
          by_cases h2 : a + b + 1 = s
          · rw [if_pos h2, if_pos (by omega), e2]
          · rw [if_neg h2, if_neg (by omega)]
        · rw [if_neg h1]
          by_cases h2 : s ≤ a ∧ s ≤ b
          · rw [if_pos h2, hb3 (a - s) (by omega) (b - s) (by omega)]
            have e0 : b - s + s = b := Nat.sub_add_cancel h2.2
            have h3 := c2 b h2.2 hb
            simp only [e0]
            by_cases h4 : a = σ b
            · rw [if_pos h4, if_pos (by omega)]
            · rw [if_neg h4, if_neg (by omega)]
          · rw [if_neg h2]
            rcases Nat.lt_or_ge b s with hbs | hbs
            · have := (c1 b hbs).1
              rw [if_neg (by omega)]
            · have := c2 b hbs hb
              rw [if_neg (by omega)]

theorem cell_point : MonomialMatrixIsPoint := by
  intro K _ n σ τ hσ hτ hP
  obtain ⟨bs, h1, h2, h3⟩ := cpt_nat n (fun i => if h : i < n then (σ ⟨i, h⟩).val else 0)
    (fun i => if h : i < n then τ ⟨i, h⟩ else 0)
    (fun i hi => by simp only [dif_pos hi]; exact (σ ⟨i, hi⟩).isLt)
    (fun i hi j hj hij => by
      simp only [dif_pos hi, dif_pos hj] at hij
      have := hσ.1 (Fin.ext hij)
      exact congrArg Fin.val this)
    (fun v hv => by
      obtain ⟨i, hi⟩ := hσ.2 ⟨v, hv⟩
      refine ⟨i.val, i.isLt, ?_⟩
      simp only [dif_pos i.isLt, Fin.eta, hi])
    (fun i hi => by simp only [dif_pos hi]; exact hτ _)
    (fun c b hcb hbn hv => by
      have hcn : c < n := lt_trans hcb hbn
      simp only [dif_pos hcn, dif_pos hbn] at hv ⊢
      exact hP ⟨c, hcn⟩ ⟨b, hbn⟩ hcb hv)
  refine ⟨⟨bs, h1, h2⟩, ?_⟩
  ext a b
  show ptEntry bs a.val b.val = mono σ τ a b
  rw [h3 a.val a.isLt b.val b.isLt]
  simp only [dif_pos b.isLt, Fin.eta, mono, Fin.ext_iff]

end Formalism.MainNotions.BridgeLemma

end
