import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiExistsStatement

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem hc_param_gap_ge_index (lam : Fin n → ℝ) (hlam : IsHCParam lam) (a b : Fin n) (hab : a ≤ b) :
    ((b : ℕ) : ℝ) - (a : ℕ) ≤ lam a - lam b := by

  have gap : ∀ i j : Fin n, i < j → lam j + 1 ≤ lam i := by
    intro i j hij
    obtain ⟨mi, hi⟩ := hlam.2 i
    obtain ⟨mj, hj⟩ := hlam.2 j
    have hlt : lam j < lam i := hlam.1 hij
    have h1 : (mj : ℝ) < mi := by linarith
    have h2 : mj < mi := by exact_mod_cast h1
    have h3 : (mj : ℝ) + 1 ≤ mi := by
      have := Int.add_one_le_of_lt h2
      exact_mod_cast this
    linarith
  have key : ∀ k : ℕ, ∀ c : Fin n, a ≤ c → (c : ℕ) = a + k → ((c : ℕ) : ℝ) - (a : ℕ) ≤ lam a - lam c := by
    intro k
    induction k with
    | zero =>
      intro c _ hc
      have : c = a := Fin.ext (by omega)
      subst this
      simp
    | succ k ih =>
      intro c hac hc
      have hc1 : (c : ℕ) - 1 < n := by omega
      let c' : Fin n := ⟨(c : ℕ) - 1, hc1⟩
      have hac' : a ≤ c' := Fin.le_def.mpr (by show (a : ℕ) ≤ (c : ℕ) - 1; omega)
      have hc' : (c' : ℕ) = a + k := by show (c : ℕ) - 1 = _; omega
      have h1 := ih c' hac' hc'
      have h2 := gap c' c (Fin.lt_def.mpr (by show (c : ℕ) - 1 < c; omega))
      have h3 : ((c : ℕ) : ℝ) = ((c' : ℕ) : ℝ) + 1 := by
        rw [show (c : ℕ) = (c' : ℕ) + 1 by show (c : ℕ) = (c : ℕ) - 1 + 1; omega]
        push_cast
        ring
      linarith
  have hab' := Fin.le_def.mp hab
  exact key ((b : ℕ) - a) b hab (by omega)

theorem lowK_card_gt (ε : Fin n → Bool) (a : Fin n) :
    (univ.filter fun b => a < b ∧ ε b ≠ ε a).card + (univ.filter fun b => a < b ∧ ε b = ε a).card
      = n - 1 - a := by
  have key : ∀ s : Finset (Fin n), (s.filter (fun b => ε b ≠ ε a)).card +
      (s.filter (fun b => ¬ (ε b ≠ ε a))).card = s.card := by
    intro s
    first
    | exact Finset.card_filter_add_card_filter_not _
    | exact Finset.filter_card_add_filter_neg_card_eq_card _
    | rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_neg s s _),
        Finset.filter_union_filter_neg_eq]
    | rw [← Finset.card_disjoint_union (Finset.disjoint_filter_filter_neg s s _),
        Finset.filter_union_filter_neg_eq]
  rw [← Fin.card_Ioi a, ← key (Finset.Ioi a)]
  congr 1 <;> congr 1 <;> ext b <;> simp

theorem lowK_card_lt (ε : Fin n → Bool) (a : Fin n) :
    (univ.filter fun b => b < a ∧ ε b ≠ ε a).card + (univ.filter fun b => b < a ∧ ε b = ε a).card
      = a := by
  have key : ∀ s : Finset (Fin n), (s.filter (fun b => ε b ≠ ε a)).card +
      (s.filter (fun b => ¬ (ε b ≠ ε a))).card = s.card := by
    intro s
    first
    | exact Finset.card_filter_add_card_filter_not _
    | exact Finset.filter_card_add_filter_neg_card_eq_card _
    | rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_neg s s _),
        Finset.filter_union_filter_neg_eq]
    | rw [← Finset.card_disjoint_union (Finset.disjoint_filter_filter_neg s s _),
        Finset.filter_union_filter_neg_eq]
  rw [← Fin.card_Iio a, ← key (Finset.Iio a)]
  congr 1 <;> congr 1 <;> ext b <;> simp

theorem lowest_k_type_formula (ε : Fin n → Bool) (lam : Fin n → ℝ) (a : Fin n) :
    lowK ε lam a = lam a + ((n : ℝ) - 1) / 2 - (a : ℕ)
      - ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℝ)
      + ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℝ) := by
  have hg := lowK_card_gt ε a
  have hl := lowK_card_lt ε a
  have ha := a.isLt
  simp only [lowK, rhoN, rhoC, Pi.add_apply, Pi.sub_apply]
  set A1 := (univ.filter fun b => a < b ∧ ε b ≠ ε a).card
  set A2 := (univ.filter fun b => a < b ∧ ε b = ε a).card
  set A3 := (univ.filter fun b => b < a ∧ ε b ≠ ε a).card
  set A4 := (univ.filter fun b => b < a ∧ ε b = ε a).card
  have e1 : ((A1 : ℕ) : ℝ) + A2 + 1 + (a : ℕ) = n := by
    exact_mod_cast (show A1 + A2 + 1 + (a : ℕ) = n by omega)
  have e2 : ((A3 : ℕ) : ℝ) + A4 = (a : ℕ) := by exact_mod_cast hl
  linarith

theorem lowK_int_dom (ε : Fin n → Bool) (lam : Fin n → ℝ) (hlam : IsHCParam lam) :
    (∀ a, ∃ m : ℤ, lowK ε lam a = m) ∧ ∀ a b, a < b → ε a = ε b → lowK ε lam b ≤ lowK ε lam a := by
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · obtain ⟨m, hm⟩ := hlam.2 a
    refine ⟨m + (n : ℤ) - 1 - ((a : ℕ) : ℤ) - ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℤ)
      + ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℤ), ?_⟩
    rw [lowest_k_type_formula]
    push_cast
    linarith
  · have hs : ε b = ε a := he.symm
    have hab' : (a : ℕ) ≤ b := le_of_lt (Fin.lt_def.mp hab)

    have c1 : (univ.filter fun c => a < c ∧ ε c = ε a).card ≤
        (univ.filter fun c => b < c ∧ ε c = ε b).card + ((b : ℕ) - a) := by
      calc _ ≤ ((univ.filter fun c => b < c ∧ ε c = ε b) ∪ Finset.Ioc a b).card := by
            apply Finset.card_le_card
            intro c hc
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
              Finset.mem_Ioc] at hc ⊢
            rw [hs]
            by_cases hcb : b < c
            · exact Or.inl ⟨hcb, hc.2⟩
            · exact Or.inr ⟨hc.1, not_lt.mp hcb⟩
        _ ≤ _ := by
            rw [← Fin.card_Ioc]
            exact Finset.card_union_le _ _
    have c2 : (univ.filter fun c => c < b ∧ ε c = ε b).card ≤
        (univ.filter fun c => c < a ∧ ε c = ε a).card + ((b : ℕ) - a) := by
      calc _ ≤ ((univ.filter fun c => c < a ∧ ε c = ε a) ∪ Finset.Ico a b).card := by
            apply Finset.card_le_card
            intro c hc
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
              Finset.mem_Ico] at hc ⊢
            rw [← hs]
            by_cases hca : c < a
            · exact Or.inl ⟨hca, hc.2⟩
            · exact Or.inr ⟨not_lt.mp hca, hc.1⟩
        _ ≤ _ := by
            rw [← Fin.card_Ico]
            exact Finset.card_union_le _ _
    have gap := hc_param_gap_ge_index lam hlam a b hab.le
    have c1r : (((univ.filter fun c => a < c ∧ ε c = ε a).card : ℕ) : ℝ) ≤
        ((univ.filter fun c => b < c ∧ ε c = ε b).card : ℕ) + (((b : ℕ) : ℝ) - (a : ℕ)) := by
      have := c1
      rw [← Nat.cast_le (α := ℝ)] at this
      push_cast [Nat.cast_sub hab'] at this
      linarith
    have hcard₃ : (((univ.filter fun c => c < b ∧ ε c = ε b).card : ℕ) : ℝ) ≤
        ((univ.filter fun c => c < a ∧ ε c = ε a).card : ℕ) + (((b : ℕ) : ℝ) - (a : ℕ)) := by
      have := c2
      rw [← Nat.cast_le (α := ℝ)] at this
      push_cast [Nat.cast_sub hab'] at this
      linarith
    rw [lowest_k_type_formula, lowest_k_type_formula]
    linarith

end ReciprocityTheory.ChartRestriction.DS.HW
