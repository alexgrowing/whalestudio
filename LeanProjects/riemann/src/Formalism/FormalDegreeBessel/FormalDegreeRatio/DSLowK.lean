import Formalism.FormalDegreeBessel.StatementDS
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.HalfSumRootsStandard

open Finset

noncomputable section

namespace Formalism.QuantumDeterminants

open Formalism.REAL

lemma dslowk_split {α : Type*} (s : Finset α) (p q : α → Prop) [DecidablePred p] [DecidablePred q] :
    (s.filter p).card =
      (s.filter fun x => p x ∧ q x).card + (s.filter fun x => p x ∧ ¬ q x).card := by
  have hd : Disjoint (s.filter fun x => p x ∧ q x) (s.filter fun x => p x ∧ ¬ q x) :=
    Finset.disjoint_filter.2 fun x _ h1 h2 => h2.2 h1.2
  rw [← Finset.card_disjUnion _ _ hd]
  congr 1
  ext x
  simp only [Finset.mem_disjUnion, Finset.mem_filter]
  tauto

lemma dslowk_lowK_eq {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (a : Fin n) :
    lowK ε lam a = lam a + (((n : ℝ) - 1) / 2 - ((a : ℕ) : ℝ)) - 2 * rhoC ε a := by
  have e1 : (univ.filter fun b : Fin n => a < b).card =
      (univ.filter fun b => a < b ∧ ε b = ε a).card + (univ.filter fun b => a < b ∧ ε b ≠ ε a).card :=
    dslowk_split _ _ _
  have e2 : (univ.filter fun b : Fin n => b < a).card =
      (univ.filter fun b => b < a ∧ ε b = ε a).card + (univ.filter fun b => b < a ∧ ε b ≠ ε a).card :=
    dslowk_split _ _ _
  have c1 : (univ.filter fun b : Fin n => a < b).card + (a : ℕ) + 1 = n := by
    rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
    have := a.isLt
    omega
  have c2 : (univ.filter fun b : Fin n => b < a).card = (a : ℕ) := by
    rw [Finset.filter_gt_eq_Iio, Fin.card_Iio]
  rw [e1] at c1
  rw [e2] at c2
  have r1 := congrArg (Nat.cast (R := ℝ)) c1
  have r2 := congrArg (Nat.cast (R := ℝ)) c2
  push_cast at r1 r2
  unfold lowK rhoN rhoC
  simp only [Pi.add_apply, Pi.sub_apply]
  linarith

theorem low_k_integrable_holds : LowKInt := by
  intro n ε lam h a
  obtain ⟨m, hm⟩ := h a
  refine ⟨m + n - 1 - a - ((univ.filter fun b => a < b ∧ ε b = ε a).card : ℤ) +
    ((univ.filter fun b => b < a ∧ ε b = ε a).card : ℤ), ?_⟩
  rw [dslowk_lowK_eq]
  unfold rhoC
  push_cast
  linarith

lemma dslowk_counts {n : ℕ} (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) :
    (univ.filter fun c => a < c ∧ ε c = ε a).card =
        (univ.filter fun c => b < c ∧ ε c = ε b).card +
          (univ.filter fun c => a < c ∧ c < b ∧ ε c = ε a).card + 1 ∧
      (univ.filter fun c => c < b ∧ ε c = ε b).card =
        (univ.filter fun c => c < a ∧ ε c = ε a).card +
          (univ.filter fun c => a < c ∧ c < b ∧ ε c = ε a).card + 1 ∧
      (univ.filter fun c => a < c ∧ c < b ∧ ε c = ε a).card + ncBetween ε a b + 1 + (a : ℕ) =
        (b : ℕ) := by
  have key : ∀ (P Q R : Fin n → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R]
      (c0 : Fin n), (∀ c, P c ↔ (Q c ∨ R c ∨ c = c0)) → (∀ c, Q c → ¬ R c) → (∀ c, Q c → c ≠ c0) →
      (∀ c, R c → c ≠ c0) → (univ.filter P).card = (univ.filter Q).card + (univ.filter R).card + 1 := by
    intro P Q R _ _ _ c0 hP hQR hQ hR
    have d1 : Disjoint (univ.filter R) {c0} := by
      rw [Finset.disjoint_singleton_right]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun h => hR c0 h rfl
    have d2 : Disjoint (univ.filter Q) ((univ.filter R).disjUnion {c0} d1) := by
      rw [Finset.disjoint_left]
      intro c hc hc'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_disjUnion,
        Finset.mem_singleton] at hc hc'
      rcases hc' with h | h
      · exact hQR c hc h
      · exact hQ c hc h
    have : univ.filter P = (univ.filter Q).disjUnion ((univ.filter R).disjUnion {c0} d1) d2 := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_disjUnion, Finset.mem_singleton]
      exact hP c
    rw [this, Finset.card_disjUnion, Finset.card_disjUnion, Finset.card_singleton, add_assoc]
  have key2 : ∀ (P Q R : Fin n → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R],
      (∀ c, P c ↔ (Q c ∨ R c)) → (∀ c, Q c → ¬ R c) →
      (univ.filter P).card = (univ.filter Q).card + (univ.filter R).card := by
    intro P Q R _ _ _ hP hQR
    have d : Disjoint (univ.filter Q) (univ.filter R) :=
      Finset.disjoint_filter.2 fun c _ h1 h2 => hQR c h1 h2
    have : univ.filter P = (univ.filter Q).disjUnion (univ.filter R) d := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_disjUnion]
      exact hP c
    rw [this, Finset.card_disjUnion]
  have hIoo : (univ.filter fun c : Fin n => a < c ∧ c < b).card = (b : ℕ) - a - 1 := by
    have : (univ.filter fun c : Fin n => a < c ∧ c < b) = Finset.Ioo a b := by
      ext c
      simp
    rw [this, Fin.card_Ioo]
  have hlt : (a : ℕ) < b := hab
  have h3 := key2 (fun c => a < c ∧ c < b) (fun c => a < c ∧ c < b ∧ ε c = ε a)
    (fun c => a < c ∧ c < b ∧ ε c ≠ ε a) (fun c => by tauto) (fun c h1 h2 => h2.2.2 h1.2.2)
  unfold ncBetween
  refine ⟨key _ _ _ b ?_ ?_ ?_ ?_, key _ _ _ a ?_ ?_ ?_ ?_, by omega⟩
  all_goals first | (intro c; grind) | skip

theorem low_k_differentiable_holds : LowKDiff := by
  intro n ε lam a b hab he
  obtain ⟨h1, h2, h3⟩ := dslowk_counts ε hab he
  rw [dslowk_lowK_eq, dslowk_lowK_eq]
  unfold rhoC
  have r1 := congrArg (Nat.cast (R := ℝ)) h1
  have r2 := congrArg (Nat.cast (R := ℝ)) h2
  have r3 := congrArg (Nat.cast (R := ℝ)) h3
  push_cast at r1 r2 r3
  linarith

lemma dslowk_gap {n : ℕ} {lam : Fin n → ℝ} {c : ℝ} (hanti : StrictAnti lam)
    (hint : ∀ x, ∃ m : ℤ, lam x - c = m) {a b : Fin n} (hab : a < b) :
    ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) ≤ lam a - lam b := by
  choose m hm using hint
  have key : ∀ j (hj : j < n), (a : ℕ) ≤ j → m ⟨j, hj⟩ + (j : ℤ) ≤ m a + ((a : ℕ) : ℤ) := by
    intro j
    induction j with
    | zero =>
      intro hj ha
      have : a = ⟨0, hj⟩ := Fin.ext (by simp; omega)
      subst this; simp
    | succ j ih =>
      intro hj ha
      rcases Nat.lt_or_ge (a : ℕ) (j + 1) with h | h
      · have ih' := ih (by omega) (by omega)
        have hlt : lam ⟨j + 1, hj⟩ < lam ⟨j, by omega⟩ := hanti (Fin.mk_lt_mk.mpr (by omega))
        have e1 := hm ⟨j + 1, hj⟩
        have e2 := hm ⟨j, by omega⟩
        have h3 : ((m ⟨j + 1, hj⟩ : ℤ) : ℝ) < (m ⟨j, by omega⟩ : ℝ) := by linarith
        have h4 : m ⟨j + 1, hj⟩ < m ⟨j, by omega⟩ := by exact_mod_cast h3
        push_cast; omega
      · have : a = ⟨j + 1, hj⟩ := Fin.ext (by simp; omega)
        subst this; simp
  have hb := key b b.isLt (le_of_lt (Fin.lt_def.mp hab))
  simp only [Fin.eta] at hb
  have e1 := hm a
  have e2 := hm b
  have hbR : ((m b : ℤ) : ℝ) + ((b : ℕ) : ℝ) ≤ (m a : ℝ) + ((a : ℕ) : ℝ) := by exact_mod_cast hb
  linarith

theorem low_k_dominant_holds : LowKDom := by
  intro n ε lam h a b hab he
  have hd := low_k_differentiable_holds n ε lam a b hab he
  have hg := dslowk_gap h.1 h.2 hab
  rw [hd]
  linarith

theorem holomorphic_low_k_holds : HolLowK := by
  intro n a b
  funext i
  rw [dslowk_lowK_eq]
  unfold rhoC
  have hA : ∀ j, epsHol n j = epsHol n i ↔ (j = 0 ↔ i = 0) := by
    intro j
    unfold epsHol
    first
      | simp
      | (simp; tauto)
  by_cases hi : i = 0
  · have c1 : (univ.filter fun j => i < j ∧ epsHol n j = epsHol n i).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _ h
      have hj : j = 0 := ((hA j).1 h.2).2 hi
      rw [hj, hi] at h
      exact lt_irrefl _ h.1
    have c2 : (univ.filter fun j => j < i ∧ epsHol n j = epsHol n i).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _ h
      rw [hi] at h
      exact Fin.not_lt_zero j h.1
    rw [c1, c2]
    subst hi
    simp [lamHol]
    try ring
  · have hi' : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext (by simpa using h))
    have e1 : (univ.filter fun j => i < j ∧ epsHol n j = epsHol n i) = univ.filter fun j => i < j := by
      refine Finset.filter_congr fun j _ => ?_
      rw [hA j]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, fun hj => absurd (hj ▸ h) (Fin.not_lt_zero i), fun h' => absurd h' hi⟩
    have e2 : (univ.filter fun j => j < i ∧ epsHol n j = epsHol n i) = Finset.Ioo 0 i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioo, hA j, hi, iff_false,
        Fin.lt_iff_val_lt_val, Fin.ext_iff, Fin.val_zero]
      first
        | omega
        | (constructor <;> intro h <;> omega)
    have c1 : (univ.filter fun j => i < j ∧ epsHol n j = epsHol n i).card + (i : ℕ) = n := by
      rw [e1, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
      have := i.isLt
      omega
    have c2 : (univ.filter fun j => j < i ∧ epsHol n j = epsHol n i).card + 1 = (i : ℕ) := by
      rw [e2, Fin.card_Ioo, Fin.val_zero]
      omega
    have r1 := congrArg (Nat.cast (R := ℝ)) c1
    have r2 := congrArg (Nat.cast (R := ℝ)) c2
    push_cast at r1 r2
    simp only [lamHol, hi, ↓reduceIte]
    push_cast
    linarith

theorem holomorphic_harish_chandra_holds : HolHC := by
  intro n a b h
  unfold IsHCParam lamHol
  refine ⟨?_, ?_⟩
  · intro i j hij
    try simp only
    have hij' : (i : ℕ) < j := hij
    have hj : j ≠ 0 := by
      rintro rfl
      exact Fin.not_lt_zero i hij
    rw [if_neg hj]
    have hj1 : (i : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij'
    by_cases hi : i = 0
    · rw [if_pos hi]
      have h1 : ((n : ℤ) : ℝ) < (b : ℝ) - a := by exact_mod_cast h
      have h2 : (1 : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ (j : ℕ))
      push_cast at h1
      linarith
    · rw [if_neg hi]
      linarith
  · intro i
    by_cases hi : i = 0
    · exact ⟨b - n, by rw [if_pos hi]; push_cast; ring⟩
    · exact ⟨a + 1 - (i : ℕ), by rw [if_neg hi]; push_cast; ring⟩

end Formalism.QuantumDeterminants
