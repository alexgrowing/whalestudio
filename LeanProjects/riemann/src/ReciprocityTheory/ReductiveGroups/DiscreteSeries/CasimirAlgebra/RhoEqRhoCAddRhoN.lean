import ReciprocityTheory.ReductiveGroups.DiscreteSeries.IsInfUnitary

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Alg

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem casimir_split {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E)
    (P : Fin n → Fin n → Prop) [DecidableRel P] (hirr : ∀ a, ¬ P a a)
    (hP : ∀ a b, a ≠ b → (P a b ↔ ¬ P b a)) :
    casimir E = ∑ a, E a a * E a a +
      ∑ a, ∑ b ∈ univ.filter (fun b => P a b), (E a a - E b b + 2 • (E b a * E a b)) := by
  classical

  have h1 : casimir E = ∑ a, ∑ b, ((if a = b then E a a * E a a else 0) +
      (if P a b then E a b * E b a else 0) + (if P b a then E a b * E b a else 0)) := by
    unfold casimir
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : a = b
    · subst hab
      simp [hirr]
    · by_cases h : P a b
      · have h' : ¬ P b a := (hP a b hab).1 h
        simp [hab, h, h']
      · have h' : P b a := by
          by_contra h''
          exact h ((hP a b hab).2 h'')
        simp [hab, h, h']

  have comm : ∀ a b, E a b * E b a + E b a * E a b = E a a - E b b + 2 • (E b a * E a b) := by
    intro a b
    have h := hE a b b a
    rw [if_pos rfl, if_pos rfl, sub_eq_iff_eq_add] at h
    rw [h]
    abel
  have h3 : ∑ a, ∑ b, (if P b a then E a b * E b a else 0) =
      ∑ a, ∑ b, (if P a b then E b a * E a b else 0) := Finset.sum_comm
  have h4 : ∑ a, ∑ b, (if a = b then E a a * E a a else 0) = ∑ a, E a a * E a a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp
  rw [h1]
  simp only [Finset.sum_add_distrib]
  rw [h3, h4, add_assoc]
  congr 1
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs
  · exact comm a b
  · simp

end Alg

theorem rho_eq_rhoC_add_rhoN (ε : Fin n → Bool) : rho n = rhoC ε + rhoN ε := by
  classical
  funext a
  simp only [rho, rhoC, rhoN, Pi.add_apply]

  have hgt : (univ.filter fun b : Fin n => a < b ∧ ε b = ε a).card +
      (univ.filter fun b : Fin n => a < b ∧ ε b ≠ ε a).card = n - 1 - (a : ℕ) := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.Ioi a)
      (fun b => ε b = ε a)
    rw [Fin.card_Ioi] at h
    rw [← h]
    congr 2 <;> ext b <;> simp

  have hlt : (univ.filter fun b : Fin n => b < a ∧ ε b = ε a).card +
      (univ.filter fun b : Fin n => b < a ∧ ε b ≠ ε a).card = (a : ℕ) := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.Iio a)
      (fun b => ε b = ε a)
    rw [Fin.card_Iio] at h
    rw [← h]
    congr 2 <;> ext b <;> simp
  have ha := a.isLt
  have hc : ((n - 1 - (a : ℕ) : ℕ) : ℝ) = (n : ℝ) - 1 - (a : ℕ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
  have c1 := congrArg (Nat.cast : ℕ → ℝ) hgt
  have c2 := congrArg (Nat.cast : ℕ → ℝ) hlt
  push_cast at c1 c2
  rw [hc] at c1
  linarith

end ReciprocityTheory.ChartRestriction.DS
