import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt

noncomputable section

open Formalism.BasicNotions.Loc

namespace UpperTheory.Gal.ClosedPhiFromClosedTrace

private theorem linearIndependent_update_sum_of_ne_zero {l : ℕ} [Fact (Nat.Prime l)] {F : IntermediateField ℚ_[l] (Om l)} {m : ℕ}
    (e : Fin m → Om l) (hLI : LinearIndependent F e) (a : Fin m → F) (j0 : Fin m) (ha : a j0 ≠ 0) :
    LinearIndependent F (Function.update e j0 (∑ j, (a j : Om l) * e j)) := by
  rw [Fintype.linearIndependent_iff] at hLI ⊢
  intro g hg
  have key : ∑ j, (g j + g j0 * a j - if j = j0 then g j0 else 0) • e j = 0 := by
    rw [← hg]
    have h1 : ∀ j, (g j + g j0 * a j - if j = j0 then g j0 else 0) • e j
        = g j • e j + (g j0 : Om l) * ((a j : Om l) * e j) - (if j = j0 then (g j0 : Om l) * e j0 else 0) := by
      intro j
      by_cases h : j = j0
      · subst h
        rw [if_pos rfl, if_pos rfl]
        show ((g j + g j * a j - g j : F) : Om l) * e j = (g j : Om l) * e j + _ - _
        push_cast
        ring
      · rw [if_neg h, if_neg h]
        show ((g j + g j0 * a j - 0 : F) : Om l) * e j = (g j : Om l) * e j + _ - _
        push_cast
        ring
    have h2 : ∀ j, g j • Function.update e j0 (∑ i, (a i : Om l) * e i) j
        = g j • e j + (if j = j0 then (g j0 : Om l) * (∑ i, (a i : Om l) * e i) - (g j0 : Om l) * e j0 else 0) := by
      intro j
      by_cases h : j = j0
      · subst h
        rw [Function.update_self, if_pos rfl]
        show (g j : Om l) * _ = (g j : Om l) * e j + _
        ring
      · rw [Function.update_of_ne h, if_neg h, add_zero]
    rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_congr rfl (fun j _ => h2 j)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true, ← Finset.mul_sum]
    ring
  have hz := hLI _ key
  have h0 : g j0 = 0 := by
    have h3 := hz j0
    rw [if_pos rfl] at h3
    have h4 : g j0 * a j0 = 0 := by linear_combination h3
    rcases mul_eq_zero.1 h4 with h | h
    · exact h
    · exact absurd h ha
  intro j
  have h5 := hz j
  rw [h0] at h5
  simpa using h5

private theorem exists_bounded_coeffs_after_update {l : ℕ} [Fact (Nat.Prime l)] {F : IntermediateField ℚ_[l] (Om l)} {m : ℕ}
    (e : Fin m → Om l) (a c : Fin m → F) (j0 : Fin m) (ha : 1 < ‖(a j0 : Om l)‖)
    (hmax : ∀ j, ‖(a j : Om l)‖ ≤ ‖(a j0 : Om l)‖) (hc : ∀ j, ‖(c j : Om l)‖ ≤ 1) :
    ∃ c' : Fin m → F, (∀ j, ‖(c' j : Om l)‖ ≤ 1) ∧
      ∑ j, (c j : Om l) * e j = ∑ j, (c' j : Om l) * Function.update e j0 (∑ i, (a i : Om l) * e i) j := by
  have ha0 : (a j0 : Om l) ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    linarith
  have hpos : 0 < ‖(a j0 : Om l)‖ := by linarith
  refine ⟨fun j => if j = j0 then c j0 / a j0 else c j - c j0 * a j / a j0, ?_, ?_⟩
  · intro j
    by_cases h : j = j0
    · simp only [if_pos h]
      push_cast
      rw [norm_div, div_le_one hpos]
      linarith [hc j0]
    · simp only [if_neg h]
      push_cast
      rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hc j) ?_)
      rw [norm_neg, norm_div, norm_mul, div_le_one hpos]
      calc ‖(c j0 : Om l)‖ * ‖(a j : Om l)‖ ≤ 1 * ‖(a j0 : Om l)‖ :=
            mul_le_mul (hc j0) (hmax j) (norm_nonneg _) zero_le_one
        _ = ‖(a j0 : Om l)‖ := one_mul _
  · set y := ∑ i, (a i : Om l) * e i with hy
    have h1 : ∀ j, ((if j = j0 then c j0 / a j0 else c j - c j0 * a j / a j0 : F) : Om l) * Function.update e j0 y j
        = (c j : Om l) * e j - ((c j0 : Om l) / (a j0 : Om l)) * ((a j : Om l) * e j)
          + (if j = j0 then ((c j0 : Om l) / (a j0 : Om l)) * y else 0) := by
      intro j
      by_cases h : j = j0
      · subst h
        rw [if_pos rfl, if_pos rfl, Function.update_self]
        push_cast
        field_simp
        ring
      · rw [if_neg h, if_neg h, Function.update_of_ne h]
        push_cast
        ring
    rw [Finset.sum_congr rfl (fun j _ => h1 j)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true, ← Finset.mul_sum, ← hy]
    ring

private theorem exists_bounded_independent_spanning_family {l : ℕ} [Fact (Nat.Prime l)] (F : IntermediateField ℚ_[l] (Om l)) (n : ℕ) :
    ∀ x : Fin n → Om l, (∀ i, ‖x i‖ ≤ 1) → ∃ (m : ℕ) (e : Fin m → Om l), LinearIndependent F e ∧
      (∀ j, ‖e j‖ ≤ 1) ∧ ∀ i, ∃ c : Fin m → F, (∀ j, ‖(c j : Om l)‖ ≤ 1) ∧ x i = ∑ j, (c j : Om l) * e j := by
  induction n with
  | zero =>
    intro x _
    exact ⟨0, Fin.elim0, linearIndependent_empty_type, fun j => j.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro x hx
    obtain ⟨m, e, hLI, he, hc⟩ := ih (fun i => x (Fin.castSucc i)) (fun i => hx _)
    by_cases hy : x (Fin.last n) ∈ Submodule.span F (Set.range e)
    · obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hy
      have ha' : x (Fin.last n) = ∑ j, (a j : Om l) * e j := ha.symm
      by_cases hb : ∀ j, ‖(a j : Om l)‖ ≤ 1
      · refine ⟨m, e, hLI, he, fun i => ?_⟩
        induction i using Fin.lastCases with
        | last => exact ⟨a, hb, ha'⟩
        | cast i => exact hc i
      · push_neg at hb
        obtain ⟨j1, hj1⟩ := hb
        haveI : Nonempty (Fin m) := ⟨j1⟩
        obtain ⟨j0, hj0⟩ := Finite.exists_max (fun j => ‖(a j : Om l)‖)
        have ha1 : 1 < ‖(a j0 : Om l)‖ := lt_of_lt_of_le hj1 (hj0 j1)
        have ha0 : a j0 ≠ 0 := by
          intro h
          rw [h] at ha1
          norm_num at ha1
        refine ⟨m, Function.update e j0 (x (Fin.last n)), ?_, ?_, ?_⟩
        · rw [ha']
          exact linearIndependent_update_sum_of_ne_zero e hLI a j0 ha0
        · intro j
          by_cases h : j = j0
          · subst h
            rw [Function.update_self]
            exact hx _
          · rw [Function.update_of_ne h]
            exact he j
        · intro i
          induction i using Fin.lastCases with
          | last =>
            refine ⟨Pi.single j0 1, ?_, ?_⟩
            · intro j
              by_cases h : j = j0
              · subst h
                simp
              · simp [Pi.single_apply, h]
            · rw [Finset.sum_eq_single j0]
              · simp
              · intro j _ h
                simp [Pi.single_apply, h]
              · simp
          | cast i =>
            obtain ⟨c, hc1, hc2⟩ := hc i
            obtain ⟨c', hc'1, hc'2⟩ := exists_bounded_coeffs_after_update e a c j0 ha1 hj0 hc1
            refine ⟨c', hc'1, ?_⟩
            rw [hc2, hc'2, ← ha']
    · refine ⟨m + 1, (Fin.snoc e (x (Fin.last n)) : Fin (m + 1) → Om l),
        linearIndependent_fin_snoc.2 ⟨hLI, hy⟩, ?_, ?_⟩
      · intro j
        induction j using Fin.lastCases with
        | last =>
          rw [Fin.snoc_last]
          exact hx _
        | cast j =>
          rw [Fin.snoc_castSucc]
          exact he j
      · intro i
        induction i using Fin.lastCases with
        | last =>
          refine ⟨(Fin.snoc (0 : Fin m → F) 1 : Fin (m + 1) → F), ?_, ?_⟩
          · intro j
            induction j using Fin.lastCases with
            | last => simp
            | cast j => simp
          · simp [Fin.sum_univ_castSucc]
        | cast i =>
          obtain ⟨c, hc1, hc2⟩ := hc i
          refine ⟨(Fin.snoc c 0 : Fin (m + 1) → F), ?_, ?_⟩
          · intro j
            induction j using Fin.lastCases with
            | last => simp
            | cast j => simp [hc1 j]
          · simp [Fin.sum_univ_castSucc, hc2]

theorem intBasis_holds : IntBasis := fun l _ F n x hx => exists_bounded_independent_spanning_family F n x hx

end UpperTheory.Gal.ClosedPhiFromClosedTrace

end
