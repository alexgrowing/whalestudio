import Mathlib
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Formalism.RealPlaceAnalysis.Complexify

open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHe.Frame

open Polynomial

theorem degree_sub_lt_of_nextCoeff_eq {p q : ℝ[X]} {m : ℕ} (hp : p.Monic) (hq : q.Monic)
    (hpd : p.natDegree = m + 1) (hqd : q.natDegree = m + 1) (hn : p.nextCoeff = q.nextCoeff) :
    (p - q).degree < (m : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro k hk
  rw [coeff_sub]
  rcases hk.eq_or_lt with rfl | hk'
  · have h1 : p.nextCoeff = p.coeff m := by
      rw [nextCoeff_of_natDegree_pos (by omega), hpd]; rfl
    have h2 : q.nextCoeff = q.coeff m := by
      rw [nextCoeff_of_natDegree_pos (by omega), hqd]; rfl
    rw [← h1, ← h2, hn, sub_self]
  · rcases (Nat.succ_le_of_lt hk').eq_or_lt with rfl | hk''
    · have h1 := hp.coeff_natDegree
      have h2 := hq.coeff_natDegree
      rw [hpd] at h1
      rw [hqd] at h2
      rw [h1, h2, sub_self]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega),
        sub_zero]

theorem prod_eq_partial_fraction {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ)
    (hd' : Function.Injective d') :
    (∏ i, (X - C (d i))) = (X - C (pfX d d')) * (∏ j, (X - C (d' j))) +
      ∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) := by
  have hPm : (∏ i, (X - C (d i)) : ℝ[X]).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hQm : (∏ j, (X - C (d' j)) : ℝ[X]).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hPd : (∏ i, (X - C (d i)) : ℝ[X]).natDegree = m + 1 := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]; simp
  have hQd : (∏ j, (X - C (d' j)) : ℝ[X]).natDegree = m := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]; simp
  have hRm : ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).Monic := (monic_X_sub_C _).mul hQm
  have hRd : ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).natDegree = m + 1 := by
    rw [(monic_X_sub_C _).natDegree_mul hQm, hQd, natDegree_X_sub_C]; omega
  have hn : (∏ i, (X - C (d i)) : ℝ[X]).nextCoeff =
      ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).nextCoeff := by
    rw [(monic_X_sub_C _).nextCoeff_mul hQm, prod_X_sub_C_nextCoeff, prod_X_sub_C_nextCoeff,
      nextCoeff_X_sub_C, pfX]
    ring
  have hD := degree_sub_lt_of_nextCoeff_eq hPm hRm hPd hRd hn
  have hS : (∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).degree
      < (m : WithBot ℕ) := by
    rw [degree_lt_iff_coeff_zero]
    intro n hn
    rw [finset_sum_coeff]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [coeff_C_mul]
    have hL : (∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).natDegree < n := by
      rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
      have hj : (univ.erase j).card + 1 = m := by
        rw [Finset.card_erase_of_mem (mem_univ j)]
        have : 0 < m := j.pos
        simp only [card_univ, Fintype.card_fin]
        omega
      simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one]
      omega
    rw [coeff_eq_zero_of_natDegree_lt hL, mul_zero]
  have hcard : (#(univ : Finset (Fin m)) : ℕ) = m := by simp
  have key := Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := (univ : Finset (Fin m)))
    (v := d') (f := (∏ i, (X - C (d i))) - (X - C (pfX d d')) * ∏ j, (X - C (d' j)))
    (g := ∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)))
    hd'.injOn (by rw [hcard]; exact hD) (by rw [hcard]; exact hS) (by
      intro j _
      have hne : ∏ k ∈ univ.erase j, (d' j - d' k) ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr fun h => ?_
        exact (Finset.mem_erase.mp hk).1 (hd' h).symm
      have hQ0 : (∏ l, (d' j - d' l)) = 0 :=
        Finset.prod_eq_zero (mem_univ j) (sub_self _)
      have hterm : ∀ l ∈ (univ : Finset (Fin m)), l ≠ j →
          pfR d d' l * ∏ k ∈ univ.erase l, (d' j - d' k) = 0 := by
        intro l _ hl
        rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hl.symm, mem_univ j⟩) (sub_self _), mul_zero]
      simp only [eval_sub, eval_mul, eval_prod, eval_X, eval_C, eval_finset_sum]
      rw [hQ0, mul_zero, sub_zero, Finset.sum_eq_single_of_mem j (mem_univ j) hterm, pfR,
        div_mul_cancel₀ _ hne])
  rw [← key]
  ring

theorem pfZero {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ)
    (hinj : Function.Injective (Sum.elim d d')) (i : Fin (m + 1)) :
    d i - pfX d d' + ∑ j, pfR d d' j / (d i - d' j) = 0 := by
  have hd' : Function.Injective d' := fun a b h =>
    Sum.inr_injective (hinj (by simpa using h))
  have hne : ∀ j, d i - d' j ≠ 0 := fun j => sub_ne_zero.mpr fun h => by
    simpa using hinj (a₁ := Sum.inl i) (a₂ := Sum.inr j) (by simpa using h)
  have hQ : ∏ j, (d i - d' j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hne j
  have h := congrArg (eval (d i)) (prod_eq_partial_fraction d d' hd')
  simp only [eval_add, eval_sub, eval_mul, eval_prod, eval_X, eval_C, eval_finset_sum] at h
  rw [Finset.prod_eq_zero (mem_univ i) (sub_self _)] at h
  have hsum : ∀ j, pfR d d' j * ∏ k ∈ univ.erase j, (d i - d' k) =
      (pfR d d' j / (d i - d' j)) * ∏ k, (d i - d' k) := by
    intro j
    rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
    field_simp [hne j]
  simp only [hsum, ← Finset.sum_mul] at h
  rw [← add_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_right hQ

end GlobalTheory.CompanionTheory.RgHe.Frame
