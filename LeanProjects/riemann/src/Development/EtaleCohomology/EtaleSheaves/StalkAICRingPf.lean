import Development.EtaleCohomology.EtaleSheaves.FibreEqvPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.StalkAICRingPf

theorem aic_loc {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (hR : AIC R) : AIC S := by
  intro p hp hn
  rcases subsingleton_or_nontrivial R with hR1 | hR1
  · refine ⟨0, ?_⟩
    have h01 : (0 : S) = 1 := by
      rw [← map_zero (algebraMap R S), ← map_one (algebraMap R S), Subsingleton.elim (0 : R) 1]
    exact @Subsingleton.elim _ (subsingleton_of_zero_eq_one h01) _ _
  set n := p.natDegree with hnd
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples M (Finset.univ : Finset (Fin n)) (fun i => p.coeff i)
  choose r hr using fun i : Fin n => hb i (Finset.mem_univ _)
  set β : S := algebraMap R S b with hβ
  have hu : IsUnit β := IsLocalization.map_units S b
  set q : R[X] := X ^ n + ∑ i : Fin n, C (r i * (b : R) ^ (n - 1 - i)) * X ^ (i : ℕ) with hq
  have hqm : q.Monic := monic_X_pow_add (degree_sum_fin_lt _)
  have hqd : q.natDegree = n := by
    rw [hq, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
    rw [degree_X_pow]; exact degree_sum_fin_lt _
  obtain ⟨c, hc⟩ := hR q hqm (hqd ▸ hn)
  refine ⟨hu.unit⁻¹ * algebraMap R S c, ?_⟩
  have key : β ^ n * p.eval (hu.unit⁻¹ * algebraMap R S c) = algebraMap R S (q.eval c) := by
    conv_lhs => rw [hp.as_sum]
    rw [← hnd, ← Fin.sum_univ_eq_sum_range]
    simp only [hq, eval_add, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_C, map_add, map_pow, map_sum, map_mul, mul_add,
      Finset.mul_sum]
    congr 1
    · rw [← mul_pow, ← mul_assoc, hu.mul_val_inv, one_mul]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hr i]
      have hβn : β ^ n = β ^ 1 * β ^ (n - 1 - (i : ℕ)) * β ^ (i : ℕ) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      simp only [Algebra.smul_def, ← hβ]
      rw [hβn, mul_pow]
      have h1 : β ^ (i : ℕ) * (↑hu.unit⁻¹ : S) ^ (i : ℕ) = 1 := by rw [← mul_pow, hu.mul_val_inv, one_pow]
      linear_combination (β ^ 1 * β ^ (n - 1 - (i:ℕ)) * p.coeff i * algebraMap R S c ^ (i:ℕ)) * h1
  rw [hc, map_zero] at key
  exact (hu.pow n).mul_right_eq_zero.1 key

theorem StalkAICRing_of : LateralTheory.E.FibreEqvPf.StalkAICRing := by
  intro S hS x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  let _ := TopCat.Presheaf.algebra_section_stalk S.presheaf (⟨x, hxU⟩ : U)
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  exact aic_loc (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (hS.2 U hU ⟨x, hxU⟩)

end LateralTheory.E.StalkAICRingPf
