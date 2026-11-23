import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ExistsTeichmullerRepModPrime
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.NormLeOneOfIntegralInt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

theorem tch_of_integral (δ : ℂ_[l]) (hδ : IsIntegral (Rmu l) δ) : ∃ ξ ∈ Tch l, ‖δ - ξ‖ < 1 := by
  have hZ := KE.isIntegral_int_of_rmu (l := l) δ hδ
  have h1 : ‖δ‖ ≤ 1 := KE.norm_le_one_of_integral_int δ hZ
  have hl : ‖(l : ℂ_[l])‖ < 1 := by
    rw [norm_l_Cl (l := l)]
    have h1l : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    exact inv_lt_one_of_one_lt₀ h1l
  obtain ⟨f, hf, hfr⟩ := KE.frob_fix_of_integral l (Fact.out : l.Prime) hl δ hZ
  obtain ⟨ξ, hξ, hd⟩ := tch_near (l := l) δ h1 f hf _ hfr le_rfl
  exact ⟨ξ, hξ, lt_of_le_of_lt hd hfr⟩

open Polynomial in
theorem kur_resClosed : ResClosed (MaximalUnramifiedExtension l) l := by
  classical
  intro P hPm hPd hPc
  have hrep : ∀ i : ℕ, ∃ ξ ∈ Tch l, ‖((P.coeff i : MaximalUnramifiedExtension l) : ℂ_[l]) - ξ‖ ≤ ‖(l : ℂ_[l])‖ :=
    fun i => kur_rep (l := l) (P.coeff i).2 (hPc i)
  choose g hgT hgd using hrep
  have hgR : ∀ i, g i ∈ Rmu l := fun i => KE.tch_mem_rmu (l := l) (hgT i)
  have hQ'deg : (∑ i : Fin P.natDegree, C (⟨g i, hgR i⟩ : Rmu l) * X ^ (i : ℕ)).degree
      < (P.natDegree : WithBot ℕ) := degree_sum_fin_lt _
  let Q' : Polynomial (Rmu l) :=
    X ^ P.natDegree + ∑ i : Fin P.natDegree, C (⟨g i, hgR i⟩ : Rmu l) * X ^ (i : ℕ)
  have hQ'm : Q'.Monic := monic_X_pow_add hQ'deg
  let Qc : Polynomial ℂ_[l] := Q'.map (algebraMap (Rmu l) ℂ_[l])
  have hQcdeg : Qc.degree ≠ 0 := by
    have hX : (X ^ P.natDegree : Polynomial (Rmu l)).degree = P.natDegree := degree_X_pow _
    have hQ'd : Q'.degree = P.natDegree := by
      rw [← hX]
      exact degree_add_eq_left_of_degree_lt (hX ▸ hQ'deg)
    rw [hQ'm.degree_map, hQ'd]
    first | exact_mod_cast hPd.ne' | simpa using hPd.ne'
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_root Qc hQcdeg
  have hδint : IsIntegral (Rmu l) δ := ⟨Q', hQ'm, by rw [← eval_map]; exact hδ⟩
  have hQeval : ∀ y : ℂ_[l],
      Qc.eval y = y ^ P.natDegree + ∑ i : Fin P.natDegree, g i * y ^ (i : ℕ) := by
    intro y
    simp [Qc, Q', eval_map, eval₂_finset_sum] <;> rfl
  obtain ⟨ξ, hξT, hξd⟩ := tch_of_integral l δ hδint
  have hξ1 : ‖ξ‖ ≤ 1 := tch_norm_le (l := l) hξT
  have hξK : ξ ∈ MaximalUnramifiedExtension l := tch_mem_kur (l := l) hξT
  have hδ1 : ‖δ‖ ≤ 1 :=
    KE.norm_le_one_of_integral (fun r : Rmu l => rmu_norm_le (l := l) r.2) δ hδint
  have hQc : ∀ i, ‖Qc.coeff i‖ ≤ 1 := by
    intro i
    rw [coeff_map]
    exact rmu_norm_le (l := l) (Q'.coeff i).2
  set F : ℂ_[l] := ξ ^ P.natDegree + ∑ i : Fin P.natDegree, g i * ξ ^ (i : ℕ) with hF
  have hFK : F ∈ MaximalUnramifiedExtension l :=
    add_mem (pow_mem hξK _)
      (sum_mem fun i _ => mul_mem (tch_mem_kur (l := l) (hgT i)) (pow_mem hξK _))
  have hFlt : ‖F‖ < 1 := by
    have h := KE.norm_eval_sub_eval_le Qc hQc hξ1 hδ1
    rw [hQeval ξ, hδ.eq_zero, sub_zero, norm_sub_rev] at h
    exact lt_of_le_of_lt h hξd
  have hFl : ‖F‖ ≤ ‖(l : ℂ_[l])‖ := kur_discrete (l := l) hFK hFlt

  have hsum : ∀ (s : Finset (Fin P.natDegree)) (f : Fin P.natDegree → ℂ_[l]),
      (∀ i ∈ s, ‖f i‖ ≤ ‖(l : ℂ_[l])‖) → ‖∑ i ∈ s, f i‖ ≤ ‖(l : ℂ_[l])‖ := by
    intro s f
    refine Finset.induction_on s (fun _ => by simp) ?_
    intro a s ha ih h
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))
  have hS : ‖∑ i : Fin P.natDegree, (((P.coeff i : MaximalUnramifiedExtension l) : ℂ_[l]) - g i) * ξ ^ (i : ℕ)‖
      ≤ ‖(l : ℂ_[l])‖ := by
    apply hsum
    intro i _
    rw [norm_mul, norm_pow]
    calc ‖((P.coeff i : MaximalUnramifiedExtension l) : ℂ_[l]) - g i‖ * ‖ξ‖ ^ (i : ℕ) ≤ ‖(l : ℂ_[l])‖ * 1 :=
          mul_le_mul (hgd i) (pow_le_one₀ (norm_nonneg _) hξ1) (by positivity) (norm_nonneg _)
      _ = ‖(l : ℂ_[l])‖ := mul_one _
  refine ⟨⟨ξ, hξK⟩, tch_norm_le (l := l) hξT, ?_⟩
  have hPx : ((P.eval (⟨ξ, hξK⟩ : MaximalUnramifiedExtension l) : MaximalUnramifiedExtension l) : ℂ_[l]) =
      ξ ^ P.natDegree + ∑ i : Fin P.natDegree, ((P.coeff i : MaximalUnramifiedExtension l) : ℂ_[l]) * ξ ^ (i : ℕ) := by
    conv_lhs => rw [hPm.as_sum]
    simp [eval_finset_sum, Finset.sum_range]
  have hlK : ((l : MaximalUnramifiedExtension l) : ℂ_[l]) = (l : ℂ_[l]) := by simp
  show ‖((P.eval (⟨ξ, hξK⟩ : MaximalUnramifiedExtension l) : MaximalUnramifiedExtension l) : ℂ_[l])‖ ≤ ‖((l : MaximalUnramifiedExtension l) : ℂ_[l])‖
  rw [hPx, hlK]
  have hsplit : ξ ^ P.natDegree + ∑ i : Fin P.natDegree, ((P.coeff i : MaximalUnramifiedExtension l) : ℂ_[l]) * ξ ^ (i : ℕ)
      = (∑ i : Fin P.natDegree, (((P.coeff i : MaximalUnramifiedExtension l) : ℂ_[l]) - g i) * ξ ^ (i : ℕ)) + F := by
    rw [hF]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hS hFl)

end ReciprocityTheory.ChartRestriction.L1
