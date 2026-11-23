import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPowerHermitianFormDensity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffEqTensorSquareTopCoefficient

set_option autoImplicit false

noncomputable section

open MvPolynomial
open GlobalTheory.CxForm GlobalTheory.GoodMetric GlobalTheory.CxForm.DensPow GlobalTheory.GrassModel GlobalTheory.GrassModel.TopRead

namespace GlobalTheory.ChernCalc.DensTop

variable {n : ℕ}

theorem bas_mul_smul (S T : Finset (Fin (n + n))) : ∃ c : ℂ, bas n S * bas n T = c • bas n (S ∪ T) := by
  by_cases h : Disjoint S T
  · obtain ⟨ε, e⟩ := bas_mul h
    exact ⟨_, by rw [e, Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ]⟩
  · have := ExteriorAlgebra.basis_mul_of_not_disjoint ((Pi.basisFun ℂ (Fin n ⊕ Fin n)).reindex finSumFinEquiv)
      (Set.powersetCard.ofCard (s := S) rfl) (Set.powersetCard.ofCard (s := T) rfl) h
    have e : bas n S * bas n T = 0 := this
    exact ⟨0, by rw [e, zero_smul]⟩

theorem prod_sym_eq {ι : Type} [DecidableEq ι] (x : ι → Fin n × Fin n) (s : Finset ι) :
    ∃ (c : ℂ) (S : Finset (Fin (n + n))), S.card ≤ 2 * s.card ∧ ((∏ j ∈ s, sym (x j) : Ev n) : Alt n) = c • bas n S := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, ∅, by simp, by simp [bas_empty]⟩
  | insert a s ha ih =>
    obtain ⟨c, S, hS, e⟩ := ih
    obtain ⟨c₁, h₁⟩ := bas_mul_smul {finSumFinEquiv (.inl (x a).1)} {finSumFinEquiv (.inr (x a).2)}
    obtain ⟨c₂, h₂⟩ := bas_mul_smul ({finSumFinEquiv (.inl (x a).1)} ∪ {finSumFinEquiv (.inr (x a).2)}) S
    refine ⟨c₁ * c * c₂, ({finSumFinEquiv (.inl (x a).1)} ∪ {finSumFinEquiv (.inr (x a).2)}) ∪ S, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem ha]
      refine (Finset.card_union_le _ _).trans ?_
      have := Finset.card_union_le ({finSumFinEquiv (.inl (x a).1)} : Finset (Fin (n + n)))
        {finSumFinEquiv (.inr (x a).2)}
      rw [Finset.card_singleton, Finset.card_singleton] at this
      omega
    · rw [Finset.prod_insert ha, Subalgebra.coe_mul, e,
        show (sym (x a) : Alt n) = dz (x a).1 * dzb (x a).2 from rfl, dz, dzb, ← bas_singleton,
        ← bas_singleton, h₁, smul_mul_smul_comm, h₂, smul_smul]

theorem prod_sym_not_inj {m : ℕ} (x : Fin m → Fin n × Fin n) (h : ¬ Function.Injective fun j => (x j).1) :
    (∏ j, sym (x j) : Ev n) = 0 := by
  simp only [Function.Injective, not_forall] at h
  obtain ⟨i, j, hij, hne⟩ := h
  have h0 : sym (x i) * sym (x j) = 0 := by
    apply Subtype.ext
    change dz (x i).1 * dzb (x i).2 * (dz (x j).1 * dzb (x j).2) = 0
    rw [hij]
    exact ι_mul_ι_mul_ι_mul_ι_left _ _ _
  rw [← Finset.mul_prod_erase Finset.univ (fun a => sym (x a)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) (fun a => sym (x a))
      (Finset.mem_erase.2 ⟨fun e => hne e.symm, Finset.mem_univ j⟩), ← mul_assoc, h0, zero_mul]

theorem dens_zero' : dens (0 : Alt n) = 0 := by simp [dens]

theorem dens_add' (x y : Alt n) : dens (x + y) = dens x + dens y := by simp [dens, add_div]

theorem dens_prod_diag : dens ((∏ a, sym (a, a) : Ev n) : Alt n) = ((Complex.I / 2) ^ n)⁻¹ := by
  have h1 := dens_vol n
  rw [vol_eq_smul_prod, Subalgebra.coe_smul, dens_smul] at h1
  exact eq_inv_of_mul_eq_one_right h1

theorem dens_prod {m : ℕ} (x : Fin m → Fin n × Fin n) :
    dens ((∏ j, sym (x j) : Ev n) : Alt n) =
      topForm n m (fun j => Pi.single (x j).1 1) * topForm n m (fun j => Pi.single (x j).2 1) /
        (Complex.I / 2) ^ n := by
  by_cases hm : m = n
  swap
  · have h0 : topForm n m = 0 := by simp [topForm, hm]
    rw [h0]
    simp only [AlternatingMap.zero_apply, mul_zero, zero_div]
    rcases lt_or_gt_of_ne hm with h | h
    · obtain ⟨c, S, hS, e⟩ := prod_sym_eq x Finset.univ
      have hne : S ≠ Finset.univ := by
        rintro rfl
        simp at hS
        omega
      rw [e]
      simp [dens, Finsupp.single_apply, hne]
    · rw [prod_sym_not_inj x, Subalgebra.coe_zero, dens_zero']
      intro hi
      have := Fintype.card_le_of_injective _ hi
      simp at this
      omega
  subst hm
  rw [topForm_self, topForm_self]
  by_cases ha : Function.Injective fun j => (x j).1
  swap
  · rw [prod_sym_not_inj x ha, Subalgebra.coe_zero, dens_zero', det_single_not_inj _ ha, zero_mul, zero_div]
  let π : Equiv.Perm (Fin m) := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp ha)
  have hπ : ∀ j, (x j).1 = π j := fun j => rfl
  have e1 : (∏ j, sym (x j) : Ev m) = ∏ c, row c (Pi.single (x (π.symm c)).2 1) := by
    rw [← Equiv.prod_comp π fun c => row c (Pi.single (x (π.symm c)).2 1)]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Equiv.symm_apply_apply, ← hπ]
    simp [row, Pi.single_apply]
  have e2 := prod_row (n := m) (Matrix.of fun c => Pi.single (x (π.symm c)).2 1)
  have e3 : (Matrix.of fun c => (Pi.single (x (π.symm c)).2 1 : Fin m → ℂ)).det =
      (Pi.basisFun ℂ (Fin m)).det ((fun j => Pi.single (x j).2 1) ∘ π.symm) := by
    rw [Pi.basisFun_det]; rfl
  rw [e1]
  refine (congrArg (fun z : Ev m => dens (z : Alt m)) e2).trans ?_
  simp only [hπ, det_single_perm]
  rw [Subalgebra.coe_smul, dens_smul, dens_prod_diag, e3, AlternatingMap.map_perm, Equiv.Perm.sign_symm,
    Units.smul_def, zsmul_eq_mul, ← div_eq_mul_inv]

theorem dens_aeval_sym (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    dens ((aeval sym P : Ev n) : Alt n) = topCoeff P / (Complex.I / 2) ^ n := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    obtain ⟨l, hl⟩ : ∃ l : List (Fin n × Fin n), (l : Multiset _) = Finsupp.toMultiset u :=
      ⟨_, Multiset.coe_toList _⟩
    have hu : u = ∑ j, Finsupp.single (l.get j) 1 := by
      apply toMultiset_injective'
      rw [toMultiset_sum_single, Fin.univ_val_map, List.ofFn_get, hl]
    have hmon : (monomial u c : MvPolynomial (Fin n × Fin n) ℂ) = c • ∏ j, X (l.get j) := by
      rw [hu, show (∏ j, X (l.get j) : MvPolynomial (Fin n × Fin n) ℂ) = monomial (∑ j, Finsupp.single (l.get j) 1) 1 from
        (monomial_sum_one _ _).symm, smul_monomial, smul_eq_mul, mul_one]
    rw [hmon, map_smul, Subalgebra.coe_smul, dens_smul, map_prod]
    simp only [aeval_X]
    rw [dens_prod, ← topCoeff_prod, ← mul_div_assoc]
    congr 1
    unfold topCoeff
    simp only [coeff_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => by ring
  | add p q hp hq =>
    rw [map_add, Subalgebra.coe_add, dens_add', hp, hq, ← add_div]
    congr 1
    unfold topCoeff
    simp only [coeff_add, mul_add, Finset.sum_add_distrib]

end GlobalTheory.ChernCalc.DensTop
