import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.SumCCMulSumOfMulEqOne

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G2

open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1

variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)

theorem coeff_divDer (be μ : ι × Fin n →₀ ℕ) (F : MvPolynomial (ι × Fin n) R) :
    coeff μ (divDer be F) = coeff (μ + be) F * ((be.prod fun k j => ((μ + be) k).choose j : ℕ) : R) := by
  classical
  rw [divDer, coeff_sum]
  rw [Finset.sum_congr rfl (g := fun m => if m = μ + be then
      coeff m F * ((be.prod fun k j => (m k).choose j : ℕ) : R) else 0)]
  · rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [notMem_support_iff.mp h, zero_mul]
  · intro m _
    by_cases h1 : be ≤ m
    · rw [if_pos h1, coeff_monomial]
      by_cases h2 : m = μ + be
      · subst h2
        rw [if_pos (add_tsub_cancel_right μ be), if_pos rfl]
      · rw [if_neg h2, if_neg]
        intro h3
        apply h2
        rw [← h3, tsub_add_cancel_of_le h1]
    · rw [if_neg h1, coeff_zero, if_neg]
      rintro rfl
      exact h1 le_add_self

theorem divDer_zero' (F : MvPolynomial (ι × Fin n) R) : divDer 0 F = F := by
  ext μ
  rw [coeff_divDer]
  simp

theorem divDer_single_one (v : ι × Fin n) (F : MvPolynomial (ι × Fin n) R) :
    divDer (Finsupp.single v 1) F = pderiv v F := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    ext μ
    rw [coeff_divDer, pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : u = μ + Finsupp.single v 1
    · subst h
      rw [if_pos rfl, if_pos (add_tsub_cancel_right μ _)]
      simp [Finsupp.prod_single_index, Nat.choose_one_right]
    · rw [if_neg h, zero_mul]
      split_ifs with h2
      · have hv : u v = 0 := by
          by_contra hv
          have hle : Finsupp.single v 1 ≤ u :=
            Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hv)
          apply h
          rw [← h2, tsub_add_cancel_of_le hle]
        rw [hv, Nat.cast_zero, mul_zero]
      · rfl
  | add p q hp hq =>
    rw [map_add, ← hp, ← hq]
    ext μ
    rw [coeff_add, coeff_divDer, coeff_divDer, coeff_divDer, coeff_add, add_mul]

theorem vecDeg_zero' (S : Set ι) : vecDeg LL S (0 : ι × Fin n →₀ ℕ) = 0 := by
  simp [vecDeg]

theorem covDeg_zero' (S : Set ι) : covDeg LL S (0 : ι × Fin n →₀ ℕ) = 0 := by
  simp [covDeg]

theorem vecDeg_single_le (S : Set ι) (v : ι × Fin n) : vecDeg LL S (Finsupp.single v 1) ≤ 1 := by
  classical
  rw [vecDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton]
  split_ifs <;> simp

theorem covDeg_single_le (S : Set ι) (v : ι × Fin n) : covDeg LL S (Finsupp.single v 1) ≤ 1 := by
  classical
  rw [covDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton]
  split_ifs <;> simp

theorem vecDeg_single_of (S : Set ι) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = false) :
    vecDeg LL S (Finsupp.single v 1) = 0 := by
  classical
  rw [vecDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, if_neg]
  rintro ⟨h1, h2⟩
  rw [h h1] at h2
  exact absurd h2 (by decide)

theorem covDeg_single_of (S : Set ι) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = true) :
    covDeg LL S (Finsupp.single v 1) = 0 := by
  classical
  rw [covDeg, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, if_neg]
  rintro ⟨h1, h2⟩
  rw [h h1] at h2
  exact absurd h2 (by decide)

theorem X_eq_monomial' (v : ι × Fin n) : (X v : MvPolynomial (ι × Fin n) R) = monomial (Finsupp.single v 1) 1 := rfl

theorem twistSub_X_out (j : Fin n) (v : ι × Fin n) (h : v.1 ∉ S) :
    twistSub (R := R) LL S j (X v) = X v := by
  simp [twistSub, h]

theorem mem_of_X_mul_mem {e t : ℤ} (v : ι × Fin n) (P : MvPolynomial (ι × Fin n) (GLLaurent R n))
    (h : X v * P ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t) : P ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t := by
  rw [laurentCoeffFiltration, flt_lift_mem] at h ⊢
  intro m
  have hm := h (Finsupp.single v 1 + m)
  rw [coeff_X_mul] at hm
  simpa using hm

theorem valS_X_mul_of (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = true) :
    valS LL S F ≤ valS LL S (X v * F) := by
  have hv := flt_op_valS LL S F (Finsupp.single v 1) 0 0
    (by rw [covDeg_single_of LL S v h, vecDeg_zero'])
  rw [divDer_zero', ← X_eq_monomial', Nat.cast_zero, WithTop.coe_zero, add_zero] at hv
  exact hv

theorem valS_X_mul (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) :
    valS LL S F ≤ valS LL S (X v * F) + ((1 : ℤ) : WithTop ℤ) := by
  have hv := flt_op_valS LL S F (Finsupp.single v 1) 0 1
    (by rw [vecDeg_zero', add_zero]; exact covDeg_single_le LL S v)
  rw [divDer_zero', ← X_eq_monomial', Nat.cast_one] at hv
  exact hv

theorem valS_pderiv_of (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = false) :
    valS LL S F ≤ valS LL S (pderiv v F) := by
  have hv := flt_op_valS LL S F 0 (Finsupp.single v 1) 0
    (by rw [covDeg_zero', vecDeg_single_of LL S v h])
  rw [divDer_single_one, MvPolynomial.monomial_zero', C_1, one_mul, Nat.cast_zero,
    WithTop.coe_zero, add_zero] at hv
  exact hv

theorem valS_pderiv (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) :
    valS LL S F ≤ valS LL S (pderiv v F) + ((1 : ℤ) : WithTop ℤ) := by
  have hv := flt_op_valS LL S F 0 (Finsupp.single v 1) 1
    (by rw [covDeg_zero', zero_add]; exact vecDeg_single_le LL S v)
  rw [divDer_single_one, MvPolynomial.monomial_zero', C_1, one_mul, Nat.cast_one] at hv
  exact hv

private lemma withTop_int_le_of_forall_coe_le {a b : WithTop ℤ}
    (h : ∀ t : ℤ, (t : WithTop ℤ) ≤ a → (t : WithTop ℤ) ≤ b) : a ≤ b := by
  cases b with
  | top => exact le_top
  | coe m =>
    cases a with
    | top => exact absurd (WithTop.coe_le_coe.mp (h (m + 1) le_top)) (by omega)
    | coe k => exact h k le_rfl

theorem valS_X_mul_out (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) (h : v.1 ∉ S) :
    valS LL S (X v * F) = valS LL S F := by
  apply le_antisymm
  · apply withTop_int_le_of_forall_coe_le
    intro t ht
    rw [flt_le_valS] at ht ⊢
    rw [map_mul, twistSub_X_out LL S _ v h] at ht
    exact mem_of_X_mul_mem v _ ht
  · exact valS_X_mul_of LL S F v (fun hv => absurd hv h)

theorem maxTwistDegree_X_mul_le_of (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = false) :
    lam1S LL S (X v * F) ≤ lam1S LL S F := by
  have hv := flt_op_lam1S LL S F (Finsupp.single v 1) 0 0
    (by rw [vecDeg_single_of LL S v h, covDeg_zero'])
  rw [divDer_zero', ← X_eq_monomial', Nat.cast_zero, WithBot.coe_zero, add_zero] at hv
  exact hv

theorem maxTwistDegree_X_mul_le_add_one (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) :
    lam1S LL S (X v * F) ≤ lam1S LL S F + ((1 : ℤ) : WithBot ℤ) := by
  have hv := flt_op_lam1S LL S F (Finsupp.single v 1) 0 1
    (by rw [covDeg_zero', add_zero]; exact vecDeg_single_le LL S v)
  rw [divDer_zero', ← X_eq_monomial', Nat.cast_one] at hv
  exact hv

theorem maxTwistDegree_pderiv_le_of (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) (h : v.1 ∈ S → LL.vec v.1 = true) :
    lam1S LL S (pderiv v F) ≤ lam1S LL S F := by
  have hv := flt_op_lam1S LL S F 0 (Finsupp.single v 1) 0
    (by rw [vecDeg_zero', covDeg_single_of LL S v h])
  rw [divDer_single_one, MvPolynomial.monomial_zero', C_1, one_mul, Nat.cast_zero,
    WithBot.coe_zero, add_zero] at hv
  exact hv

theorem maxTwistDegree_pderiv_le_add_one (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) :
    lam1S LL S (pderiv v F) ≤ lam1S LL S F + ((1 : ℤ) : WithBot ℤ) := by
  have hv := flt_op_lam1S LL S F 0 (Finsupp.single v 1) 1
    (by rw [vecDeg_zero', zero_add]; exact covDeg_single_le LL S v)
  rw [divDer_single_one, MvPolynomial.monomial_zero', C_1, one_mul, Nat.cast_one] at hv
  exact hv

private lemma withBot_int_le_of_forall_le_coe {a b : WithBot ℤ}
    (h : ∀ M : ℤ, b ≤ (M : WithBot ℤ) → a ≤ (M : WithBot ℤ)) : a ≤ b := by
  cases a with
  | bot => exact bot_le
  | coe k =>
    cases b with
    | bot => exact absurd (WithBot.coe_le_coe.mp (h (k - 1) bot_le)) (by omega)
    | coe m => exact h m le_rfl

theorem maxTwistDegree_X_mul_of_not_mem (F : MvPolynomial (ι × Fin n) R) (v : ι × Fin n) (h : v.1 ∉ S) :
    lam1S LL S (X v * F) = lam1S LL S F := by
  apply le_antisymm
  · exact maxTwistDegree_X_mul_le_of LL S F v (fun hv => absurd hv h)
  · apply withBot_int_le_of_forall_le_coe
    intro M hM
    rw [flt_lam1S_le] at hM ⊢
    rw [map_mul, twistSub_X_out LL S _ v h] at hM
    exact mem_of_X_mul_mem v _ hM

end Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
