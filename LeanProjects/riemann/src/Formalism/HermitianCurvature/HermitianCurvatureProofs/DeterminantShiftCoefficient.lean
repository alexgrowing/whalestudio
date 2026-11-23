import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapRWordsOfParts

open MvPolynomial Finset

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

theorem detShift_prod_coeff {σ ι : Type*} [Fintype ι] (h c : ι → MvPolynomial σ ℂ)
    (hh : ∀ i, (h i).IsHomogeneous 1) (hc : ∀ i, (c i).IsHomogeneous 0)
    (d : σ →₀ ℕ) (hd : d.degree = Fintype.card ι) :
    coeff d (∏ i, (h i + c i)) = coeff d (∏ i, h i) := by
  classical
  rw [Finset.prod_add, coeff_sum, Finset.sum_eq_single Finset.univ]
  · simp
  · intro S _ hS
    have hH : ((∏ i ∈ S, h i) * ∏ i ∈ univ \ S, c i).IsHomogeneous S.card := by
      have := (IsHomogeneous.prod S h (fun _ => 1) (fun i _ => hh i)).mul
        (IsHomogeneous.prod (univ \ S) c (fun _ => 0) (fun i _ => hc i))
      simpa using this
    apply hH.coeff_eq_zero
    rw [hd]
    intro hcard
    exact hS (Finset.eq_univ_of_card S hcard.symm)
  · intro hn
    exact absurd (Finset.mem_powerset.mpr (Finset.subset_univ _)) hn

def detShiftSub : Fin 2 → Polynomial ℂ := ![Polynomial.X, -1]

theorem detShift_aeval_monomial (d : Fin 2 →₀ ℕ) (a : ℂ) :
    aeval detShiftSub (monomial d a) = Polynomial.C (a * (-1) ^ d 1) * Polynomial.X ^ d 0 := by
  rw [aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  simp [detShiftSub, Polynomial.algebraMap_eq, map_mul, map_pow, map_neg]
  ring

theorem detShift_aeval_coeff (Q : MvPolynomial (Fin 2) ℂ) (t j : ℕ) (hj : j ≤ t)
    (hQ : Q.IsHomogeneous t) :
    (aeval detShiftSub Q).coeff (t - j) =
      (-1) ^ j * coeff (Finsupp.single (0 : Fin 2) (t - j) + Finsupp.single (1 : Fin 2) j) Q := by
  classical
  set D : Fin 2 →₀ ℕ := Finsupp.single (0 : Fin 2) (t - j) + Finsupp.single (1 : Fin 2) j with hD
  have hD0 : D 0 = t - j := by simp [hD]
  have hD1 : D 1 = j := by simp [hD]
  have hterm : ∀ d : Fin 2 →₀ ℕ, (aeval detShiftSub (monomial d (coeff d Q))).coeff (t - j) =
      if t - j = d 0 then coeff d Q * (-1) ^ d 1 else 0 := by
    intro d
    rw [detShift_aeval_monomial, Polynomial.coeff_C_mul_X_pow]
  conv_lhs => rw [Q.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff, Finset.sum_eq_single D]
  · rw [hterm, hD0, hD1, if_pos rfl, mul_comm]
  · intro d hd hne
    rw [hterm]
    split_ifs with h0
    · exfalso
      have hdeg : d.degree = t := by
        by_contra hne'
        exact (mem_support_iff.mp hd) (hQ.coeff_eq_zero hne')
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hdeg
      apply hne
      ext i
      fin_cases i
      · simp [hD0, ← h0]
      · simp only [Fin.mk_one, Fin.isValue, hD1]
        omega
    · rfl
  · intro hn
    rw [hterm, notMem_support_iff.mp hn]
    simp

theorem detShift_factor {t : ℕ} (M : Matrix (Fin t) (Fin t) ℂ) (σ : Equiv.Perm (Fin t)) (i : Fin t) :
    ((if σ i = i then X 0 - C ((i : ℕ) : ℂ) else 0) + X 1 * C (M (σ i) i) : MvPolynomial (Fin 2) ℂ) =
      ((if σ i = i then X 0 else 0) + X 1 * C (M (σ i) i)) +
        (if σ i = i then -C ((i : ℕ) : ℂ) else 0) := by
  split_ifs <;> ring

theorem detShift_hom {t : ℕ} (M : Matrix (Fin t) (Fin t) ℂ) (σ : Equiv.Perm (Fin t)) (i : Fin t) :
    ((if σ i = i then X 0 else 0) + X 1 * C (M (σ i) i) : MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 := by
  apply IsHomogeneous.add
  · split_ifs
    · exact isHomogeneous_X _ _
    · exact isHomogeneous_zero _ _ _
  · rw [mul_comm]
    exact isHomogeneous_C_mul_X _ _

theorem detShift_const {t : ℕ} (σ : Equiv.Perm (Fin t)) (i : Fin t) :
    ((if σ i = i then -C ((i : ℕ) : ℂ) else 0) : MvPolynomial (Fin 2) ℂ).IsHomogeneous 0 := by
  split_ifs
  · exact (isHomogeneous_C _ _).neg
  · exact isHomogeneous_zero _ _ _

theorem detShift_subst {t : ℕ} (M : Matrix (Fin t) (Fin t) ℂ) :
    aeval detShiftSub (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 2) ℂ) *
      ∏ i : Fin t, ((if σ i = i then X 0 else 0) + X 1 * C (M (σ i) i))) = M.charpoly := by
  rw [Matrix.charpoly, Matrix.det_apply', map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : σ i = i
  · rw [h]
    simp [detShiftSub, Matrix.charmatrix_apply_eq, Polynomial.algebraMap_eq]
    ring
  · simp [detShiftSub, h, Polynomial.algebraMap_eq]

theorem determinant_shift_coefficient : DetShiftCoeff := by
  intro t M j hj
  set D : Fin 2 →₀ ℕ := Finsupp.single (0 : Fin 2) (t - j) + Finsupp.single (1 : Fin 2) j with hD
  set Q : MvPolynomial (Fin 2) ℂ := ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 2) ℂ) *
      ∏ i : Fin t, ((if σ i = i then X 0 else 0) + X 1 * C (M (σ i) i)) with hQdef
  have hdeg : D.degree = t := by
    rw [hD, map_add, Finsupp.degree_single, Finsupp.degree_single]
    omega
  have hQ : Q.IsHomogeneous t := by
    apply IsHomogeneous.sum
    intro σ _
    rw [← map_intCast (C : ℂ →+* MvPolynomial (Fin 2) ℂ)]
    simpa using (isHomogeneous_C (Fin 2) (((Equiv.Perm.sign σ : ℤ) : ℂ))).mul
      (IsHomogeneous.prod (univ : Finset (Fin t)) _ (fun _ => 1) (fun i _ => detShift_hom M σ i))
  have hPQ : coeff D (∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin 2) ℂ) *
        ∏ i : Fin t, ((if σ i = i then X 0 - C ((i : ℕ) : ℂ) else 0) + X 1 * C (M (σ i) i))) =
      coeff D Q := by
    rw [hQdef, coeff_sum, coeff_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← map_intCast (C : ℂ →+* MvPolynomial (Fin 2) ℂ), coeff_C_mul, coeff_C_mul]
    congr 1
    simp_rw [detShift_factor M σ]
    exact detShift_prod_coeff _ _ (detShift_hom M σ) (detShift_const σ) D (by simp [hdeg])
  rw [hPQ]
  have hC := detShift_aeval_coeff Q t j hj hQ
  rw [hQdef, detShift_subst] at hC
  rw [hC, ← hQdef, ← mul_assoc, ← mul_pow, show ((-1 : ℂ) * -1) = 1 by norm_num, one_pow, one_mul]

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
