import Formalism.SharpRestriction.GrowthBounds.RootWeights.MatrixSubstTransvectionX

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G

theorem prod_monomial_eq_monomial_sum_prod {B σ α : Type*} [CommRing B] (s : Finset α) (f : α → σ →₀ ℕ) (c : α → B) :
    ∏ i ∈ s, monomial (f i) (c i) = monomial (∑ i ∈ s, f i) (∏ i ∈ s, c i) := by
  first
  | exact (monomial_sum_index s f c).symm
  | classical
    refine Finset.induction_on s (by simp) ?_
    intro i s hi ih
    rw [prod_insert hi, prod_insert hi, sum_insert hi, ih, monomial_mul]

section mono

variable {B : Type*} [CommRing B] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι)
  (a b : Fin n) (t : B) (m : ι × Fin n →₀ ℕ)

open Classical in

def sourceExp (l : ι) : ℕ := if l ∈ S then m (sourceVar LL a b l) else 0

def sourceVariableExponent : ι × Fin n →₀ ℕ := ∑ l : ι, Finsupp.single (sourceVar LL a b l) (sourceExp LL S a b m l)

def shiftedExponent (p : ι → ℕ) : ι × Fin n →₀ ℕ :=
  (m - ∑ l : ι, Finsupp.single (sourceVar LL a b l) (p l)) + ∑ l : ι, Finsupp.single (targetVar LL a b l) (p l)

def rootShiftCoefficient (B : Type*) [CommRing B] {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (a b : Fin n)
    (m : ι × Fin n →₀ ℕ) (p : ι → ℕ) : B :=
  ∏ l : ι, (if LL.vec l then ((m (l, b)).choose (p l) : B) else (-1 : B) ^ (p l) * ((m (l, a)).choose (p l) : B))

theorem sourcePart_le : sourceVariableExponent LL S a b m ≤ m := by
  classical
  rw [Finsupp.le_def]
  intro v
  unfold sourceVariableExponent
  rw [sum_single_sourceVar_apply]
  split_ifs with h
  · unfold sourceExp
    split_ifs
    · exact (congrArg m h.symm).le
    · exact Nat.zero_le _
  · exact Nat.zero_le _

theorem sub_sourcePart_sourceVar (l : ι) (hl : l ∈ S) : (m - sourceVariableExponent LL S a b m) (sourceVar LL a b l) = 0 := by
  classical
  rw [Finsupp.tsub_apply]
  unfold sourceVariableExponent
  rw [sum_single_sourceVar_apply, sourceVar_fst, if_pos rfl]
  unfold sourceExp
  rw [if_pos hl]
  exact Nat.sub_self _

variable {R : Type*} [CommRing R] (φ : R →+* B)

theorem matrixSubst_transvection_monomial_of_fixed (m0 : ι × Fin n →₀ ℕ) (h0 : ∀ l ∈ S, m0 (sourceVar LL a b l) = 0) :
    matrixSubst LL S φ (Matrix.transvection a b t) (Matrix.transvection a b (-t)) (monomial m0 1) = monomial m0 1 := by
  classical
  simp only [monomial_eq, map_one, one_mul, Finsupp.prod, map_prod, map_pow]
  refine Finset.prod_congr rfl fun v hv => ?_
  have hv' : ¬ (v.1 ∈ S ∧ v = sourceVar LL a b v.1) := by
    rintro ⟨hS, he⟩
    exact (Finsupp.mem_support_iff.1 hv) ((congrArg m0 he).trans (h0 _ hS))
  rw [matrixSubst_transvection_X, if_neg hv']

theorem matrixSubst_transvection_monomial_prod :
    matrixSubst LL S φ (Matrix.transvection a b t) (Matrix.transvection a b (-t)) (monomial m 1) =
      monomial (m - sourceVariableExponent LL S a b m) 1 *
        ∏ l : ι, (C (letterSign B LL l * t) * X (targetVar LL a b l) + X (sourceVar LL a b l)) ^ (sourceExp LL S a b m l) := by
  classical
  have hsplit : (monomial m (1 : R) : MvPolynomial (ι × Fin n) R) =
      monomial (m - sourceVariableExponent LL S a b m) 1 * monomial (sourceVariableExponent LL S a b m) 1 := by
    rw [monomial_mul, one_mul, tsub_add_cancel_of_le (sourcePart_le LL S a b m)]
  have hprod : (monomial (sourceVariableExponent LL S a b m) (1 : R) : MvPolynomial (ι × Fin n) R) =
      ∏ l : ι, X (sourceVar LL a b l) ^ sourceExp LL S a b m l := by
    unfold sourceVariableExponent
    simp only [X_pow_eq_monomial]
    rw [prod_monomial_eq_monomial_sum_prod, Finset.prod_const_one]
  rw [hsplit, map_mul, matrixSubst_transvection_monomial_of_fixed (LL := LL) (S := S) (a := a) (b := b) (t := t)
    (φ := φ) (m0 := m - sourceVariableExponent LL S a b m) (h0 := sub_sourcePart_sourceVar LL S a b m)]
  congr 1
  rw [hprod, map_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [map_pow]
  by_cases hl : l ∈ S
  · rw [matrixSubst_transvection_X, sourceVar_fst, if_pos ⟨hl, rfl⟩, add_comm]
  · have he : sourceExp LL S a b m l = 0 := by
      unfold sourceExp
      rw [if_neg hl]
    rw [he, pow_zero, pow_zero]

private theorem letterSign_pow_mul_choose_sourceExp (p : ι → ℕ) (l : ι) (hpl : p l ≤ sourceExp LL S a b m l) :
    letterSign B LL l ^ p l * ((sourceExp LL S a b m l).choose (p l) : B) =
      (if LL.vec l then ((m (l, b)).choose (p l) : B) else (-1 : B) ^ (p l) * ((m (l, a)).choose (p l) : B)) := by
  classical
  by_cases hS : l ∈ S
  · have he : sourceExp LL S a b m l = m (sourceVar LL a b l) := by
      unfold sourceExp
      rw [if_pos hS]
    rw [he]
    unfold sourceVar letterSign
    cases LL.vec l <;> simp
  · have he : sourceExp LL S a b m l = 0 := by
      unfold sourceExp
      rw [if_neg hS]
    rw [he] at hpl ⊢
    have hp0 : p l = 0 := by omega
    rw [hp0]
    simp

theorem monomial_mul_prod_binomial_term (p : ι → ℕ) (hp : ∀ l, p l ≤ sourceExp LL S a b m l) :
    monomial (m - sourceVariableExponent LL S a b m) (1 : B) *
      ∏ l : ι, ((C (letterSign B LL l * t) * X (targetVar LL a b l)) ^ (p l) *
        X (sourceVar LL a b l) ^ (sourceExp LL S a b m l - p l) * (((sourceExp LL S a b m l).choose (p l) : ℕ) :
          MvPolynomial (ι × Fin n) B)) =
      C (t ^ (∑ l, p l)) * monomial (shiftedExponent LL a b m p) (rootShiftCoefficient B LL a b m p) := by
  classical
  have hfac : ∀ l : ι, (C (letterSign B LL l * t) * X (targetVar LL a b l)) ^ (p l) *
        X (sourceVar LL a b l) ^ (sourceExp LL S a b m l - p l) *
        (((sourceExp LL S a b m l).choose (p l) : ℕ) : MvPolynomial (ι × Fin n) B) =
      monomial (Finsupp.single (targetVar LL a b l) (p l) +
          Finsupp.single (sourceVar LL a b l) (sourceExp LL S a b m l - p l))
        ((letterSign B LL l * t) ^ (p l) * ((sourceExp LL S a b m l).choose (p l) : B)) := by
    intro l
    rw [← monomial_mul, ← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial]
    simp only [mul_pow, map_pow, map_mul, map_natCast]
    ring
  simp_rw [hfac]
  rw [prod_monomial_eq_monomial_sum_prod, monomial_mul, C_mul_monomial, one_mul]
  refine congrArg₂ (fun (s : ι × Fin n →₀ ℕ) (c : B) => (monomial s c : MvPolynomial (ι × Fin n) B)) ?_ ?_
  · have key : m - sourceVariableExponent LL S a b m +
        ∑ l : ι, Finsupp.single (sourceVar LL a b l) (sourceExp LL S a b m l - p l) =
        m - ∑ l : ι, Finsupp.single (sourceVar LL a b l) (p l) := by
      unfold sourceVariableExponent
      ext v
      rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.tsub_apply, sum_single_sourceVar_apply,
        sum_single_sourceVar_apply, sum_single_sourceVar_apply]
      split_ifs with h
      · have h1 := hp v.1
        have h2 : sourceExp LL S a b m v.1 ≤ m v := by
          unfold sourceExp
          split_ifs
          · exact (congrArg m h.symm).le
          · exact Nat.zero_le _
        omega
      · simp
    rw [Finset.sum_add_distrib, shiftedExponent, ← key, add_assoc,
      add_comm (∑ l : ι, Finsupp.single (targetVar LL a b l) (p l))]
  · unfold rootShiftCoefficient
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [← letterSign_pow_mul_choose_sourceExp (B := B) LL S a b m p l (hp l)]
    ring

open Classical in

theorem matrixSubst_transvection_monomial_sum :
    matrixSubst LL S φ (Matrix.transvection a b t) (Matrix.transvection a b (-t)) (monomial m 1) =
      ∑ p ∈ Fintype.piFinset (fun l : ι => Finset.range (sourceExp LL S a b m l + 1)),
        C (t ^ (∑ l, p l)) * monomial (shiftedExponent LL a b m p) (rootShiftCoefficient B LL a b m p) := by
  rw [matrixSubst_transvection_monomial_prod]
  simp_rw [add_pow]
  rw [Finset.prod_univ_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  refine monomial_mul_prod_binomial_term LL S a b t m p fun l => ?_
  have hl := Fintype.mem_piFinset.1 hp l
  rw [Finset.mem_range] at hl
  omega

end mono

end Formalism.MainNotions.G.GLWeightTheory
