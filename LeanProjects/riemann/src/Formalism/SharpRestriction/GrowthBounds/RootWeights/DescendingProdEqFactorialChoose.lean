import Formalism.SharpRestriction.GrowthBounds.RootWeights.PolarizationDividedPowerSumSucc

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section v2dpCon

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ}

def polarizationSource (LL : Letters ι) (a b : Fin n) (l : ι) : ι × Fin n := if LL.vec l then (l, b) else (l, a)

def polarizationTarget (LL : Letters ι) (a b : Fin n) (l : ι) : ι × Fin n := if LL.vec l then (l, a) else (l, b)

def polarizationLetterSign (R : Type*) [CommRing R] (LL : Letters ι) (l : ι) : R := if LL.vec l then 1 else -1

theorem polarizationSource_injective (LL : Letters ι) (a b : Fin n) : Function.Injective (polarizationSource LL a b) := by
  intro l l' h
  have h1 : ∀ l₀, (polarizationSource LL a b l₀).1 = l₀ := fun l₀ => by
    unfold polarizationSource; split_ifs <;> rfl
  rw [← h1 l, h, h1 l']

theorem polarizationTarget_ne_source (LL : Letters ι) (a b : Fin n) (hab : a ≠ b) (l l' : ι) :
    polarizationTarget LL a b l' ≠ polarizationSource LL a b l := by
  intro h
  have e1 : (polarizationTarget LL a b l').1 = l' := by unfold polarizationTarget; split_ifs <;> rfl
  have e2 : (polarizationSource LL a b l).1 = l := by unfold polarizationSource; split_ifs <;> rfl
  have hl : l' = l := by rw [← e1, h, e2]
  subst hl
  unfold polarizationTarget polarizationSource at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at h
  · exact hab h.2
  · exact hab h.2.symm

open Classical in
theorem glAct_eq_sum_polarizations (LL : Letters ι) (S : Set ι) (a b : Fin n) :
    glAct R LL S a b = ∑ l ∈ Finset.univ.filter (· ∈ S),
      polarizationDerivation (polarizationLetterSign R LL) (polarizationSource LL a b) (polarizationTarget LL a b) l := by
  rw [glAct, Finset.sum_filter]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp_all [polarizationDerivation, polarizationLetterSign, polarizationSource, polarizationTarget]

open Classical in
theorem divPowMono_eq_monomialSum (LL : Letters ι) (S : Set ι) (a b : Fin n) (k : ℕ) (m : ι × Fin n →₀ ℕ) :
    divPowMono R LL S a b k m =
      dividedPowerMonomialSum (polarizationLetterSign R LL) (polarizationSource LL a b) (polarizationTarget LL a b) (Finset.univ.filter (· ∈ S)) k m := by
  unfold divPowMono dividedPowerMonomialSum
  refine Finset.sum_congr rfl fun f hf => ?_
  have hsub : f.support ⊆ Finset.univ.filter (· ∈ S) := (Finset.mem_finsuppAntidiag.1 hf).2
  unfold dividedPowerMonomialTerm dividedPowerExponent dividedPowerCoefficient
  congr 1
  rw [← Finset.prod_subset hsub (f := fun l => polarizationLetterSign R LL l ^ f l *
    ((m (polarizationSource LL a b l)).choose (f l) : R)) ?_]
  · refine Finset.prod_congr rfl fun l _ => ?_
    by_cases hv : LL.vec l <;> simp [polarizationLetterSign, polarizationSource, hv]
  · intro l _ hl
    rw [Finsupp.notMem_support_iff.1 hl]
    simp

theorem glAct_comp_divPow (LL : Letters ι) (S : Set ι) (a b : Fin n) (hab : a ≠ b) (k : ℕ) :
    glAct R LL S a b ∘ₗ divPow R LL S a b k = (k + 1) • divPow R LL S a b (k + 1) := by
  classical
  refine (MvPolynomial.basisMonomials (ι × Fin n) R).ext fun m => ?_
  rw [LinearMap.comp_apply, LinearMap.smul_apply]
  simp only [divPow, Module.Basis.constr_basis]
  rw [divPowMono_eq_monomialSum, divPowMono_eq_monomialSum, glAct_eq_sum_polarizations]
  exact polarization_dividedPowerSum_succ _ _ _ (polarizationSource_injective LL a b) (polarizationTarget_ne_source LL a b hab) _ m k

theorem divPow_zero' (LL : Letters ι) (S : Set ι) (a b : Fin n) : divPow R LL S a b 0 = LinearMap.id := by
  classical
  refine (MvPolynomial.basisMonomials (ι × Fin n) R).ext fun m => ?_
  rw [LinearMap.id_apply]
  simp only [divPow, Module.Basis.constr_basis]
  rw [divPowMono_eq_monomialSum, dividedPowerMonomialSum_zero, MvPolynomial.coe_basisMonomials]

theorem glAct_pow_eq_factorial_divPow (LL : Letters ι) (S : Set ι) (a b : Fin n) (hab : a ≠ b) (k : ℕ) :
    (glAct R LL S a b : Module.End R (MvPolynomial (ι × Fin n) R)) ^ k = k.factorial • divPow R LL S a b k := by
  induction k with
  | zero => rw [pow_zero, divPow_zero', Nat.factorial_zero, one_smul]; rfl
  | succ k ih =>
    rw [pow_succ', ih, Module.End.mul_eq_comp, LinearMap.comp_smul, glAct_comp_divPow LL S a b hab k,
      smul_smul]
    congr 1
    rw [Nat.factorial_succ]
    ring

theorem X_mul_pderiv_monomial' {σ : Type*} (v : σ) (m : σ →₀ ℕ) (c : R) :
    X v * pderiv v (monomial m c) = ((m v : ℕ) : R) • monomial m c := by
  classical
  rw [MvPolynomial.pderiv_monomial]
  by_cases h : m v = 0
  · simp [h]
  · have hle : Finsupp.single v 1 ≤ m := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h)
    rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, add_tsub_cancel_of_le hle,
      MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]

theorem glAct_diagonal_monomial (LL : Letters ι) (S : Set ι) (a : Fin n) (m : ι × Fin n →₀ ℕ) (c : R) :
    glAct R LL S a a (monomial m c) = ((wtS LL S m a : ℤ) : R) • monomial m c := by
  classical
  rw [glAct, LinearMap.sum_apply, wtS, Int.cast_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp_all [-MvPolynomial.pderiv_monomial, X_mul_pderiv_monomial']

theorem list_prod_shifted_eigen {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (T : Module.End K V) (w : K) (x : V)
    (h : T x = w • x) (L : List ℕ) :
    ((L.map fun j : ℕ => T - (j : K) • (1 : Module.End K V)).prod) x = ((L.map fun j : ℕ => w - (j : K)).prod) • x := by
  induction L with
  | nil => simp
  | cons j L ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, map_smul,
      LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, h]
    rw [← sub_smul, smul_smul, mul_comm]

theorem list_range_prod_eq_finset_prod {K : Type*} [CommRing K] (w : K) (k : ℕ) :
    ((List.range k).map fun j : ℕ => w - (j : K)).prod = ∏ j ∈ Finset.range k, (w - (j : K)) := by
  rw [Finset.prod_eq_multiset_prod, Finset.range_val, Multiset.range, Multiset.map_coe,
    Multiset.prod_coe]

theorem descending_prod_eq_factorial_choose (z : ℤ) (k : ℕ) : ∏ j ∈ Finset.range k, (z - (j : ℤ)) = (k.factorial : ℤ) * Ring.choose z k := by
  rw [← descPochhammer_eval_eq_prod_range, Polynomial.eval_eq_smeval,
    Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]

end v2dpCon

theorem dividedPower_formula_char_zero : DividedPowerFormulaCharZero := by
  intro R _ _ ι _ LL n S a b k hab
  show ((k.factorial : R)⁻¹) • (glAct R LL S a b) ^ k = divPow R LL S a b k
  rw [glAct_pow_eq_factorial_divPow LL S a b hab k, ← Nat.cast_smul_eq_nsmul R, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_smul]

theorem binomial_formula_char_zero : BinomialFormulaCharZero := by
  intro R _ _ ι _ LL n S a k
  classical
  refine (MvPolynomial.basisMonomials (ι × Fin n) R).ext fun m => ?_
  rw [binomPol, Module.Basis.constr_basis, MvPolynomial.coe_basisMonomials]
  show ((k.factorial : R)⁻¹ • ((List.range k).map fun j : ℕ =>
    glAct R LL S a a - (j : R) • (1 : Module.End R (MvPolynomial (ι × Fin n) R))).prod) (monomial m 1) = _
  rw [LinearMap.smul_apply, list_prod_shifted_eigen (glAct R LL S a a) ((wtS LL S m a : ℤ) : R) (monomial m 1)
    (glAct_diagonal_monomial LL S a m 1), list_range_prod_eq_finset_prod, smul_smul]
  have hc : ∏ j ∈ Finset.range k, (((wtS LL S m a : ℤ) : R) - (j : R)) =
      (((k.factorial : ℤ) * Ring.choose (wtS LL S m a) k : ℤ) : R) := by
    rw [← descending_prod_eq_factorial_choose]
    push_cast
    rfl
  rw [hc]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero k), one_mul,
    MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

end Formalism.MainNotions.G.GLWeightTheory
