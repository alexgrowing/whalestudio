import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.DetShiftNormOf
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ProdFactorialSupportSubSingle
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowDivAdj
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFockqLemmas

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace PI.HookSteps

theorem mulXAdj : MulXAdj := by
  intro σ v f g
  classical
  apply (Rat.castHom ℂ).injective
  show ((fockQ (X v * f) g : ℚ) : ℂ) = ((fockQ f (pderiv v g) : ℚ) : ℂ)
  rw [lfockq_cast, lfockq_cast, map_mul, map_X, Formalism.REAL.fischerInner_X_mul_left, pderiv_map]

private theorem fockQ_eq_sum_of_support_subset_of_type {σ : Type*} (f g : MvPolynomial σ ℚ) (S : Finset (σ →₀ ℕ))
    (h : f.support ⊆ S) :
    fockQ f g = ∑ m ∈ S, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) := by
  unfold fockQ
  refine Finset.sum_subset h fun m _ hm => ?_
  have : f.coeff m = 0 := by simpa using hm
  rw [this]
  ring

theorem fockQ_zero_left {σ : Type*} (g : MvPolynomial σ ℚ) : fockQ 0 g = 0 := by
  unfold fockQ
  simp

theorem fockQ_sum_left {σ ι : Type*} (s : Finset ι) (F : ι → MvPolynomial σ ℚ) (g : MvPolynomial σ ℚ) :
    fockQ (∑ i ∈ s, F i) g = ∑ i ∈ s, fockQ (F i) g := by
  classical
  exact Finset.induction_on s (by simp [fockQ_zero_left]) fun a s ha ih => by
    rw [Finset.sum_insert ha, Finset.sum_insert ha, lfockq_add_left, ih]

theorem fockQ_sum_right {σ ι : Type*} (s : Finset ι) (F : ι → MvPolynomial σ ℚ) (f : MvPolynomial σ ℚ) :
    fockQ f (∑ i ∈ s, F i) = ∑ i ∈ s, fockQ f (F i) := by
  unfold fockQ
  simp only [MvPolynomial.coeff_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem fockQ_zsmul_left {σ : Type*} (z : ℤ) (f g : MvPolynomial σ ℚ) :
    fockQ (z • f) g = (z : ℚ) * fockQ f g := by
  rw [← Int.cast_smul_eq_zsmul ℚ z f, fockQ_eq_sum_of_support_subset_of_type _ g f.support MvPolynomial.support_smul]
  unfold fockQ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem fockQ_zsmul_right {σ : Type*} (z : ℤ) (f g : MvPolynomial σ ℚ) :
    fockQ f (z • g) = (z : ℚ) * fockQ f g := by
  rw [← Int.cast_smul_eq_zsmul ℚ z g]
  unfold fockQ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem fockQ_listX (hX : MulXAdj) {σ : Type} (l : List σ) (f g : MvPolynomial σ ℚ) :
    fockQ ((l.map fun v => (X v : MvPolynomial σ ℚ)).prod * f) g =
      fockQ f ((l.map fun v => ((pderiv v : Derivation ℚ _ _).toLinearMap :
        Module.End ℚ (MvPolynomial σ ℚ))).prod g) := by
  induction l generalizing f g with
  | nil => simp
  | cons v l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [mul_assoc, mul_left_comm, ih, hX σ v]
    rfl

theorem detAdj_of (hX : MulXAdj) : DetAdj := by
  intro N f g
  classical
  rw [detX, Matrix.det_apply, Finset.sum_mul, fockQ_sum_left, detD, LinearMap.sum_apply,
    fockQ_sum_right]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, smul_mul_assoc, fockQ_zsmul_left, LinearMap.smul_apply, fockQ_zsmul_right]
  congr 1
  have h := fockQ_listX hX (List.ofFn fun j : Fin N => (σ j, j)) f g
  simp only [List.map_ofFn] at h
  rw [List.prod_ofFn] at h
  exact h

theorem determinant_adjugate : DetAdj := detAdj_of mulXAdj

end PI.HookSteps
