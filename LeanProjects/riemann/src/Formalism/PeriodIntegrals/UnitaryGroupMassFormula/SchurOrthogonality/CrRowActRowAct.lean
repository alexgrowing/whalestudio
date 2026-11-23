import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.InstMeasurableSpaceMat
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalD

noncomputable section

namespace PI.WSF

open Formalism.BasicNotions MvPolynomial

theorem cr_rowAct_X {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (w : Fin N × Fin N) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g (X w : MvPolynomial (Fin N × Fin N) ℂ) = ∑ b : Fin N, C (g w.1 b) * X (b, w.2) := by
  simp [Formalism.GradedWeylDivisibility.rowAct]

theorem cr_rowAct_C {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (a : ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g (C a : MvPolynomial (Fin N × Fin N) ℂ) = C a :=
  (Formalism.GradedWeylDivisibility.rowAct ℂ g).commutes a

theorem cr_evalM_rowAct {N : ℕ} (g x : Matrix (Fin N) (Fin N) ℂ) (s : MvPolynomial (Fin N × Fin N) ℂ) :
    evalM x (Formalism.GradedWeylDivisibility.rowAct ℂ g s) = evalM (g * x) s := by
  induction s using MvPolynomial.induction_on
  next a =>
    rw [cr_rowAct_C]
    simp [evalM]
  next p q hp hq =>
    simp only [map_add, evalM] at hp hq ⊢
    rw [hp, hq]
  next p v hp =>
    simp only [evalM, map_mul] at hp ⊢
    rw [hp, cr_rowAct_X]
    congr 1
    simp [Matrix.mul_apply]

theorem cr_rowAct_one {N : ℕ} (s : MvPolynomial (Fin N × Fin N) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (1 : Matrix (Fin N) (Fin N) ℂ) s = s := by
  have h : (Formalism.GradedWeylDivisibility.rowAct ℂ (1 : Matrix (Fin N) (Fin N) ℂ) :
      MvPolynomial (Fin N × Fin N) ℂ →ₐ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro w
    rw [cr_rowAct_X]
    simp [Matrix.one_apply]
  rw [h]
  rfl

theorem cr_rowAct_rowAct {N : ℕ} (g h : Matrix (Fin N) (Fin N) ℂ) (s : MvPolynomial (Fin N × Fin N) ℂ) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g (Formalism.GradedWeylDivisibility.rowAct ℂ h s) = Formalism.GradedWeylDivisibility.rowAct ℂ (h * g) s := by
  have hc : (Formalism.GradedWeylDivisibility.rowAct ℂ g).comp (Formalism.GradedWeylDivisibility.rowAct ℂ h) =
      (Formalism.GradedWeylDivisibility.rowAct ℂ (h * g) : MvPolynomial (Fin N × Fin N) ℂ →ₐ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) := by
    apply MvPolynomial.algHom_ext
    intro w
    rw [AlgHom.comp_apply, cr_rowAct_X, map_sum, cr_rowAct_X]
    simp only [map_mul, cr_rowAct_C, cr_rowAct_X, Matrix.mul_apply, map_sum, Finset.mul_sum, Finset.sum_mul,
      mul_assoc]
    exact Finset.sum_comm
  rw [← hc, AlgHom.comp_apply]

theorem cr_polyFun {N : ℕ} (s : MvPolynomial (Fin N × Fin N) ℂ) :
    ∀ L : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] ℂ, ∃ P : MvPolynomial (Fin N × Fin N) ℂ,
      ∀ g : Matrix (Fin N) (Fin N) ℂ, L (Formalism.GradedWeylDivisibility.rowAct ℂ g s) = evalM g P := by
  intro L
  let Φ : MvPolynomial (Fin N × Fin N) ℂ →ₐ[ℂ]
      MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) ℂ) :=
    aeval fun v => ∑ b : Fin N, C (X (v.1, b) : MvPolynomial (Fin N × Fin N) ℂ) * X (b, v.2)
  have hmap : ∀ g : Matrix (Fin N) (Fin N) ℂ,
      MvPolynomial.map (MvPolynomial.eval fun v : Fin N × Fin N => g v.1 v.2) (Φ s) = Formalism.GradedWeylDivisibility.rowAct ℂ g s := by
    intro g
    induction s using MvPolynomial.induction_on
    next a =>
      rw [cr_rowAct_C]
      simp [Φ]
    next p q hp hq =>
      simp only [map_add, hp, hq]
    next p w hp =>
      simp only [map_mul, hp, cr_rowAct_X]
      simp only [Φ, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
        MvPolynomial.eval_X]
  have hmono : ∀ (m : Fin N × Fin N →₀ ℕ) (a : ℂ), L (monomial m a) = a * L (monomial m 1) := by
    intro m a
    calc L (monomial m a) = L (a • monomial m (1 : ℂ)) := by rw [smul_monomial, smul_eq_mul, mul_one]
      _ = a * L (monomial m 1) := by rw [map_smul, smul_eq_mul]
  refine ⟨∑ m ∈ (Φ s).support, (Φ s).coeff m * C (L (monomial m 1)), fun g => ?_⟩
  rw [← hmap g]
  conv_lhs => rw [(Φ s).as_sum]
  simp only [map_sum, MvPolynomial.map_monomial, evalM, map_mul, MvPolynomial.eval_C]
  exact Finset.sum_congr rfl fun m _ => hmono m _

end PI.WSF
