import Mathlib
import Formalism.PeriodIntegrals.IsoDerivB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDerivative.ExistsOePerm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDerivative.ApplyAt0EqSum

open Finset

noncomputable section

namespace PI.IsoDerivBFintype

open PI.IsoDerivB

section expand

variable {T : Type} {N N' : ℕ} (s : T → ℂ) (y' : T → Matrix (Fin N') (Fin N') ℂ)

def gD : FrV T N → MvPolynomial (Idx T N N') ℂ := fun k => ∑ b : Fin N',
    MvPolynomial.C (s k.1 * (if h : (k.2.2 : ℕ) < N' then y' k.1 b ⟨k.2.2, h⟩ else 0)) *
      MvPolynomial.X ((k.1, b, k.2.1) : Idx T N N')

theorem polD_eq_aeval (Q : MvPolynomial (FrV T N) ℂ) :
    polD s Q y' = MvPolynomial.aeval (gD s y') Q := rfl

theorem minor_expand (τ : T) {h : ℕ} (Jc : Fin h ↪o Fin N) :
    MvPolynomial.aeval (gD s y') (Matrix.det (Matrix.of fun i j : Fin h =>
      if hj : (j : ℕ) < N then (MvPolynomial.X (τ, Jc i, ⟨j, hj⟩) : MvPolynomial (FrV T N) ℂ)
      else 0))
    = ∑ I : Fin h ↪o Fin N', Matrix.det (Matrix.of fun i k : Fin h =>
        MvPolynomial.C (s τ) *
          (MvPolynomial.X ((τ, I i, Jc k) : Idx T N N') : MvPolynomial (Idx T N N') ℂ)) *
      MvPolynomial.C (Matrix.det (Matrix.of fun i j : Fin h => colsOf (y' τ) (I i) (j : ℕ))) := by
  have hN := le_of_oe Jc
  let A : Matrix (Fin h) (Fin N') (MvPolynomial (Idx T N N') ℂ) :=
    Matrix.of fun i b => MvPolynomial.C (s τ) * MvPolynomial.X (τ, b, Jc i)
  let B : Matrix (Fin N') (Fin h) (MvPolynomial (Idx T N N') ℂ) :=
    Matrix.of fun b j => MvPolynomial.C (colsOf (y' τ) b (j : ℕ))
  have hAB : (MvPolynomial.aeval (gD s y')).mapMatrix (Matrix.of fun i j : Fin h =>
      if hj : (j : ℕ) < N then (MvPolynomial.X (τ, Jc i, ⟨j, hj⟩) : MvPolynomial (FrV T N) ℂ)
      else 0) = A * B := by
    refine Matrix.ext fun i j => ?_
    have hj : (j : ℕ) < N := lt_of_lt_of_le j.2 hN
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, dif_pos hj,
      MvPolynomial.aeval_X, gD, Matrix.mul_apply, A, B, colsOf]
    apply Finset.sum_congr rfl
    intro b _
    rw [MvPolynomial.C_mul]
    ring
  rw [AlgHom.map_det, hAB, cauchyBinet]
  refine Finset.sum_congr rfl fun I _ => ?_
  congr 1
  · rw [← Matrix.det_transpose (A.submatrix id I)]
    rfl
  · rw [RingHom.map_det]
    rfl

variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (tp : Lt → T) (nu : Lt → YoungDiagram)

theorem aeval_mY (J : ColChoice N nu) :
    MvPolynomial.aeval (gD s y') (mY tp nu J) =
      ∑ I : ColChoice N' nu, PIJ tp nu s I J * MvPolynomial.C (minY N' nu I (frC tp y')) := by
  unfold mY
  rw [map_prod]
  simp only [map_prod, minor_expand]
  rw [Finset.prod_congr rfl fun z _ => Fintype.prod_sum _, Fintype.prod_sum]
  refine Fintype.sum_equiv (Equiv.refl _) _ _ fun I => ?_
  simp only [Equiv.refl_apply, PIJ, minY, Finset.prod_mul_distrib, map_prod]

end expand

theorem isoDerivB : IsoDerivB := by
  intro Lt T _ _ _ tp N N' nu s Θ φ Q hQ y'
  rw [polD_eq_aeval, Q_eq tp nu φ Q hQ, map_sum]
  simp only [map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, aeval_mY]
  rw [applyAt0_sum]
  simp only [applyAt0_C_mul, applyAt0_sum, applyAt0_mul_C]
  unfold canC prC hvC AOp
  rw [finsum_eq_sum_of_fintype]
  simp only [finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end PI.IsoDerivBFintype
