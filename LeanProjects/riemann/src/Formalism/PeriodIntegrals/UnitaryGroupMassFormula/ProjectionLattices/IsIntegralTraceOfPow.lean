import Mathlib
import Formalism.PeriodIntegrals.SameFormAllLevels
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ArithmeticCylinders

noncomputable section

namespace PI.Dv.GLP

open Polynomial

theorem eigen_pow_eq_one {L : Type} [Field L] {d : Type} [Fintype d] [DecidableEq d]
    (M : Matrix d d L) (n : ℕ) (hM : M ^ n = 1) (μ : L) (hμ : M.charpoly.IsRoot μ) : μ ^ n = 1 :=
  _root_.UpperTheory.Reformulated.B.ArithmeticCylinders.eigen_pow_eq_one M n hM μ hμ

theorem isIntegral_trace_of_pow {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (f : Module.End K W) (n : ℕ) (hn : 0 < n) (hf : f ^ n = 1) :
    IsIntegral ℤ (LinearMap.trace K W f) := by
  classical
  let b := Module.finBasis K W
  let L := AlgebraicClosure K
  let M := LinearMap.toMatrix b b f
  have hMn : M ^ n = 1 := by
    show LinearMap.toMatrix b b f ^ n = 1
    rw [LinearMap.toMatrix_pow, hf, LinearMap.toMatrix_one]
  let M' : Matrix _ _ L := M.map (algebraMap K L)
  have hM'n : M' ^ n = 1 := by
    have : M' ^ n = (M ^ n).map (algebraMap K L) :=
      (RingHom.map_pow (algebraMap K L).mapMatrix M n).symm
    rw [this, hMn]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have htr : algebraMap K L (LinearMap.trace K W f) = M'.trace := by
    rw [LinearMap.trace_eq_matrix_trace K b]
    exact AddMonoidHom.map_trace (algebraMap K L) M
  have hint : IsIntegral ℤ M'.trace := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    refine IsIntegral.multiset_sum fun μ hμ => ?_
    have h1 : μ ^ n = 1 := eigen_pow_eq_one M' n hM'n μ (Polynomial.isRoot_of_mem_roots hμ)
    exact IsIntegral.of_pow hn (by rw [h1]; exact isIntegral_one)
  rw [← htr] at hint
  exact (isIntegral_algebraMap_iff (algebraMap K L).injective).1 hint

end PI.Dv.GLP
