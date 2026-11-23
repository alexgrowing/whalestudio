import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory.TorusExp

theorem modulus_exp_eq {F : Type} [Field F] [NumberField F] {n r : ℕ} (v : Fin r → ℝ) :
    (modulus F n fun i => Real.exp (v i)) =
      Real.exp (-(2 * Module.finrank ℚ F * ∑ i : Fin r, (i.val - (n - 1) / 2 : ℝ) * v i)) ^ 2 := by
  rw [← Real.exp_nat_mul, Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.mul_sum, Real.exp_sum, modulus]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Real.rpow_intCast, ← Real.exp_mul]
  congr 1
  push_cast
  ring

theorem norm_expChar_single {F : Type} [Field F] [NumberField F] {n r : ℕ} (s : Fin r → ℂ) (k : Fin r) (c : ℝ) :
    ‖expChar F n s (Pi.single k c)‖ = Real.exp (2 * Module.finrank ℚ F * c * ((s k).re - (negRho n r k).re)) := by
  rw [expChar, modulus_exp_eq, Real.sqrt_sq (Real.exp_pos _).le, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.norm_exp, ← Real.exp_add]
  congr 1
  simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [negRho, Complex.mul_re]
  ring

end GlobalTheory.TorusExp
