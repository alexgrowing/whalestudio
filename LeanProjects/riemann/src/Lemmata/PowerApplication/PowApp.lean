import Mathlib

open Polynomial Finset

namespace Bl.PowerApplication

variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]

private theorem pow_app {T : Module.End ℂ Y} {z : ℂ} {f : Y} (hf : T f = z • f) (n : ℕ) :
    (T ^ n) f = z ^ n • f := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hf, smul_smul, pow_succ]

theorem goal1 {T : Module.End ℂ Y} {z : ℂ} {f : Y} (hf : T f = z • f) (p : ℂ[X]) :
    aeval T p f = p.eval z • f := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply, hp, hq, eval_add, add_smul]
  | monomial n a =>
    rw [aeval_monomial, Module.End.mul_apply, pow_app hf, Module.algebraMap_end_apply,
      smul_smul, eval_monomial]

end Bl.PowerApplication
