import Mathlib

universe u_3 u_4

namespace Bl.general_b_fact_upper_variant

theorem goal1 :
  ∀ {LL : Type u_3} {M : Type u_4} [inst : Field.{u_3} LL] [inst_1 : AddCommGroup.{u_4} M]
  [inst_2 : Module.{u_3, u_4} LL M] (T : Module.End.{u_3, u_4} LL M) (a : LL) (y : M),
  Eq.{u_4 + 1} (DFunLike.coe.{u_4 + 1, u_4 + 1, u_4 + 1} T y) (HSMul.hSMul.{u_3, u_4, u_4} a y) →
    ∀ (p : Polynomial.{u_3} LL),
      Eq.{u_4 + 1}
        (DFunLike.coe.{u_4 + 1, u_4 + 1, u_4 + 1}
          (DFunLike.coe.{max (u_4 + 1) (u_3 + 1), u_3 + 1, u_4 + 1} (Polynomial.aeval.{u_3, u_4} T) p) y)
        (HSMul.hSMul.{u_3, u_4, u_4} (Polynomial.eval.{u_3} a p) y) := by
  intro LL M _ _ _ T a y h p
  induction p using Polynomial.induction_on with
  | C c =>
    simp only [Polynomial.aeval_C, Polynomial.eval_C, Module.algebraMap_end_apply]
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq, Polynomial.eval_add, add_smul]
  | monomial n c ih =>
    have e : (Polynomial.C c * Polynomial.X ^ (n + 1) : Polynomial LL)
        = (Polynomial.C c * Polynomial.X ^ n) * Polynomial.X := by ring
    rw [e, map_mul, Polynomial.aeval_X, Module.End.mul_apply, h, map_smul, ih, smul_smul]
    congr 1
    simp only [Polynomial.eval_mul, Polynomial.eval_X]
    ring

end Bl.general_b_fact_upper_variant
