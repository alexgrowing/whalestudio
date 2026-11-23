import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaExistence.TermBound

namespace PI.ThGW

namespace Hol

variable {T I J : Type} [Fintype T] [Fintype I] [Fintype J]

lemma hf_add_left (A : ℝ) (z z' w : T → I → J → ℂ) :
    HfG A (z + z') w = HfG A z w + HfG A z' w := by
  simp only [HfG, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

lemma hf_smul_left (A : ℝ) (c : ℂ) (z w : T → I → J → ℂ) :
    HfG A (c • z) w = c * HfG A z w := by
  simp only [HfG, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

noncomputable def hl (A : ℝ) (v : T → I → J → ℂ) : (T → I → J → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => HfG A z v
      map_add' := fun z z' => hf_add_left A z z' v
      map_smul' := fun c z => by simp only [hf_smul_left, smul_eq_mul, RingHom.id_apply] }

end Hol

end PI.ThGW
