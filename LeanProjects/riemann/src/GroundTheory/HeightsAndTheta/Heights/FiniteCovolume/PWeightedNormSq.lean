import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField

theorem WeightedNormSq.proof (E : Type*) [Field E] [NumberField E] : WeightedNormSq.Statement E := by
  intro c hc a
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Fin.sum_univ_two]
  simp only [weightedEmbed, AddMonoidHom.coe_mk, ZeroHom.coe_mk, PiLp.toLp_apply, Real.norm_eq_abs,
    sq_abs, show ((1 : Fin 2) = 0) = False from by decide, ↓reduceIte]
  rw [mul_pow, mul_pow, Real.sq_sqrt (hc w), Complex.sq_norm, Complex.normSq_apply]
  ring

end GroundTheory.Heights₂.Heights.FiniteCovolume
