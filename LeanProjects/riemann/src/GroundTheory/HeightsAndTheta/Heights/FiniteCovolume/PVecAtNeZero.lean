import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open Module NumberField

variable {E : Type*} [Field E] {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*}

theorem VecAtNeZero.proof (v : Basis ι E W) : VecAtNeZero.Statement v := by
  intro x hx w hw
  apply hx
  apply v.repr.injective
  ext i
  have h := congrFun hw i
  simp only [vecAt, Pi.zero_apply] at h
  simpa using (map_eq_zero_iff w.embedding w.embedding.injective).mp h

end GroundTheory.Heights₂.Heights.FiniteCovolume
