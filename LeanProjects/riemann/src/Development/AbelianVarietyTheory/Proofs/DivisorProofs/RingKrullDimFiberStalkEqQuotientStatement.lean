import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimFiberStalkEqQuotient
import Mathlib
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringKrullDim_fiber_stalk_eq_quotient : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b), ringKrullDim ((π.fiber b).presheaf.stalk z) = ringKrullDim (Y.presheaf.stalk (π.fiberι b z) ⧸ (IsLocalRing.maximalIdeal (B.presheaf.stalk (π (π.fiberι b z)))).map (π.stalkMap (π.fiberι b z)).hom) := by
  first | exact @GlobalTheory.FibreStalk.ringKrullDim_stalk_fiber | exact GlobalTheory.FibreStalk.ringKrullDim_stalk_fiber | (intros; apply GlobalTheory.FibreStalk.ringKrullDim_stalk_fiber <;> assumption)
