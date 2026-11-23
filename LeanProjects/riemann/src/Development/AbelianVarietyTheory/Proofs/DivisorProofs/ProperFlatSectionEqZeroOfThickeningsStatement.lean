import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperFlatSectionEqZeroOfThickenings
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickFibIsPullback
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.SpecialConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_flat_section_eq_zero_of_thickenings : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)) [IsProper f] [Flat f] (s : Γ(Y, ⊤)), (∀ n, (thickι f n).appTop.hom s = 0) → s = 0 := by
  first | exact @GlobalTheory.SpecialConn.eq_zero_of_thickι | exact GlobalTheory.SpecialConn.eq_zero_of_thickι | (intros; apply GlobalTheory.SpecialConn.eq_zero_of_thickι <;> assumption)
