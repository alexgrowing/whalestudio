import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperFlatAdicSectionsLift
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickFibIsPullback
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.SpecialConn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_flat_adic_sections_lift : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)) [IsProper f] [Flat f] (e : ∀ n, Γ(thickFib f n, ⊤)), (∀ n, (thickTr f n).appTop.hom (e (n + 1)) = e n) → ∃ s : Γ(Y, ⊤), ∀ n, (thickι f n).appTop.hom s = e n := by
  first | exact @GlobalTheory.SpecialConn.exists_global_of_thick | exact GlobalTheory.SpecialConn.exists_global_of_thick | (intros; apply GlobalTheory.SpecialConn.exists_global_of_thick <;> assumption)
