import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantVanishingAtZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishAt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_vanishing_at_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.DetEqv.VanishAt k 0 := by
  first | exact @GlobalTheory.DetEqv.vanishAt_zero | exact GlobalTheory.DetEqv.vanishAt_zero | (intros; apply GlobalTheory.DetEqv.vanishAt_zero <;> assumption)
