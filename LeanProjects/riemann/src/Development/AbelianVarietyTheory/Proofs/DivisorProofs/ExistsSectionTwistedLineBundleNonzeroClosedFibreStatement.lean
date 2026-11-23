import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionTwistedLineBundleNonzeroClosedFibre
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_twistedLineBundle_nonzero_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (D : DegPre R) (α : D.X) (x : D.P.A.left), D.P.A.hom x = IsLocalRing.closedPoint R → ∃ σ : D.SecB 2 α, x ∈ nonzeroLocus σ := by
  first | exact @GlobalTheory.TwistGen.exists_sec_nonzeroLocus_closedFibre | exact GlobalTheory.TwistGen.exists_sec_nonzeroLocus_closedFibre | (intros; apply GlobalTheory.TwistGen.exists_sec_nonzeroLocus_closedFibre <;> assumption)
