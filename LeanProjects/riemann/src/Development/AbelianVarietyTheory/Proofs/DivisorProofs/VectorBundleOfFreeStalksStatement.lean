import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleOfFreeStalks
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_bundle_of_free_stalks : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (F : X.Modules) [GlobalTheory.QCoh.IsFiniteQC F] (r : ℕ), (∀ x : X, Nonempty (Module.Basis (Fin r) (X.presheaf.stalk x) (F.presheaf.stalk x :))) → IsVB F r := by
  first | exact @GlobalTheory.VB.isVB_of_basis_stalk | exact GlobalTheory.VB.isVB_of_basis_stalk | (intros; apply GlobalTheory.VB.isVB_of_basis_stalk <;> assumption)
