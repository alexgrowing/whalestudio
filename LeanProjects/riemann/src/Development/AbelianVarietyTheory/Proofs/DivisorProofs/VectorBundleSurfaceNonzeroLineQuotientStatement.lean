import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleSurfaceNonzeroLineQuotient
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_bundle_surface_nonzero_line_quotient : ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T], IsProjSurface k T → ∀ (E : T.Modules) (r : ℕ), IsVB E (r + 1) → ∃ (L : T.Modules) (φ : E ⟶ L), IsVB L 1 ∧ φ ≠ 0 := by
  first | exact @GlobalTheory.Proof.Div.vector_bundle_surface_nonzero_line_quotient.exists_hom_isVB_one_ne_zero | exact GlobalTheory.Proof.Div.vector_bundle_surface_nonzero_line_quotient.exists_hom_isVB_one_ne_zero | (intros; apply GlobalTheory.Proof.Div.vector_bundle_surface_nonzero_line_quotient.exists_hom_isVB_one_ne_zero <;> assumption)
