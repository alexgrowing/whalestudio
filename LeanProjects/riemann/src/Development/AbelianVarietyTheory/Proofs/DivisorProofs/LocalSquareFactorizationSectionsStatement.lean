import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSquareFactorizationSections
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallHeightOneExistsDvdMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_square_factorization_sections : ∀ (X : Scheme.{0}) (L2 : LB X) (h : L2.Sec) (x : X) (j₀ : L2.ι) (hx : x ∈ L2.U j₀) (u : (X.presheaf.stalk x)ˣ) (a : X.presheaf.stalk x), a ≠ 0 → (X.presheaf.germ (L2.U j₀) x hx).hom (h.f j₀) = u * a ^ 2 → ∃ V : X.Opens, x ∈ V ∧ ∃ a : Γ(X, V), a ≠ 0 ∧ ∀ j, ∃ u : Γ(X, V ⊓ L2.U j)ˣ, (X.presheaf.map (homOfLE inf_le_right).op).hom (h.f j) = (u : Γ(X, V ⊓ L2.U j)) * (X.presheaf.map (homOfLE inf_le_left).op).hom a ^ 2 := by
  first | exact @GlobalTheory.Mum.unit_mul_sq_spread | exact GlobalTheory.Mum.unit_mul_sq_spread | (intros; apply GlobalTheory.Mum.unit_mul_sq_spread <;> assumption)
