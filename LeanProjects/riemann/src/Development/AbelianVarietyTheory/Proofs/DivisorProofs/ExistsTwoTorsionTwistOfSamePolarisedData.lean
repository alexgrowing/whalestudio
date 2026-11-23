import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoRefinementsSamePolarisedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslateOfMumfordBundleMatchStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderTwoPointTorusExtensionTranslateStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp

theorem exists_twist_of_samePol : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)), SamePol D₀.toPre D.toPre → ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧ GlobalTheory.MumCmp.IsTwist D₀.toPre D.toPre g := by
  intro R _ _ _ hR D₀ D hS
  obtain ⟨β, xe, hβ, hc, wΛ, hwΛ, hτ⟩ := GlobalTheory.T.exists_iso_refinements_same_polarised R D₀.toPre D.toPre hS
  haveI : IsNoetherianRing R := hR.1.1
  obtain ⟨b, hb, w, hw⟩ := GlobalTheory.T.exists_translate_of_mumfordBundle_match R D₀.toPre D.toPre β hβ ⟨wΛ, hwΛ⟩
  obtain ⟨g, -, h2, ht⟩ := GlobalTheory.T.exists_order_two_point_torus_extension_translate R hR D₀ D β xe hβ hc wΛ hwΛ hτ b hb w hw
  exact ⟨g, h2, ht⟩

end GlobalTheory.MumCmp
