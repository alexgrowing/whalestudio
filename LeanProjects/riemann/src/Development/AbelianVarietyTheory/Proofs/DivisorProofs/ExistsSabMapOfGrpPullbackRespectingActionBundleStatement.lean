import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSabMapOfGrpPullbackRespectingActionBundle
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sabMap_of_grpPullback_respecting_action_bundle : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} (t' : SAB H S') (t : SAB H S) (f : S' ⟶ S) (π : t'.G.left ⟶ t.G.left), IsProper t.G.hom → IsGrpPullback t'.G t.G f π → (∀ a, (t'.act.act a).left ≫ π = π ≫ (t.act.act a).left) → LBIso t'.PP.L (t.PP.L.pull π) → ∃ m : SABMap t' t f, m.φ = π := by
  first | exact @GlobalTheory.UCanon.TriplePull.exists_sabMap_of_isProper | exact GlobalTheory.UCanon.TriplePull.exists_sabMap_of_isProper | (intros; apply GlobalTheory.UCanon.TriplePull.exists_sabMap_of_isProper <;> assumption)
