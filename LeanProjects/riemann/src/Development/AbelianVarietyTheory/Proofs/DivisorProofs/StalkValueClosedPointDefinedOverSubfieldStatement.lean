import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkValueClosedPointDefinedOverSubfield
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SepAtBIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stalkValue_closedPoint_definedOver_subfield : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] [IsLocalRing R] (ξ₁ : Sp R ⟶ X) (K : Type) [Field K] (ev₁ : R →+* K) (k₀ : Subfield K), (∀ p, (spMap ev₁ ≫ ξ₁) p = ξ₁ (closedPoint R)) → GlobalTheory.UChart.DefOver k₀ (spMap ev₁ ≫ ξ₁) → ∀ h ∈ (Scheme.stalkClosedPointTo ξ₁).hom.range, ev₁ h ∈ k₀ ∧ (h ∈ maximalIdeal R → ev₁ h = 0) := by
  first | exact @GlobalTheory.USep.stalkVal_closedPoint | exact GlobalTheory.USep.stalkVal_closedPoint | (intros; apply GlobalTheory.USep.stalkVal_closedPoint <;> assumption)
