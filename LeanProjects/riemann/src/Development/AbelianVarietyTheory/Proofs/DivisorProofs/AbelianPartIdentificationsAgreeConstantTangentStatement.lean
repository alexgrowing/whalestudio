import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartIdentificationsAgreeConstantTangent
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPart_identifications_agree_constant_tangent : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* R) (B₀ : Over (Sp W₀)) [GrpObj B₀] (β : Q.P.A.left ⟶ B₀.left), IsGrpPullback Q.P.A B₀ (spMap ιb) β → ∀ (k : Type) [Field k] (ρ : R →+* DualNumber k), ρ.comp ιb = GlobalTheory.RigChart.constHom (ρ.comp ιb) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ Q.P.A.left), IsGrpPullback B' Q.P.A (spMap ρ) π₁ → IsGrpPullback B' Q.P.A (spMap (GlobalTheory.RigChart.constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → π₁ ≫ β = π₂ ≫ β := by
  first | exact @GlobalTheory.RigHom.comp_eq_of_const | exact GlobalTheory.RigHom.comp_eq_of_const | (intros; apply GlobalTheory.RigHom.comp_eq_of_const <;> assumption)
