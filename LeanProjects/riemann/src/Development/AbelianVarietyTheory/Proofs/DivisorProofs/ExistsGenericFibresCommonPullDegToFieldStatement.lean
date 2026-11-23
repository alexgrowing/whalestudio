import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibresCommonPullDegToField
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generic_fibres_common_pullDeg_to_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ D₂ : DegData R (maximalIdeal R)) (W : Type) [CommRing W] [IsDomain W] (φ : R →+* W), Function.Injective φ → ∀ D' : DegPre W, IsPullDeg φ D₁.toPre D' → IsPullDeg φ D₂.toPre D' → ∃ (E₁ E₂ : DegPre (FractionRing R)) (L : Type) (_ : Field L) (β : FractionRing R →+* L) (E' : DegPre L), Nonempty (IsPullDeg (algebraMap R (FractionRing R)) D₁.toPre E₁) ∧ Nonempty (IsPullDeg (algebraMap R (FractionRing R)) D₂.toPre E₂) ∧ Nonempty (IsPullDeg β E₁ E') ∧ Nonempty (IsPullDeg β E₂ E') := by
  first | exact @GlobalTheory.Mum.exists_generic_common_pull | exact GlobalTheory.Mum.exists_generic_common_pull | (intros; apply GlobalTheory.Mum.exists_generic_common_pull <;> assumption)
