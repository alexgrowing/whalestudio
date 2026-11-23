import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullDegTraitAndBaseUniformisation
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_pullDeg_trait_and_base_uniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → IsSemiAbelian G → UnifTrait D G L →
    ∀ (D₂ : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U₂ : Unif (maximalIdeal R) D₂ A G),
    U₂.LG.L = L → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (φ : R →+* W) (D' : DegPre W),
      Function.Injective φ ∧ Nonempty (IsPullDeg φ D.toPre D') ∧ Nonempty (IsPullDeg φ D₂.toPre D') := by
  first | exact @GlobalTheory.Mum.CommonPull.exists_common_pull | exact GlobalTheory.Mum.CommonPull.exists_common_pull | (intros; apply GlobalTheory.Mum.CommonPull.exists_common_pull <;> assumption)
