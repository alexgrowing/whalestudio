import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianHomLieExtends
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_hom_lie_extends : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (G G' : Over (Sp O)) [GrpObj G] [GrpObj G'] (GK GK' : Over (Sp K)) [GrpObj GK] [GrpObj GK'] (φ : GK.left ⟶ G.left) (φ' : GK'.left ⟶ G'.left), IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap O K)) φ → IsGrpPullback GK' G' (spMap (algebraMap O K)) φ' → ∀ (q : GK ⟶ GK') [IsMonHom q] (E : Type) [AddCommGroup E] [Module O E] (E' : Type) [AddCommGroup E'] [Module O E'] (M : LieModel G (𝟙 _) E) (M' : LieModel G' (𝟙 _) E'), ∃ f : E →ₗ[O] E', ∀ (e : E) (v : epsAt (𝟙 (Sp K)) ⟶ GK), M.Lifts (algebraMap O K) φ e v → M'.Lifts (algebraMap O K) φ' (f e) (v ≫ q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieHomOk.hom_maps_lie | exact GlobalTheory.CompanionTheory.Ar.LieHomOk.hom_maps_lie | (intros; apply GlobalTheory.CompanionTheory.Ar.LieHomOk.hom_maps_lie <;> assumption)
