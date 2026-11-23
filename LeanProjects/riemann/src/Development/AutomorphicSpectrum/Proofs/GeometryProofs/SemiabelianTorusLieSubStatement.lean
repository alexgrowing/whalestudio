import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianTorusLieSub
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_torus_lie_sub : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (G : Over (Sp O)) [GrpObj G] (GK : Over (Sp K)) [GrpObj GK] (φ : GK.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback GK G (spMap (algebraMap O K)) φ → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp K) X ⟶ GK) [IsMonHom i] [Mono i] (MT : LieModel (splitTorus (Sp K) X) (𝟙 _) (X →+ K)), IsCocharLie MT → ∀ (E : Type) [AddCommGroup E] [Module O E] (M : LieModel G (𝟙 _) E), ∃ io : (X →+ O) →ₗ[O] E, (∀ δ, M.Lifts (algebraMap O K) φ (io δ) (MT.pt ((algebraMap O K).toAddMonoidHom.comp δ) ≫ i)) ∧ Function.Injective io ∧ ∀ (a : O) (y : E), a ≠ 0 → a • y ∈ LinearMap.range io → y ∈ LinearMap.range io := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TsOk.saturated | exact GlobalTheory.CompanionTheory.Ar.TsOk.saturated | (intros; apply GlobalTheory.CompanionTheory.Ar.TsOk.saturated <;> assumption)
