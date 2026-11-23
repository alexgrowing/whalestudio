import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusExtensionTangentExact
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_extension_tangent_exact : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] (τ : TorusExtension G), letI := τ.addCommGroup; letI := τ.grpB; ∀ (A : Type) [Field A] (c : K →+* A), (∀ v : epsAt (spMap c) ⟶ G, IsTanAt G _ v → (v ≫ τ.q = 1 ↔ ∃ w : epsAt (spMap c) ⟶ splitTorus (Sp K) τ.X, IsTanAt _ _ w ∧ w ≫ τ.i = v)) ∧ ∀ w : epsAt (spMap c) ⟶ τ.B, IsTanAt τ.B _ w → ∃ v : epsAt (spMap c) ⟶ G, IsTanAt G _ v ∧ v ≫ τ.q = w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieExact.lie_exact_field | exact GlobalTheory.CompanionTheory.Ar.LieExact.lie_exact_field | (intros; apply GlobalTheory.CompanionTheory.Ar.LieExact.lie_exact_field <;> assumption)
