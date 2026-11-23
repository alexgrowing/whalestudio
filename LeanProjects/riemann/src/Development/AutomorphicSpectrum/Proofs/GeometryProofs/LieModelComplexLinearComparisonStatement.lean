import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexLinearComparison
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_complex_linear_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (t' : SAB H (Sp R)) (h : Sp R ⟶ X) (m : SABMap t' t h) (g : ℕ) (M : LieModel t'.G (𝟙 (Sp R)) (Fin g → R)) (ψ : R →+* ℂ) (Vz : Type) [AddCommGroup Vz] [Module ℂ Vz] (MR : LieModel t.G (spMap ψ ≫ h) Vz), ∃ Θ : (Fin g → ℂ) →ₗ[ℂ] Vz, ∀ x : Fin g → R, (MR.pt (Θ (fun e => ψ (x e)))).left = spMap (dualMap ψ) ≫ (M.pt x).left ≫ m.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FrameFibre.exists_linear_fibre | exact GlobalTheory.CompanionTheory.Ar.FrameFibre.exists_linear_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.FrameFibre.exists_linear_fibre <;> assumption)
