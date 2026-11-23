import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSpaceEquivHolUnif
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_space_equiv_hol_unif : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (z : Spec (CommRingCat.of ℂ) ⟶ X) (V : Type) [AddCommGroup V] [Module ℂ V] (M : LieModel G z V) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ G.left) (L : LB A.left) (g : ℕ) (u : HolUnif A L g), IsGrpPullback A G z φ → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → ∃ D : V ≃ₗ[ℂ] (Fin g → ℂ), ∀ v, ∃ x : epsR ℂ ⟶ A, IsTangent x ∧ x.left ≫ φ = (M.pt v).left ∧ u.IsDiff (D v) x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeLin.exists_linearEquiv | exact GlobalTheory.CompanionTheory.Ar.HodgeLin.exists_linearEquiv | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeLin.exists_linearEquiv <;> assumption)
