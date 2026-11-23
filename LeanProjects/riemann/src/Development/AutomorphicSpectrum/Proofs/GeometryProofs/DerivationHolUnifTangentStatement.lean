import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerivationHolUnifTangent
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecMapCompAppLE
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.InvDer
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivation_hol_unif_tangent : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (A : Over (Sp ℂ)) [GrpObj A] (z : Sp ℂ ⟶ Sp R) (φ : A.left ⟶ G.left) (_ : IsGrpPullback A G z φ) (g : ℕ) (Lb : LB A.left) (u : HolUnif A Lb g) (v₀ : epsAt (𝟙 (Sp R)) ⟶ G) (hv₀ : IsTanAt G (𝟙 (Sp R)) v₀) (c : Fin g → ℂ) (v' : epsR ℂ ⟶ A), v'.left ≫ φ = spMap (dualMap (bmap z)) ≫ v₀.left → u.IsDiff c v' → ∀ (V : G.left.Opens) (hV : IsAffineOpen V) (f : Γ(G.left, V)) (w : Fin g → ℂ), ⊤ ≤ ((u.ex w).left ≫ φ) ⁻¹ᵁ V → fderiv ℂ (fun x => valAt' ((u.ex x).left ≫ φ) V f) w c = valAt' ((u.ex w).left ≫ φ) V (der v₀ hv₀ hV f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.InvDer.fderiv_valAt_eq_der | exact GlobalTheory.CompanionTheory.Ar.InvDer.fderiv_valAt_eq_der | (intros; apply GlobalTheory.CompanionTheory.Ar.InvDer.fderiv_valAt_eq_der <;> assumption)
