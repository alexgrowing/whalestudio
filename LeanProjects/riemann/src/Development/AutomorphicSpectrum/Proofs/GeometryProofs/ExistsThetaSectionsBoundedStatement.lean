import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsThetaSectionsBounded
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_sections_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (th : Out.H0 D.t.PP.L 1) (Φ : ℝ) (M : (L →+* ℂ) → ℝ) (m : ℕ), 1 ≤ m → D.HasTheta th Φ → D.SupLe th M → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (D' : PPData H L') (_ : D.Ext D') (s : Fin (m ^ (2 * D.g)) → Out.H0 D'.t.PP.L (m ^ 2)), (∀ i, D'.SupLe (s i) fun σ' => M (σ'.comp (algebraMap L L'))) ∧ ∀ (σ' : L' →+* ℂ) (a : D'.Frame σ') (f : Fin (m ^ (2 * D.g)) → (Fin D'.g → ℂ) → ℂ), (∀ i, a.IsFn (s i) (f i)) → ∀ F, a.IsTheta (m ^ 2) F → ∃ c : Fin (m ^ (2 * D.g)) → ℂ, F = ∑ i, c i • f i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Basis.main | exact GlobalTheory.CompanionTheory.Ar.Sl.Basis.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Basis.main <;> assumption)
