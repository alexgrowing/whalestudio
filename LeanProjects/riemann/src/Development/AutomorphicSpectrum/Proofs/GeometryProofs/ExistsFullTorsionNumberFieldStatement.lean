import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFullTorsionNumberField
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_full_torsion_number_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (m : ℕ), 1 ≤ m → ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra L K) (x : Fin (m ^ (2 * D.g)) → (Over.mk (spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L))) ⟶ D.t.G)), (∀ i, x i ^ m = 1) ∧ ∀ (F : Type) [Field F] (f : K →+* F) (b : Sp F ⟶ Sp (𝓞 L)) (y : Over.mk b ⟶ D.t.G), b = spMap f ≫ spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L)) → y ^ m = 1 → ∃! i, y.left = spMap f ≫ (x i).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.TorsRat.torsion_rational | exact GlobalTheory.CompanionTheory.Ar.Sl.TorsRat.torsion_rational | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.TorsRat.torsion_rational <;> assumption)
