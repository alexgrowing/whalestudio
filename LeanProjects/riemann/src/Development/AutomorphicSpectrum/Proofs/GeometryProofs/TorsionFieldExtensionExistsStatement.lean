import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionFieldExtensionExists
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_field_extension_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (th : Out.H0 D.t.PP.L 1) (m : ℕ) (K : Type) [Field K] [NumberField K] [Algebra L K] (x : Over.mk (spMap ((algebraMap L K).comp (algebraMap (𝓞 L) L))) ⟶ D.t.G), 1 ≤ m → x ^ m = 1 → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (_ : Algebra L K') (_ : IsScalarTower L K K'), ∀ (L' : Type) [Field L'] [NumberField L'] [Algebra K' L'] [Algebra L L'] [IsScalarTower L K' L'] (D' : PPData H L') (e : D.Ext D'), ∃ (s : Out.H0 D'.t.PP.L (m ^ 2)) (d : 𝓞 L'), d ≠ 0 ∧ ∀ (F : Type) [Field F] (f : L' →+* F) (y : Over.mk (spMap (f.comp (algebraMap (𝓞 L') L'))) ⟶ D'.t.G) (b : Sp F ⟶ Sp (𝓞 L)) (xF yF : Over.mk b ⟶ D.t.G) (N : ℕ) (T T' : F), xF.left = spMap ((f.comp (algebraMap K' L')).comp (algebraMap K K')) ≫ x.left → yF.left = y.left ≫ e.φ → TorsVal D'.t.PP s y N T → TorsVal D.t.PP th (xF * yF ^ m) (N * m) T' → ∃ r : ℕ, 1 ≤ r ∧ (T ^ (m ^ 2)) ^ r = (f (d : L') ^ ((N * m) ^ 2) * T') ^ r := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Transl.transl_main | exact GlobalTheory.CompanionTheory.Ar.Sl.Transl.transl_main | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Transl.transl_main <;> assumption)
