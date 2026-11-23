import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolarizedDataFieldExtension
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarized_data_field_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (L' : Type) [Field L'] [NumberField L'] [Algebra L L'], Nonempty (Σ D' : PPData H L', D.Ext D') ∧ ∀ (D' : PPData H L') (_ : D.Ext D'), D'.g = D.g ∧ D'.hp = D.hp ∧ ∃ io : D.B.carrier →ₛₗ[algebraMap (𝓞 L) (𝓞 L')] D'.B.carrier, Function.Injective io ∧ Submodule.span (𝓞 L') (Set.range io) = ⊤ ∧ ∀ (σ' : L' →+* ℂ) (x y : D.B.carrier), ((D'.B.metric.form σ').inner ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] io x) ((1 : ComplexAt σ') ⊗ₜ[𝓞 L'] io y) : ℂ) = ((D.B.metric.form (σ'.comp (algebraMap L L'))).inner ((1 : ComplexAt _) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt _) ⊗ₜ[𝓞 L] y) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.ext_baseChange | exact GlobalTheory.CompanionTheory.Ar.Sl.ext_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.ext_baseChange <;> assumption)
