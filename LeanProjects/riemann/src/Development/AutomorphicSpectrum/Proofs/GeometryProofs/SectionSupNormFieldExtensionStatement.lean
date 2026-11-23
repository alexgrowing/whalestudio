import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionSupNormFieldExtension
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_sup_norm_field_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (L' : Type) [Field L'] [NumberField L'] [Algebra L L'] (D' : PPData H L') (_ : D.Ext D') (n : ℕ) (s : Out.H0 D.t.PP.L n), ∃ s' : Out.H0 D'.t.PP.L n, (∀ M : (L →+* ℂ) → ℝ, D.SupLe s M → D'.SupLe s' fun σ' => M (σ'.comp (algebraMap L L'))) ∧ ∀ (σ' : L' →+* ℂ) (a' : D'.Frame σ'), ∃ a : ArchFrame D.t.PP (emb (σ'.comp (algebraMap L L'))) D'.g, a.u.Λ = a'.u.Λ ∧ a.Hm = a'.Hm ∧ ∀ θ, a.IsFn s θ ↔ a'.IsFn s' θ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.ExtTrans.exists_section | exact GlobalTheory.CompanionTheory.Ar.Sl.ExtTrans.exists_section | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.ExtTrans.exists_section <;> assumption)
