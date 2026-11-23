import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetIdealSelfDualLatticeAndInterStandard
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detIdeal_selfDual_lattice_and_inter_standard : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Λ : GenLat E n), Λ.Unimod → ∃ J : Ideal (𝓞 E), J ≠ ⊥ ∧ Ideal.absNorm J = (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ∧ Submodule.span (𝓞 E) (detSet Λ.Ln) = J • Submodule.span (𝓞 E) (detSet Λ.La) ∧ Submodule.span (𝓞 E) (detSet Λ.Ln) = Submodule.map (Algebra.linearMap (𝓞 E) E) (conjI J) ∧ ∀ h : Matrix (Fin n) (Fin n) E, Submodule.span (𝓞 E) (detSet (actLat h Λ).La) = Submodule.map (LinearMap.mulLeft (𝓞 E) h.det) (Submodule.span (𝓞 E) (detSet Λ.La)) := by
  first | exact @GlobalTheory.DetIdeal.detIdeal_selfDual | exact GlobalTheory.DetIdeal.detIdeal_selfDual | (intros; apply GlobalTheory.DetIdeal.detIdeal_selfDual <;> assumption)
