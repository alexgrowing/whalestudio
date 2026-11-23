import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionMixedCoordsRankZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittDecomposition_mixedCoords_rank_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), (∀ (S S₀ T : HSp D) (d : HypDec S S₀ 0) (μ : Measure (Mx D T.rank 0)) (𝓕 : Set (Mx D T.rank 0)), IsCovolOne (ratMx D T.rank 0) μ 𝓕 → ∀ f x, d.mixS T ψ μ 𝓕 f x = fun w => f (d.ext0 T w)) ∧ (∀ (S T T₀ : HSp D) (d : HypDec T T₀ 0) (μ : Measure (Mx D 0 S.rank)) (𝓕 : Set (Mx D 0 S.rank)), IsCovolOne (ratMx D 0 S.rank) μ 𝓕 → ∀ f y, d.mixT S ψ μ 𝓕 f y = fun w => f (d.inc0 S w)) ∧ ∀ (S S₀ : HSp D) (d : HypDec S S₀ 0), (∀ a, d.levi a = 1) ∧ (∀ b, d.nB b = 1) ∧ ∀ c, d.nC c = 1 := by
  first | exact @GlobalTheory.Unf.mixRankZero | exact GlobalTheory.Unf.mixRankZero | (intros; apply GlobalTheory.Unf.mixRankZero <;> assumption)
