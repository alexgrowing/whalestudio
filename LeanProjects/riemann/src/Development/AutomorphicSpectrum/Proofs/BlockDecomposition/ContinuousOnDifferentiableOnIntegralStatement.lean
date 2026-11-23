import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnDifferentiableOnIntegral
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_differentiableOn_parameter_integral : ∀ {Y T : Type} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [TopologicalSpace T]
    [FirstCountableTopology T] (μ : Measure Y) (U : Set ℂ), IsOpen U → ∀ F : ℂ → T → Y → ℂ,
  ContinuousOn (fun u : ℂ × T × Y => F u.1 u.2.1 u.2.2) (U ×ˢ Set.univ) →
  (∀ t y, DifferentiableOn ℂ (fun z => F z t y) U) →
  (∀ z₀ ∈ U, ∀ t₀ : T, ∃ V ∈ 𝓝 z₀, ∃ N ∈ 𝓝 t₀, ∃ w : Y → ℝ, Integrable w μ ∧ ∀ z ∈ V, ∀ t ∈ N, ∀ y, ‖F z t y‖ ≤ w y) →
  ContinuousOn (fun u : ℂ × T => ∫ y, F u.1 u.2 y ∂μ) (U ×ˢ Set.univ) ∧
    ∀ t, DifferentiableOn ℂ (fun z => ∫ y, F z t y ∂μ) U := by
  first | exact @GlobalTheory.CompanionTheory.Param.continuousOn_differentiableOn_integral | exact GlobalTheory.CompanionTheory.Param.continuousOn_differentiableOn_integral | (intros; apply GlobalTheory.CompanionTheory.Param.continuousOn_differentiableOn_integral <;> assumption)
