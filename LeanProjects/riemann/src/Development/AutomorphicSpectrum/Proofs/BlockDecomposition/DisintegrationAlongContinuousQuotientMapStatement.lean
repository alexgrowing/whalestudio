import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationAlongContinuousQuotientMap
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSplitK
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.disintegration_along_continuous_quotient_map : ∀ (V H Z : Type) [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace H] [T2Space H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H] (μ : Measure V) (ν : Measure H) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] (f : V → Z) (ι : H → Z) (q : V → H) (U : Set V) (m : H → Measure V), IsOpen U → Continuous q → Function.Injective ι → (∀ X, ι (q X) = f X) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ m → ∀ φ : V → ℂ, Continuous φ → Integrable φ μ → (∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ A : Set V, IsCompact A ∧ A ⊆ U ∧ ∀ Y, MeasurableSet Y → ∫⁻ X in Aᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ ε * ν Y) → ∀ c : H, Integrable φ (m c) ∧ ∀ r : ℕ → H → ℝ, (∀ k, Continuous (r k) ∧ HasCompactSupport (r k) ∧ (∀ y, 0 ≤ r k y) ∧ 0 < ∫ y, r k y ∂ν) → Filter.Tendsto (fun k => tsupport (r k)) Filter.atTop (nhds c).smallSets → Filter.Tendsto (fun k => (∫ X, φ X * (r k (q X) : ℂ) ∂μ) / ((∫ y, r k y ∂ν : ℝ) : ℂ)) Filter.atTop (nhds (∫ X, φ X ∂(m c))) := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.Lim.fibre_avg_tendsto | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.Lim.fibre_avg_tendsto | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.Lim.fibre_avg_tendsto <;> assumption)
