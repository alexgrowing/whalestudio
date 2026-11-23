import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchimedeanUnitarySurjective
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_unitary_surjective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (b : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ), (∀ τ, (b τ)ᴴ * C.gr τ * b τ = C.gr τ) → ∃ a : C.Arch, ∀ τ, C.tm a τ = b τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.tm_surj | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.tm_surj | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.tm_surj <;> assumption)
