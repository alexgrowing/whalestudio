import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsTranslatedRiemannLattice
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
theorem _root_.GlobalTheory.T.exists_translated_riemann_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (R : RiemLat E g Λ) (a ai : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ), R.form = F.form → (∀ τ, a τ * ai τ = 1) → (∀ τ, (a τ)ᴴ * C.gr τ * a τ = C.gr τ) → ∃ R' : RiemLat E g Λ, R'.form = R.form ∧ R'.B = R.B ∧ (∀ x, R'.P x = C.perExt R fun τ => ai τ *ᵥ C.vec x τ) ∧ ∀ A, C.IsAdapted R A → C.IsAdapted R' fun τ => a τ * A τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Rotate.rotate_exists | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Rotate.rotate_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Rotate.rotate_exists <;> assumption)
