import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameInverseProperties
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
theorem _root_.GlobalTheory.T.adapted_frame_inverse_properties : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (τ : Ψ) (A : Matrix (Fin (j + j')) (Sg j j') ℂ), Aᴴ * C.sgr τ * A = sgI j j' → C.cinv A τ * A = 1 ∧ A * C.cinv A τ = 1 ∧ ((C.cinv A τ)ᴴ * C.cinv A τ).PosDef ∧ ((C.cinv A τ)ᴴ * C.cinv A τ) * (C.gr τ)⁻¹ * ((C.cinv A τ)ᴴ * C.cinv A τ) = C.gr τ ∧ (∀ a ai : Matrix (Fin (j + j')) (Fin (j + j')) ℂ, a * ai = 1 → aᴴ * C.gr τ * a = C.gr τ → (a * A)ᴴ * C.sgr τ * (a * A) = sgI j j' ∧ C.cinv (a * A) τ = C.cinv A τ * ai ∧ IsSgU (C.cinv A τ * (a * A)) ∧ ((C.cinv A τ * (a * A))ᴴ * (C.cinv A τ * (a * A)) = 1 ↔ aᴴ * ((C.cinv A τ)ᴴ * C.cinv A τ) * a = (C.cinv A τ)ᴴ * C.cinv A τ)) ∧ ∀ A' : Matrix (Fin (j + j')) (Sg j j') ℂ, A'ᴴ * C.sgr τ * A' = sgI j j' → (A' * C.cinv A τ)ᴴ * C.gr τ * (A' * C.cinv A τ) = C.gr τ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.cinv_facts | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.cinv_facts | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.cinv_facts <;> assumption)
