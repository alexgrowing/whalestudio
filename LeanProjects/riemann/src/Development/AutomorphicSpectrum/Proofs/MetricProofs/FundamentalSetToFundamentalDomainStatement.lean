import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FundamentalSetToFundamentalDomain
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_set_to_fundamental_domain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (Δ : GroupDict F) (μ : Measure (archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))))) [μ.IsHaarMeasure] (Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ)) (FF : Set (Fin n → ℂ)) (FD : Set (archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))))), F.IsArith Γ → F.IsFundSet Γ FF → IsFundamentalDomain (archLatticeGroup Δ.h (Pi.basisFun E (Fin (j + j'))) Δ.e.range) FD μ → ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ Φ : (Fin n → ℂ) → ℝ≥0∞, Measurable Φ → (∀ t ∈ ballDom F.q, ∀ t' ∈ ballDom F.q, F.Eqv (autGrp F.form) t t' → Φ t = Φ t') → ∫⁻ t in FF, Φ t * ENNReal.ofReal (ballDens F.q t) = C * ∫⁻ a in FD, Φ (Δ.π a) ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.lintegral_fundSet_eq_const_mul | exact GlobalTheory.CompanionTheory.Ar.Cusp.lintegral_fundSet_eq_const_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.lintegral_fundSet_eq_const_mul <;> assumption)
