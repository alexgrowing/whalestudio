import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CongruenceSubgroupOfFormAutomorphisms
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_subgroup_of_form_automorphisms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] [Module.Finite ℤ Λ] (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) (I : Ideal (𝓞 E)) (M A : ℕ), 0 < M → 0 < A → ∃ Γ : Subgroup (Λ ≃ₗ[𝓞 E] Λ), Γ ≤ autGrp form ∧ Γ.relIndex (autGrp form) ≠ 0 ∧ ∀ γ, γ ∈ Γ ↔ (∀ a b, form (γ a) (γ b) = form a b) ∧ (∀ a ∈ I • (⊤ : Submodule (𝓞 E) Λ), ∃ e, γ a = a + M • e) ∧ ∀ a, ∃ e, γ a = a + A • e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.levelGrp_finite_index | exact GlobalTheory.CompanionTheory.Ar.Cusp.levelGrp_finite_index | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.levelGrp_finite_index <;> assumption)
