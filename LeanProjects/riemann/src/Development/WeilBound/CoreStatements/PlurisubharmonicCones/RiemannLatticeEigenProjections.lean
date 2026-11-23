import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.EmbEquivSymmApply

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace LevelTowerAlt

theorem riemann_lattice_eigen_projections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ), Function.Injective R.P ∧ Submodule.span ℝ (Set.range R.P) = ⊤ ∧ (∀ s : 𝓞 E →+* ℂ, (∀ x, eigComp R.B s x ∈ eigSp R.B s) ∧ (∀ x ∈ eigSp R.B s, eigComp R.B s x = x) ∧ (∀ (c : ℂ) x y, eigComp R.B s (c • x + y) = c • eigComp R.B s x + eigComp R.B s y) ∧ ∀ a x, eigComp R.B s (R.B a x) = s a • eigComp R.B s x) ∧ (∀ x, ∑ s : E →+* ℂ, eigComp R.B (s.comp (algebraMap (𝓞 E) E)) x = x) ∧ ∀ s s' : 𝓞 E →+* ℂ, s ≠ s' → ∀ x ∈ eigSp R.B s, ∀ y ∈ eigSp R.B s', R.ip x y = 0 := by
  intro E _ _ _ g Λ _ _ Ψ _ R
  refine ⟨LevelTowerAlt.precomp_injective R, LevelTowerAlt.span_top R,
    fun s => ⟨fun x => ?_, fun x hx => ?_, fun c x y => ?_, fun a x => ?_⟩, fun x => ?_,
    fun s s' hss' x hx y hy => LevelTowerAlt.ip_orth R hss' hx hy⟩
  · rw [LevelTowerAlt.eigComp_eq]
    exact LevelTowerAlt.proj_mem _ _ _
  · rw [LevelTowerAlt.eigComp_eq]
    exact LevelTowerAlt.proj_eig_self hx
  · simp only [LevelTowerAlt.eigComp_eq, map_add, map_smul]
  · simp only [LevelTowerAlt.eigComp_eq]
    exact LevelTowerAlt.proj_act _ _ _ _
  · simp only [LevelTowerAlt.eigComp_eq]
    conv_rhs => rw [← LevelTowerAlt.sum_proj R.B x]
    exact Fintype.sum_equiv (LevelTowerAlt.embEquiv E) _ _ (fun _ => rfl)

end LevelTowerAlt
