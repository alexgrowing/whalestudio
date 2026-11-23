import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesStep
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt

theorem levi_margin {n : ℕ} {f : (Fin n → ℂ) → ℝ} (hf : ContDiffOn ℝ 2 f (Metric.ball 0 1))
    (hp : ∀ t ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ v, v ≠ 0 → 0 < levi f t v) :
    ∃ δ > (0 : ℝ), ∀ t : Fin n → ℂ, ‖t‖ ≤ 1 / 2 → ∀ v, δ * ‖v‖ ^ 2 ≤ levi f t v := by
  have hc := ReciprocityTheory.AnForm.continuousOn_levi Metric.isOpen_ball hf
  set S : Set ((Fin n → ℂ) × (Fin n → ℂ)) := Metric.closedBall 0 (1 / 2) ×ˢ Metric.sphere 0 1 with hS
  have hSc : IsCompact S := (isCompact_closedBall _ _).prod (isCompact_sphere _ _)
  have hsub : S ⊆ Metric.ball 0 1 ×ˢ Set.univ := fun p hp' =>
    ⟨Metric.closedBall_subset_ball (by norm_num) hp'.1, trivial⟩
  obtain ⟨δ, hδ, hle⟩ := hSc.exists_forall_le' (hc.mono hsub) (a := 0) fun p hp' =>
    hp _ (hsub hp').1 _ fun h0 => by
      have := hp'.2
      rw [h0] at this
      simp at this
  refine ⟨δ, hδ, fun t ht v => ?_⟩
  by_cases hv : v = 0
  · rw [hv, ReciprocityTheory.AnForm.levi_zero]
    simp
  · have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
    have h1 := hle (t, ‖v‖⁻¹ • v) ⟨by simpa using ht, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']⟩
    simp only [ReciprocityTheory.AnForm.levi_smul_dir] at h1
    calc δ * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ ^ 2 * levi f t v) * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = levi f t v := by field_simp

theorem coneTangent_fderiv {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)} {e : ℕ}
    {τ : (Fin e → ℂ) → (Σ k, J k) → ℂ} {y : Fin e → ℂ} (hτ : DifferentiableAt ℂ τ y)
    (hm : ∀ᶠ y' in 𝓝 y, τ y' ∈ mcPts P) (w : Fin e → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P (τ y) (fderiv ℂ τ y w) := by
  intro f hf
  set F := MvPolynomial.map (Int.castRingHom ℂ) f
  have h0 : (fun y' => MvPolynomial.eval (τ y') F) =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hm] with y' hy'
    exact hy'.2 f hf
  have hD := (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval F (τ y)).comp y hτ.hasFDerivAt
  have hD0 : HasFDerivAt (fun y' => MvPolynomial.eval (τ y') F) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq h0
  have h1 := congrArg (fun L => L w) (hD.unique hD0)
  simpa [smul_eq_mul, mul_comm] using h1

end LevelTowerAlt

theorem LevelTowerAlt.levi_positive_reference_line : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W), ∃ δ > (0 : ℝ), ∀ a, ∀ t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ, ‖t‖ ≤ 1 / 2 → ∀ v, δ * ‖v‖ ^ 2 ≤ levi (fun t' => Real.log (D.A'.h ((D.chart a).γ t'))) t v := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D
  have key : ∀ a, ∃ δ > (0 : ℝ), ∀ t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ, ‖t‖ ≤ 1 / 2 → ∀ v,
      δ * ‖v‖ ^ 2 ≤ levi (fun t' => Real.log (D.A'.h ((D.chart a).γ t'))) t v := by
    intro a
    have hφ : ∀ t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1,
        ContDiffAt ℝ 2 (fun z => Real.log (D.A'.h z)) ((D.chart a).γ t) := fun t ht => by
      have hz := (D.chart a).mem t ht
      exact ((D.A'_pos.1.contDiffAt (StokesStep.isOpen_multicone.mem_nhds hz.1)).of_le
        (WithTop.coe_le_coe.mpr le_top)).log (D.A'.pos _ hz.1).ne'
    refine LevelTowerAlt.levi_margin (fun t ht => ?_) fun t ht v hv => ?_
    · exact ((hφ t ht).comp t
        (((D.chart a).analytic t ht).restrictScalars (𝕜 := ℝ)).contDiffAt).contDiffWithinAt
    · have hτ := (D.chart a).analytic t ht
      have h1 := ReciprocityTheory.AnForm.levi_comp v hτ (hφ t ht)
      change 0 < levi ((fun z => Real.log (D.A'.h z)) ∘ (D.chart a).γ) t v
      rw [h1]
      refine D.A'_pos.2 _ ((D.chart a).mem t ht) _ (LevelTowerAlt.coneTangent_fderiv hτ.differentiableAt ?_ v)
        fun c hc => hv ((D.chart a).immersion t ht v ⟨c, hc⟩)
      filter_upwards [Metric.isOpen_ball.mem_nhds ht] with y hy using (D.chart a).mem y hy
  choose δ hδ h using key
  obtain ⟨m, hm, hle⟩ : ∃ m > (0 : ℝ), ∀ a, m ≤ δ a := by
    rcases isEmpty_or_nonempty (Fin D.nCharts) with h0 | h0
    · exact ⟨1, one_pos, fun a => h0.elim a⟩
    · obtain ⟨a₀, h₀⟩ := Finite.exists_min δ
      exact ⟨δ a₀, hδ a₀, h₀⟩
  exact ⟨m, hm, fun a t ht v => (mul_le_mul_of_nonneg_right (hle a) (by positivity)).trans (h a t ht v)⟩
