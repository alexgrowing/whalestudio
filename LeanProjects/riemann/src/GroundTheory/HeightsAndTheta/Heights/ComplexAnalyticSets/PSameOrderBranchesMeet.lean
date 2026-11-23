import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSameOrderBranchesMeet
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchInCurveComponent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSameOrdersLiftCentre
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchLift
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable def VarBranch.restrictInto {n k : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (c : VarBranch I k q) (ε : ℝ) (hε : 0 < ε)
    (h : ∀ t ∈ Metric.ball (0 : Fin k → ℂ) ε, c.toFun t ∈ zeroSet J) : VarBranch J k q where
  radius := min ε c.radius
  radius_pos := lt_min hε c.radius_pos
  toFun := c.toFun
  differentiableOn := c.differentiableOn.mono (Metric.ball_subset_ball (min_le_right _ _))
  injOn := c.injOn.mono (Metric.ball_subset_ball (min_le_right _ _))
  map_zero := c.map_zero
  mapsTo := fun t ht ↦ h t (Metric.ball_subset_ball (min_le_left _ _) ht)

theorem VarBranch.eventually_mem_zeroSet {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (c : VarBranch I 1 q) (h : ∀ f ∈ J, branchOrder c f = ⊤) :
    ∀ᶠ t in 𝓝 (0 : Fin 1 → ℂ), c.toFun t ∈ zeroSet J := by
  have key : ∀ f ∈ J, ∀ᶠ t in 𝓝 (0 : Fin 1 → ℂ), eval (c.toFun t) f = 0 := by
    intro f hf
    have h0 := analyticOrderAt_eq_top.1 (h f hf)
    have ht : Tendsto (fun t : Fin 1 → ℂ ↦ t 0) (𝓝 0) (𝓝 0) := (continuous_apply 0).tendsto' _ _ rfl
    filter_upwards [ht.eventually h0] with t ht
    have : (fun _ : Fin 1 ↦ t 0) = t := funext fun i ↦ by rw [Subsingleton.elim i 0]
    rwa [this] at ht
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian J : J.FG)
  filter_upwards [(s.eventually_all).2 fun g hg ↦ key g (hs ▸ Submodule.subset_span hg)] with t ht f hf
  have hle : Ideal.span (s : Set (MvPolynomial (Fin n) ℂ)) ≤ RingHom.ker (eval (c.toFun t)) :=
    Ideal.span_le.2 fun g hg ↦ ht g hg
  have hf' : f ∈ Ideal.span (s : Set (MvPolynomial (Fin n) ℂ)) := by
    rw [Ideal.span, hs]
    exact hf
  exact hle hf'

theorem SameOrderBranchesMeet.proof (hC : BranchInCurveComponent.Statement) (hO : SameOrdersLiftCentre.Statement)
    (hL : IndefiniteRowSideFullHecke.ComplexSets.BranchLift.Statement) : SameOrderBranchesMeet.Statement := by
  intro n I q c c' _ hdim hord
  obtain ⟨J, hJmin, hJdim, hev⟩ := hC n I q c hdim
  have hJ : J.IsPrime := hJmin.1.1
  have htop : ∀ f ∈ J, branchOrder c f = ⊤ := fun f hf ↦ by
    refine analyticOrderAt_eq_top.2 ?_
    have hι : Tendsto (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) (𝓝 0) (𝓝 0) :=
      (continuous_pi fun _ ↦ continuous_id).tendsto' _ _ rfl
    filter_upwards [hι.eventually hev] with τ hτ using hτ f hf
  have hev' := c'.eventually_mem_zeroSet J fun f hf ↦ (hord f).symm.trans (htop f hf)
  obtain ⟨ε, hε, hεJ⟩ := Metric.eventually_nhds_iff_ball.1 hev
  obtain ⟨ε', hε', hεJ'⟩ := Metric.eventually_nhds_iff_ball.1 hev'
  let γ := c.restrictInto J ε hε hεJ
  let γ' := c'.restrictInto J ε' hε' hεJ'
  obtain ⟨M⟩ := IndefiniteRowSideFullHecke.ComplexSets.NormalModelExists.proof n J hJ
  obtain ⟨Γ, hΓd, hΓ, -⟩ := hL n 1 J q M γ hJ hJdim
  obtain ⟨Γ', hΓ'd, hΓ', hΓ'o⟩ := hL n 1 J q M γ' hJ hJdim
  have hw : Γ 0 = Γ' 0 := hO n J q M γ γ' Γ Γ' hJ hJdim hΓd hΓ hΓ'd hΓ' hord
  obtain ⟨U, hUo, hU⟩ := hΓ'o _ subset_rfl Metric.isOpen_ball
  have h0 : (0 : Fin 1 → ℂ) ∈ Metric.ball 0 γ.radius := Metric.mem_ball_self γ.radius_pos
  have hΓ0U : Γ 0 ∈ U := by
    rw [hw]
    exact (hU ▸ Set.mem_image_of_mem Γ' (Metric.mem_ball_self γ'.radius_pos)).2
  have hcont : ContinuousAt Γ 0 := hΓd.continuousOn.continuousAt (Metric.ball_mem_nhds 0 γ.radius_pos)
  have hnear : ∀ᶠ τ in 𝓝[≠] (0 : Fin 1 → ℂ), τ ≠ 0 ∧ τ ∈ Metric.ball 0 γ.radius ∧ Γ τ ∈ U := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 γ.radius_pos),
      nhdsWithin_le_nhds (hcont.preimage_mem_nhds (hUo.mem_nhds hΓ0U))] with τ h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨τ, hτ0, hτ, hτU⟩ := hnear.exists
  obtain ⟨τ', hτ', hτ'eq⟩ : Γ τ ∈ Γ' '' Metric.ball 0 γ'.radius := hU ▸ ⟨(hΓ τ hτ).1, hτU⟩
  have hτc : τ ∈ Metric.ball 0 c.radius := Metric.ball_subset_ball (min_le_right _ _) hτ
  refine ⟨c.toFun τ, ⟨⟨τ, hτc, rfl⟩, ⟨τ', Metric.ball_subset_ball (min_le_right _ _) hτ', ?_⟩⟩, fun hq ↦ hτ0 ?_⟩
  · have e1 := (hΓ' τ' hτ').2
    have e2 := (hΓ τ hτ).2
    rw [hτ'eq] at e1
    exact e1.symm.trans e2
  · exact c.injOn hτc (Metric.mem_ball_self c.radius_pos) (hq.trans c.map_zero.symm)

end GroundTheory.Heights₂.Heights
