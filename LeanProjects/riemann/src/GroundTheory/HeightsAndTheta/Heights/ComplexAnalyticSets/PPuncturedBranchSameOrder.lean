import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPuncturedBranchSameOrder
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPuncturedCurveDiscInverse
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

namespace PuncturedBranchSameOrder

theorem const_mem_ball_iff (τ : ℂ) (r : ℝ) :
    (fun _ : Fin 1 ↦ τ) ∈ Metric.ball (0 : Fin 1 → ℂ) r ↔ τ ∈ Metric.ball (0 : ℂ) r := by
  simp only [Metric.mem_ball, dist_zero_right, pi_norm_const]

theorem disc_props {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ} (b : VarBranch I 1 q) :
    DifferentiableOn ℂ (fun τ : ℂ ↦ b.toFun fun _ ↦ τ) (Metric.ball 0 b.radius) ∧
    Set.InjOn (fun τ : ℂ ↦ b.toFun fun _ ↦ τ) (Metric.ball 0 b.radius) ∧
    Set.MapsTo (fun τ : ℂ ↦ b.toFun fun _ ↦ τ) (Metric.ball 0 b.radius) (zeroSet I) ∧
    (b.toFun fun _ ↦ (0 : ℂ)) = q ∧
    ∀ x, x ∈ b.image ↔ ∃ σ ∈ Metric.ball (0 : ℂ) b.radius, (b.toFun fun _ ↦ σ) = x := by
  have hι : Differentiable ℂ (fun τ : ℂ ↦ fun _ : Fin 1 ↦ τ) := differentiable_pi.2 fun _ ↦ differentiable_id
  refine ⟨b.differentiableOn.comp hι.differentiableOn fun τ hτ ↦ (const_mem_ball_iff τ _).2 hτ,
    fun s hs t ht h ↦ congrFun (b.injOn ((const_mem_ball_iff s _).2 hs) ((const_mem_ball_iff t _).2 ht) h) 0,
    fun τ hτ ↦ b.mapsTo ((const_mem_ball_iff τ _).2 hτ), b.map_zero, fun x ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨t, ht, rfl⟩
    have ht' : (fun _ : Fin 1 ↦ t 0) = t := funext fun i ↦ by rw [Subsingleton.elim i 0]
    refine ⟨t 0, (const_mem_ball_iff _ _).1 ?_, by rw [ht']⟩
    rw [ht']
    exact ht
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨_, (const_mem_ball_iff σ _).2 hσ, rfl⟩

theorem factor_of_punctured {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {C D : ℂ → E} {ψ : ℂ → ℂ}
    {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hCd : DifferentiableOn ℂ C (Metric.ball 0 r)) (hCi : Set.InjOn C (Metric.ball 0 r))
    (hDd : DifferentiableOn ℂ D (Metric.ball 0 ρ)) (hDi : Set.InjOn D (Metric.ball 0 ρ)) (h0 : C 0 = D 0)
    (hψd : DifferentiableOn ℂ ψ (Metric.ball 0 ρ \ {0}))
    (hψ : ∀ τ ∈ Metric.ball (0 : ℂ) ρ \ {0}, ψ τ ∈ Metric.ball (0 : ℂ) r ∧ C (ψ τ) = D τ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ (∀ᶠ τ in 𝓝 0, D τ = C (g τ)) ∧ 𝓝 0 ≤ map g (𝓝 0) := by
  obtain ⟨g, hg_def⟩ : ∃ g : ℂ → ℂ, g = Function.update ψ 0 (limUnder (𝓝[≠] (0 : ℂ)) ψ) := ⟨_, rfl⟩
  have hB : Metric.ball (0 : ℂ) ρ ∈ 𝓝 0 := Metric.ball_mem_nhds 0 hρ
  have hgd : DifferentiableOn ℂ g (Metric.ball 0 ρ) := by
    rw [hg_def]
    refine Complex.differentiableOn_update_limUnder_of_bddAbove hB hψd ⟨r, ?_⟩
    rintro _ ⟨τ, hτ, rfl⟩
    exact (mem_ball_zero_iff.1 (hψ τ hτ).1).le
  have hgψ : ∀ τ, τ ≠ 0 → g τ = ψ τ := fun τ hτ ↦ by rw [hg_def]; exact Function.update_of_ne hτ _ _
  have hgc : ContinuousAt g 0 := (hgd.differentiableAt hB).continuousAt
  have hpunct : ∀ᶠ τ in 𝓝[≠] (0 : ℂ), τ ∈ Metric.ball (0 : ℂ) ρ \ {0} :=
    Filter.mem_of_superset (inter_mem_nhdsWithin _ hB) fun τ h ↦ ⟨h.2, h.1⟩
  have hpt : ∀ s : ℝ, 0 < s → s < ρ → (s : ℂ) ∈ Metric.ball (0 : ℂ) ρ \ {0} := fun s hs hsρ ↦
    ⟨by rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hs.le]; exact hsρ, by simpa using hs.ne'⟩
  have hle : ‖g 0‖ ≤ r := by
    refine le_of_tendsto (hgc.norm.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0)) ?_
    filter_upwards [hpunct] with τ hτ
    rw [hgψ τ hτ.2]
    exact (mem_ball_zero_iff.1 (hψ τ hτ).1).le
  have hlt : ‖g 0‖ < r := by
    refine lt_of_le_of_ne hle fun heq ↦ ?_
    have hmax : IsMaxOn (norm ∘ g) (Metric.ball 0 ρ) 0 := isMaxOn_iff.2 fun τ hτ ↦ by
      show ‖g τ‖ ≤ ‖g 0‖
      by_cases h : τ = 0
      · rw [h]
      · rw [hgψ τ h, heq]
        exact (mem_ball_zero_iff.1 (hψ τ ⟨hτ, h⟩).1).le
    have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball (0 : ℂ) ρ).isPreconnected
      Metric.isOpen_ball hgd (Metric.mem_ball_self hρ) hmax
    have h1 := hpt (ρ / 2) (by positivity) (by linarith)
    have h2 := hpt (ρ / 4) (by positivity) (by linarith)
    have e1 : D ((ρ / 2 : ℝ) : ℂ) = C (g 0) := by
      rw [← (hψ _ h1).2, ← hgψ _ h1.2]
      exact congrArg C (hconst h1.1)
    have e2 : D ((ρ / 4 : ℝ) : ℂ) = C (g 0) := by
      rw [← (hψ _ h2).2, ← hgψ _ h2.2]
      exact congrArg C (hconst h2.1)
    have := Complex.ofReal_injective (hDi h1.1 h2.1 (e1.trans e2.symm))
    linarith
  have hgr : g 0 ∈ Metric.ball (0 : ℂ) r := mem_ball_zero_iff.2 hlt
  have hCg0 : C (g 0) = D 0 := by
    have hC : ContinuousAt C (g 0) := (hCd.differentiableAt (Metric.isOpen_ball.mem_nhds hgr)).continuousAt
    have hD : ContinuousAt D 0 := (hDd.differentiableAt hB).continuousAt
    refine tendsto_nhds_unique_of_eventuallyEq ((hC.comp hgc).tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0))
      (hD.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 0)) ?_
    filter_upwards [hpunct] with τ hτ
    rw [Function.comp_apply, hgψ τ hτ.2]
    exact (hψ τ hτ).2
  have hg0 : g 0 = 0 := hCi hgr (Metric.mem_ball_self hr) (hCg0.trans h0.symm)
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), D τ = C (g τ) := by
    filter_upwards [hB] with τ hτ
    by_cases h : τ = 0
    · rw [h, hCg0]
    · rw [hgψ τ h]
      exact (hψ τ ⟨hτ, h⟩).2.symm
  have hga : AnalyticAt ℂ g 0 := hgd.analyticAt hB
  refine ⟨g, hga, hg0, hev, ?_⟩
  rcases hga.eventually_constant_or_nhds_le_map_nhds with hc | hc
  · exfalso
    obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 (hc.and hev)
    have hm : 0 < min ε ρ := lt_min hε hρ
    have hs : 0 < min ε ρ / 2 := half_pos hm
    have hsε : min ε ρ / 2 < ε := by have := min_le_left ε ρ; linarith
    have hsρ : min ε ρ / 2 < ρ := by have := min_le_right ε ρ; linarith
    have h1 := hpt _ hs hsρ
    obtain ⟨hgc1, hD1⟩ := hεb (by rw [dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hs.le]; exact hsε)
    exact h1.2 (hDi h1.1 (Metric.mem_ball_self hρ) (by rw [hD1, hgc1, hg0, h0]))
  · rwa [hg0] at hc

theorem punctured_factor (hcut : PuncturedCurveDiscInverse.Statement) {n : ℕ} {I : Ideal (MvPolynomial (Fin n) ℂ)}
    {q : Fin n → ℂ} (hI : IsRadicalAt I q) (hdim : ringKrullDim (curveLocalRing I q) = 1) (c d : VarBranch I 1 q)
    (ρ : ℝ) (hρ : 0 < ρ) (hcd : ∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < ρ → d.toFun (fun _ ↦ τ) ∈ c.image) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ g 0 = 0 ∧ (∀ᶠ τ in 𝓝 0, (d.toFun fun _ ↦ τ) = c.toFun fun _ ↦ g τ) ∧
      𝓝 0 ≤ map g (𝓝 0) := by
  obtain ⟨hCd, hCi, hCm, hC0, hCim⟩ := disc_props c
  obtain ⟨hDd, hDi, hDm, hD0, -⟩ := disc_props d
  obtain ⟨ε, hε, hcutε⟩ := hcut n I q hI hdim
  have hDc : ContinuousAt (fun τ : ℂ ↦ d.toFun fun _ ↦ τ) 0 :=
    (hDd.differentiableAt (Metric.ball_mem_nhds 0 d.radius_pos)).continuousAt
  obtain ⟨ρ₁, hρ₁, hρ₁ε⟩ := Metric.continuousAt_iff.1 hDc ε hε
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : ℝ, ρ' = min (min ρ ρ₁) d.radius := ⟨_, rfl⟩
  have hρ'pos : 0 < ρ' := hρ' ▸ lt_min (lt_min hρ hρ₁) d.radius_pos
  have hρ'ρ : ρ' ≤ ρ := hρ' ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hρ'1 : ρ' ≤ ρ₁ := hρ' ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hsub : Metric.ball (0 : ℂ) ρ' ⊆ Metric.ball 0 d.radius := Metric.ball_subset_ball (hρ' ▸ min_le_right _ _)
  let ψ : ℂ → ℂ := fun τ ↦
    Function.invFunOn (fun σ : ℂ ↦ c.toFun fun _ ↦ σ) (Metric.ball 0 c.radius) (d.toFun fun _ ↦ τ)
  have hψ : ∀ τ ∈ Metric.ball (0 : ℂ) ρ' \ {0},
      ψ τ ∈ Metric.ball (0 : ℂ) c.radius ∧ (c.toFun fun _ ↦ ψ τ) = d.toFun fun _ ↦ τ := by
    intro τ hτ
    have hex := (hCim _).1 (hcd τ (norm_pos_iff.2 hτ.2) (lt_of_lt_of_le (mem_ball_zero_iff.1 hτ.1) hρ'ρ))
    exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
  have hopen : IsOpen (Metric.ball (0 : ℂ) ρ' \ {0}) := Metric.isOpen_ball.sdiff isClosed_singleton
  have hψd : DifferentiableOn ℂ ψ (Metric.ball 0 ρ' \ {0}) := by
    intro τ₀ hτ₀
    obtain ⟨hσ₀r, hσ₀⟩ := hψ τ₀ hτ₀
    have hδ : 0 < c.radius - ‖ψ τ₀‖ := sub_pos.2 (mem_ball_zero_iff.1 hσ₀r)
    have hballsub : Metric.ball (ψ τ₀) (c.radius - ‖ψ τ₀‖) ⊆ Metric.ball 0 c.radius :=
      Metric.ball_subset_ball' (by rw [dist_zero_right]; linarith)
    have hne : (d.toFun fun _ ↦ τ₀) ≠ q := fun h ↦
      hτ₀.2 (hDi (hsub hτ₀.1) (Metric.mem_ball_self d.radius_pos) (h.trans hD0.symm))
    have hε₀ : (d.toFun fun _ ↦ τ₀) ∈ Metric.ball q ε := by
      have := hρ₁ε (x := τ₀) (by rw [dist_zero_right]; exact lt_of_lt_of_le (mem_ball_zero_iff.1 hτ₀.1) hρ'1)
      rw [Metric.mem_ball]
      rwa [hD0] at this
    obtain ⟨U, hUo, hUx, Ψ, hΨd, hΨ⟩ := hcutε (fun σ ↦ c.toFun fun _ ↦ σ) (ψ τ₀) (c.radius - ‖ψ τ₀‖) hδ
      (hCd.mono hballsub) (hCi.mono hballsub) (fun σ hσ ↦ hCm (hballsub hσ))
      (by show (c.toFun fun _ ↦ ψ τ₀) ∈ Metric.ball q ε; rw [hσ₀]; exact hε₀)
      (by show (c.toFun fun _ ↦ ψ τ₀) ≠ q; rw [hσ₀]; exact hne)
    have hUD : (d.toFun fun _ ↦ τ₀) ∈ U := by
      have hUx' : (c.toFun fun _ ↦ ψ τ₀) ∈ U := hUx
      rwa [hσ₀] at hUx'
    have hDdiff : DifferentiableAt ℂ (fun τ : ℂ ↦ d.toFun fun _ ↦ τ) τ₀ :=
      hDd.differentiableAt (Metric.isOpen_ball.mem_nhds (hsub hτ₀.1))
    have hevU : ∀ᶠ τ in 𝓝 τ₀, (d.toFun fun _ ↦ τ) ∈ U :=
      hDdiff.continuousAt.preimage_mem_nhds (hUo.mem_nhds hUD)
    have heq : ψ =ᶠ[𝓝 τ₀] fun τ ↦ Ψ (d.toFun fun _ ↦ τ) := by
      filter_upwards [hevU, hopen.mem_nhds hτ₀] with τ hτU hτ
      obtain ⟨σ, hσ, hσz, hΨσ⟩ := hΨ (d.toFun fun _ ↦ τ) ⟨hDm (hsub hτ.1), hτU⟩
      rw [hΨσ]
      exact hCi (hψ τ hτ).1 (hballsub hσ) ((hψ τ hτ).2.trans hσz.symm)
    have hdiff : DifferentiableAt ℂ (fun τ ↦ Ψ (d.toFun fun _ ↦ τ)) τ₀ :=
      (hΨd.differentiableAt (hUo.mem_nhds hUD)).comp τ₀ hDdiff
    exact (hdiff.congr_of_eventuallyEq heq).differentiableWithinAt
  exact factor_of_punctured (C := fun σ : ℂ ↦ c.toFun fun _ ↦ σ) (D := fun τ : ℂ ↦ d.toFun fun _ ↦ τ)
    c.radius_pos hρ'pos hCd hCi (hDd.mono hsub) (hDi.mono hsub) (hC0.trans hD0.symm) hψd hψ

end PuncturedBranchSameOrder

theorem PuncturedBranchSameOrder.proof (hcut : PuncturedCurveDiscInverse.Statement) :
    PuncturedBranchSameOrder.Statement := by
  intro n I q c d ρ hI hdim hρ hcd f
  obtain ⟨g, hga, hg0, hev, hmap⟩ := PuncturedBranchSameOrder.punctured_factor hcut hI hdim c d ρ hρ hcd
  have hBd : Metric.ball (0 : ℂ) d.radius ∈ 𝓝 0 := Metric.ball_mem_nhds 0 d.radius_pos
  have hdc : ∃ ρ'' > 0, ∀ σ : ℂ, 0 < ‖σ‖ → ‖σ‖ < ρ'' → c.toFun (fun _ ↦ σ) ∈ d.image := by
    have hA : {τ : ℂ | τ ∈ Metric.ball 0 d.radius ∧ (d.toFun fun _ ↦ τ) = c.toFun fun _ ↦ g τ} ∈ 𝓝 0 :=
      Filter.Eventually.and hBd hev
    obtain ⟨ρ'', hρ'', hball⟩ := Metric.mem_nhds_iff.1 (hmap (Filter.image_mem_map hA))
    refine ⟨ρ'', hρ'', fun σ _ hσ ↦ ?_⟩
    obtain ⟨τ, ⟨hτd, hτeq⟩, rfl⟩ := hball (mem_ball_zero_iff.2 hσ)
    exact ((PuncturedBranchSameOrder.disc_props d).2.2.2.2 _).2 ⟨τ, hτd, hτeq⟩
  obtain ⟨ρ'', hρ'', hdc'⟩ := hdc
  obtain ⟨k, hka, hk0, hev', -⟩ := PuncturedBranchSameOrder.punctured_factor hcut hI hdim d c ρ'' hρ'' hdc'
  have hgt : Tendsto g (𝓝 0) (𝓝 0) := by
    have := hga.continuousAt.tendsto
    rwa [hg0] at this
  have hkt : Tendsto k (𝓝 0) (𝓝 0) := by
    have := hka.continuousAt.tendsto
    rwa [hk0] at this
  have hid : (fun τ ↦ k (g τ)) =ᶠ[𝓝 0] id := by
    filter_upwards [hgt.eventually hev', (hkt.comp hgt).eventually hBd, hev, hBd] with τ h1 h2 h3 h4
    exact (PuncturedBranchSameOrder.disc_props d).2.1 h2 h4 (h1.symm.trans h3.symm)
  have hgd : deriv g 0 ≠ 0 := by
    intro hz
    have hk' : HasDerivAt k (deriv k 0) (g 0) := by
      rw [hg0]
      exact hka.differentiableAt.hasDerivAt
    have e1 : HasDerivAt (fun τ ↦ k (g τ)) (deriv k 0 * deriv g 0) 0 :=
      hk'.comp 0 hga.differentiableAt.hasDerivAt
    have e2 : HasDerivAt (fun τ ↦ k (g τ)) 1 0 := (hasDerivAt_id 0).congr_of_eventuallyEq hid
    have := e1.unique e2
    rw [hz, mul_zero] at this
    exact zero_ne_one this
  have hcong : (fun τ : ℂ ↦ eval (d.toFun fun _ ↦ τ) f) =ᶠ[𝓝 0]
      (fun σ : ℂ ↦ eval (c.toFun fun _ ↦ σ) f) ∘ g := by
    filter_upwards [hev] with τ hτ
    rw [Function.comp_apply, hτ]
  show analyticOrderAt (fun τ : ℂ ↦ eval (c.toFun fun _ ↦ τ) f) 0 =
    analyticOrderAt (fun τ : ℂ ↦ eval (d.toFun fun _ ↦ τ) f) 0
  rw [analyticOrderAt_congr hcong, analyticOrderAt_comp_of_deriv_ne_zero hga hgd, hg0]

end

end GroundTheory.Heights₂.Heights
