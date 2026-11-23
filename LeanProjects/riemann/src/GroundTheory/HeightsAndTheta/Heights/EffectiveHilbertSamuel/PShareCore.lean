import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.StatementsShare
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open Filter Topology

noncomputable section

variable {n : ℕ} {MS : Type} [TopologicalSpace MS]

theorem HolomorphicAlong.analyticOnNhd {z : MS → (Fin n → ℂ)} {u : MS → ℂ}
    (hu : HolomorphicAlong z u) (e : OpenPartialHomeomorph MS (Fin n → ℂ))
    (hz : ∀ q ∈ e.source, z q = e q) : AnalyticOnNhd ℂ (u ∘ e.symm) e.target := by
  intro x hx
  have hq : e.symm x ∈ e.source := e.map_target hx
  obtain ⟨e', hq', hz', han⟩ := hu (e.symm x)
  have hex : e' (e.symm x) = x := by rw [← hz' _ hq', hz _ hq, e.right_inv hx]
  have hx' : x ∈ e'.target := hex ▸ e'.map_source hq'
  refine (han x hx').congr ?_
  have h1 : ∀ᶠ x' in 𝓝 x, x' ∈ e.target := e.open_target.mem_nhds hx
  have h2 : ∀ᶠ x' in 𝓝 x, e.symm x' ∈ e'.source :=
    (e.continuousAt_symm hx).preimage_mem_nhds (e'.open_source.mem_nhds hq')
  filter_upwards [h1, h2] with x' h1 h2
  have h3 : e' (e.symm x') = x' := by rw [← hz' _ h2, hz _ (e.map_target h1), e.right_inv h1]
  have h4 : e'.symm x' = e.symm x' := by
    calc e'.symm x' = e'.symm (e' (e.symm x')) := by rw [h3]
      _ = e.symm x' := e'.left_inv h2
  simp only [Function.comp_apply, h4]

theorem HolomorphicAlong.continuous {z : MS → (Fin n → ℂ)} {u : MS → ℂ}
    (hu : HolomorphicAlong z u) : Continuous u := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  obtain ⟨e, hp, -, han⟩ := hu p
  have hc : ContinuousAt ((u ∘ e.symm) ∘ e) p :=
    (han (e p) (e.map_source hp)).continuousAt.comp (e.continuousAt hp)
  refine hc.congr ?_
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  simp [e.left_inv hq]

theorem HolomorphicAlong.mul {z : MS → (Fin n → ℂ)} {u v : MS → ℂ}
    (hu : HolomorphicAlong z u) (hv : HolomorphicAlong z v) :
    HolomorphicAlong z (fun p => u p * v p) := by
  intro p
  obtain ⟨e, hp, hz, -⟩ := hu p
  exact ⟨e, hp, hz, (hu.analyticOnNhd e hz).mul (hv.analyticOnNhd e hz)⟩

theorem HolomorphicAlong.pow {z : MS → (Fin n → ℂ)} {u : MS → ℂ}
    (hu : HolomorphicAlong z u) (k : ℕ) : HolomorphicAlong z (fun p => u p ^ k) := by
  intro p
  obtain ⟨e, hp, hz, -⟩ := hu p
  exact ⟨e, hp, hz, (hu.analyticOnNhd e hz).pow k⟩

theorem HolomorphicAlong.eq_zero_of_eventually [ConnectedSpace MS] {z : MS → (Fin n → ℂ)}
    {u : MS → ℂ} (hu : HolomorphicAlong z u) {p₀ : MS} (h₀ : u =ᶠ[𝓝 p₀] 0) : u = 0 := by
  set A : Set MS := {p | u =ᶠ[𝓝 p] 0} with hA
  have hAo : IsOpen A := isOpen_setOfPred_eventually_nhds
  have hAc : IsClosed A := by
    refine isClosed_of_closure_subset fun p hp => ?_
    obtain ⟨e, hpe, hz, -⟩ := hu p
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 e.open_target (e p) (e.map_source hpe)
    have hV : e.source ∩ e ⁻¹' Metric.ball (e p) ε ∈ 𝓝 p :=
      inter_mem (e.open_source.mem_nhds hpe)
        ((e.continuousAt hpe).preimage_mem_nhds (Metric.ball_mem_nhds _ hε))
    obtain ⟨q, ⟨hqs, hqb⟩, hqA⟩ := mem_closure_iff_nhds.1 hp _ hV
    have han : AnalyticOnNhd ℂ (u ∘ e.symm) (Metric.ball (e p) ε) :=
      (hu.analyticOnNhd e hz).mono hball
    have hev : (u ∘ e.symm) =ᶠ[𝓝 (e q)] 0 := by
      have ht : Tendsto e.symm (𝓝 (e q)) (𝓝 q) := by
        have := (e.continuousAt_symm (e.map_source hqs)).tendsto
        rwa [e.left_inv hqs] at this
      exact ht.eventually hqA
    have hzero := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (e p) ε).isPreconnected hqb hev
    show u =ᶠ[𝓝 p] 0
    filter_upwards [hV] with q' ⟨hq's, hq'b⟩
    have := hzero hq'b
    simpa [e.left_inv hq's] using this
  have huniv : A = Set.univ := IsClopen.eq_univ ⟨hAc, hAo⟩ ⟨p₀, h₀⟩
  funext p
  have hp : p ∈ A := huniv ▸ Set.mem_univ p
  exact hp.self_of_nhds

theorem HolomorphicAlong.eq_zero_of_mul_eq_zero [ConnectedSpace MS] {z : MS → (Fin n → ℂ)}
    {g h : MS → ℂ} (hg : HolomorphicAlong z g) (hh : HolomorphicAlong z h)
    (hgh : ∀ p, g p * h p = 0) (hg0 : g ≠ 0) : h = 0 := by
  obtain ⟨p, hp⟩ : ∃ p, g p ≠ 0 := by
    by_contra H
    exact hg0 (funext fun p => by_contra fun hp => H ⟨p, hp⟩)
  have hne : ∀ᶠ q in 𝓝 p, g q ≠ 0 := hg.continuous.continuousAt.eventually_ne hp
  refine hh.eq_zero_of_eventually (p₀ := p) ?_
  filter_upwards [hne] with q hq
  exact (mul_eq_zero.1 (hgh q)).resolve_left hq

theorem eventually_norm_le_of_continuous {u : MS → ℂ} (hu : Continuous u) (p : MS) :
    ∀ᶠ q in 𝓝 p, ‖u q‖ ≤ ‖u p‖ + 1 := by
  have : ∀ᶠ q in 𝓝 p, ‖u q‖ < ‖u p‖ + 1 :=
    hu.norm.continuousAt.preimage_mem_nhds (Iio_mem_nhds (lt_add_one _))
  filter_upwards [this] with q hq using hq.le

theorem ShareCore.proof (hNorm : NormLemma.Statement) : ShareCore.Statement := by
  intro n MS _ _ _ _ De z δ f θ τ C e a hDe hcov hf hθ hτ hθ0 hτ0 hbound hord
  have hτa : HolomorphicAlong z (fun p => τ p ^ a) := hτ.pow a
  have hg : HolomorphicAlong z (fun p => θ p * τ p ^ a) := hθ.mul hτa
  have hg0 : (fun p => θ p * τ p ^ a) ≠ 0 := by
    intro H
    have h0 : (fun p => τ p ^ a) = 0 :=
      hθ.eq_zero_of_mul_eq_zero hτa (fun p => congrFun H p) hθ0
    exact hτ0 (funext fun p => eq_zero_of_pow_eq_zero (congrFun h0 p))
  have hu : HolomorphicAlong z (fun p => f p * θ p * τ p ^ a) := (hf.mul hθ).mul hτa
  have horder : ∀ p, z p = 0 → OrderGT z (fun p => f p * θ p * τ p ^ a) p e := by
    intro p hp
    obtain ⟨Cf, hCf⟩ := hord p hp
    refine ⟨Cf * ((‖θ p‖ + 1) * (‖τ p‖ + 1) ^ a), ?_⟩
    filter_upwards [hCf, eventually_norm_le_of_continuous hθ.continuous p,
      eventually_norm_le_of_continuous hτ.continuous p] with q hq1 hq2 hq3
    rw [norm_mul, norm_mul, norm_pow]
    have hr : 0 ≤ Cf * Real.sqrt (normSq (z q - z p)) ^ (e + 1) := (norm_nonneg _).trans hq1
    calc ‖f q‖ * ‖θ q‖ * ‖τ q‖ ^ a
        ≤ (Cf * Real.sqrt (normSq (z q - z p)) ^ (e + 1)) * (‖θ p‖ + 1) * (‖τ p‖ + 1) ^ a := by
          gcongr
      _ = Cf * ((‖θ p‖ + 1) * (‖τ p‖ + 1) ^ a) * Real.sqrt (normSq (z q - z p)) ^ (e + 1) := by
          ring
  have hu0 := hNorm n MS De z δ _ C e hDe hcov hu hbound horder
  exact hg.eq_zero_of_mul_eq_zero hf (fun p => by
    have := congrFun hu0 p
    simp only [Pi.zero_apply] at this
    linear_combination this) hg0

theorem ShareNumbers.proof : ShareNumbers.Statement := by
  intro D N T hD hN hT
  have h11 : 11 * D ≤ T := by nlinarith
  refine ⟨?_, ?_, ?_⟩ <;> omega

end

end GroundTheory.Heights₂.Heights.EffectiveHS
