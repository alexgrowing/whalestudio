import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacOut

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex

namespace PositivityTheory.Rg.Sw.AbsSt.HP

variable {X : Type} [TopologicalSpace X]

theorem eventually_unif {C : Set X} {U K : Set ℂ} {F : X → ℂ → ℂ}
    (hF : ContinuousOn (fun y : X × ℂ => F y.1 y.2) (C ×ˢ U)) (hK : IsCompact K) (hKU : K ⊆ U) {x₀ : X} (hx₀ : x₀ ∈ C)
    {η : ℝ} (hη : 0 < η) : ∀ᶠ x in 𝓝 x₀, ∀ ζ ∈ K, x ∈ C → ζ ∈ U → ‖F x ζ - F x₀ ζ‖ < η := by
  have key : ∀ ζ ∈ K, ∀ᶠ p : X × ℂ in 𝓝 (x₀, ζ), p.1 ∈ C → p.2 ∈ U → ‖F p.1 p.2 - F x₀ p.2‖ < η := by
    intro ζ hζ
    have hc := hF (x₀, ζ) ⟨hx₀, hKU hζ⟩
    have h1 : ∀ᶠ p : X × ℂ in 𝓝 (x₀, ζ), p ∈ C ×ˢ U → dist (F p.1 p.2) (F x₀ ζ) < η / 2 :=
      eventually_nhdsWithin_iff.mp (hc.eventually (Metric.ball_mem_nhds _ (half_pos hη)))
    have hg : Tendsto (fun p : X × ℂ => (x₀, p.2)) (𝓝 (x₀, ζ)) (𝓝 (x₀, ζ)) := by
      have hcont : Continuous (fun p : X × ℂ => (x₀, p.2)) := by fun_prop
      simpa using hcont.tendsto (x₀, ζ)
    have h2 := hg.eventually h1
    filter_upwards [h1, h2] with p hp1 hp2 hpC hpU
    have a := hp1 ⟨hpC, hpU⟩
    have b : dist (F x₀ p.2) (F x₀ ζ) < η / 2 := hp2 ⟨hx₀, hpU⟩
    rw [← dist_eq_norm]
    calc dist (F p.1 p.2) (F x₀ p.2) ≤ dist (F p.1 p.2) (F x₀ ζ) + dist (F x₀ p.2) (F x₀ ζ) :=
          dist_triangle_right _ _ _
      _ < η / 2 + η / 2 := add_lt_add a b
      _ = η := add_halves η
  filter_upwards [hK.eventually_forall_of_forall_eventually
    (P := fun x ζ => x ∈ C → ζ ∈ U → ‖F x ζ - F x₀ ζ‖ < η) key] with x hx ζ hζ hxC hζU
  exact hx ζ hζ hxC hζU

theorem continuousOn_deriv {C : Set X} {U : Set ℂ} {F : X → ℂ → ℂ} (hU : IsOpen U)
    (hF : ContinuousOn (fun y : X × ℂ => F y.1 y.2) (C ×ˢ U)) (hd : ∀ x ∈ C, DifferentiableOn ℂ (F x) U) :
    ContinuousOn (fun y : X × ℂ => deriv (F y.1) y.2) (C ×ˢ U) := by
  intro ⟨x₀, z₀⟩ ⟨hx₀, hz₀⟩
  have hT : TendstoLocallyUniformlyOn F (F x₀) (𝓝[C] x₀) U := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
    intro K hKU hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [nhdsWithin_le_nhds (eventually_unif hF hK hKU hx₀ hε), self_mem_nhdsWithin]
      with x hx hxC ζ hζ
    rw [dist_comm, dist_eq_norm]
    exact hx ζ hζ hxC (hKU hζ)
  have hD : ∀ᶠ x in 𝓝[C] x₀, DifferentiableOn ℂ (F x) U := by
    filter_upwards [self_mem_nhdsWithin] with x hx using hd x hx
  have hT' := hT.deriv hD hU
  have hc : ContinuousAt (deriv (F x₀)) z₀ :=
    (((hd x₀ hx₀).deriv hU).continuousOn z₀ hz₀).continuousAt (hU.mem_nhds hz₀)
  rw [Metric.continuousWithinAt_iff']
  intro ε hε
  obtain ⟨t, ht, hA⟩ := (Metric.tendstoLocallyUniformlyOn_iff.mp hT') (ε / 2) (half_pos hε) z₀ hz₀
  have hB := (Metric.continuousAt_iff'.mp hc) (ε / 2) (half_pos hε)
  have hB' : ∀ᶠ y in 𝓝[U] z₀, y ∈ t ∧ dist (deriv (F x₀) y) (deriv (F x₀) z₀) < ε / 2 :=
    Filter.inter_mem ht (nhdsWithin_le_nhds hB)
  rw [nhdsWithin_prod_eq]
  filter_upwards [Filter.prod_mem_prod hA hB'] with q hq
  have h1 : dist (deriv (F x₀) q.2) (deriv (F q.1) q.2) < ε / 2 := hq.1 q.2 hq.2.1
  have h2 : dist (deriv (F x₀) q.2) (deriv (F x₀) z₀) < ε / 2 := hq.2.2
  show dist (deriv (F q.1) q.2) (deriv (F x₀) z₀) < ε
  have h3 := dist_triangle (deriv (F q.1) q.2) (deriv (F x₀) q.2) (deriv (F x₀) z₀)
  rw [dist_comm] at h1
  linarith

theorem eqOn_iteratedDeriv {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ} (h : EqOn f g U) :
    ∀ r : ℕ, EqOn (iteratedDeriv r f) (iteratedDeriv r g) U := by
  intro r
  induction r with
  | zero => simpa using h
  | succ r ih =>
    intro z hz
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    exact (ih.eventuallyEq_of_mem (hU.mem_nhds hz)).deriv_eq

variable [MeasurableSpace X] [BorelSpace X]

theorem aesm_of {μ : Measure X} {C : Set X} (hC : IsCompact C) (hCn : μ Cᶜ = 0) {f : X → ℂ}
    (hf : ContinuousOn f C) : AEStronglyMeasurable f μ := by
  set t := (toMeasurable μ Cᶜ)ᶜ with ht
  have htm : MeasurableSet t := (measurableSet_toMeasurable μ Cᶜ).compl
  have htC : t ⊆ C := by
    intro x hx
    by_contra hxC
    exact hx (subset_toMeasurable μ Cᶜ hxC)
  have hμ : μ.restrict t = μ := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    have e : {a | ¬ a ∈ t} = toMeasurable μ Cᶜ := by
      ext a
      simp [ht]
    rw [e, measure_toMeasurable]
    exact hCn
  have hh := hf.aestronglyMeasurable_of_subset_isCompact (μ := μ) hC htm htC
  rwa [hμ] at hh

theorem hasDerivAt_int {μ : Measure X} [IsFiniteMeasure μ] {C : Set X} (hC : IsCompact C) (hCn : μ Cᶜ = 0)
    {U : Set ℂ} {F : X → ℂ → ℂ} (hU : IsOpen U)
    (hF : ContinuousOn (fun y : X × ℂ => F y.1 y.2) (C ×ˢ U)) (hd : ∀ x ∈ C, DifferentiableOn ℂ (F x) U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) : HasDerivAt (fun z => ∫ x, F x z ∂μ) (∫ x, deriv (F x) z₀ ∂μ) z₀ := by
  have hcz : ∀ z ∈ U, ContinuousOn (fun x => F x z) C := fun z hz =>
    hF.comp (by fun_prop : Continuous fun x : X => (x, z)).continuousOn (fun x hx => ⟨hx, hz⟩)
  have hmeas : ∀ z ∈ U, AEStronglyMeasurable (fun x => F x z) μ :=
    fun z hz => aesm_of hC hCn (hcz z hz)
  have hae : ∀ᵐ x ∂μ, x ∈ C := ae_iff.mpr hCn
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  have hsub : closedBall z₀ (ε / 2) ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hball
  have hD := continuousOn_deriv hU hF hd
  obtain ⟨M, hM⟩ := (hC.prod (isCompact_closedBall z₀ (ε / 2))).exists_bound_of_continuousOn
    (hD.mono (prod_mono subset_rfl hsub))
  obtain ⟨M0, hM0⟩ := (hC.prod (isCompact_closedBall z₀ (ε / 2))).exists_bound_of_continuousOn
    (hF.mono (prod_mono subset_rfl hsub))
  have hint : Integrable (fun x => F x z₀) μ := by
    refine Integrable.of_bound (hmeas z₀ hz₀) M0 ?_
    filter_upwards [hae] with x hx
    exact hM0 (x, z₀) ⟨hx, mem_closedBall_self (half_pos hε).le⟩
  have hcd : ContinuousOn (fun x => deriv (F x) z₀) C :=
    hD.comp (by fun_prop : Continuous fun x : X => (x, z₀)).continuousOn (fun x hx => ⟨hx, hz₀⟩)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := fun z x => F x z)
    (F' := fun z x => deriv (F x) z) (bound := fun _ => M)
    (closedBall_mem_nhds z₀ (half_pos hε))
    (Filter.eventually_of_mem (hU.mem_nhds hz₀) hmeas) hint (aesm_of hC hCn hcd)
    (by filter_upwards [hae] with x hx z hz using hM (x, z) ⟨hx, hz⟩)
    (integrable_const M)
    (by
      filter_upwards [hae] with x hx z hz
      exact (((hd x hx) z (hsub hz)).differentiableAt (hU.mem_nhds (hsub hz))).hasDerivAt)
  exact key.2

theorem main {μ : Measure X} [IsFiniteMeasure μ] {C : Set X} (hC : IsCompact C) (hCn : μ Cᶜ = 0)
    {U : Set ℂ} (hU : IsOpen U) : ∀ (r : ℕ) (F : X → ℂ → ℂ), ContinuousOn (fun y : X × ℂ => F y.1 y.2) (C ×ˢ U) →
      (∀ x ∈ C, DifferentiableOn ℂ (F x) U) →
      ∀ z ∈ U, iteratedDeriv r (fun z => ∫ x, F x z ∂μ) z = ∫ x, iteratedDeriv r (F x) z ∂μ := by
  intro r
  induction r with
  | zero =>
    intro F _ _ z _
    simp
  | succ n ih =>
    intro F hF hd z hz
    have hEq : EqOn (deriv (fun z => ∫ x, F x z ∂μ)) (fun z => ∫ x, deriv (F x) z ∂μ) U :=
      fun w hw => (hasDerivAt_int hC hCn hU hF hd hw).deriv
    rw [iteratedDeriv_succ', eqOn_iteratedDeriv hU hEq n hz,
      ih (fun x => deriv (F x)) (continuousOn_deriv hU hF hd) (fun x hx => (hd x hx).deriv hU) z hz]
    simp_rw [iteratedDeriv_succ']

end PositivityTheory.Rg.Sw.AbsSt.HP

namespace PositivityTheory.Rg.Sw.AbsSt

theorem holParam : HolParam := by
  intro X _ _ _ μ _ C hC hCn U F hU hF hd
  exact ⟨fun z hz => (HP.hasDerivAt_int hC hCn hU hF hd hz).differentiableAt.differentiableWithinAt,
    fun z hz r => HP.main hC hCn hU r F hF hd z hz⟩

end PositivityTheory.Rg.Sw.AbsSt
