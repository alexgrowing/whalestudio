import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
namespace GlobalTheory.L2Cutoff

theorem cutoff_smooth_dbar : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (ψ : M → ℝ) (G : M → ℂ) (Ω : Set M) (δ b : ℝ) (θ : ℝ → ℝ), SmoothR n X.z ψ → ContDiff ℝ ∞ θ → (∀ t, b ≤ t → θ t = 0) → IsOpen Ω → (∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → DifferentiableOn ℂ (G ∘ e.symm) (e.target ∩ e.symm ⁻¹' Ω)) → (∀ x, δ * ψ x ≤ b → x ∈ Ω) → Smooth n X.z (fun x => (θ (δ * ψ x) : ℂ) * G x) ∧ ∀ (x : M) (ξ : Fin n → ℂ), dbarDot n X.z (fun y => (θ (δ * ψ y) : ℂ) * G y) x ξ = ((deriv θ (δ * ψ x) * δ : ℝ) : ℂ) * G x * dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ := by
  intro n M _ _ _ _ _ X ψ G Ω δ b θ hψ hθ hθ0 hΩ hG hsub
  have hψe : ∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e →
      ContDiffOn ℝ ∞ (fun v => ψ (e.symm v)) e.target := by
    intro e he
    have h1 := (Complex.reCLM.contDiff (n := ∞)).comp_contDiffOn (hψ e he)
    refine h1.congr fun v _ => ?_
    simp
  have hθd : ∀ t, DifferentiableAt ℝ θ t := fun t => (hθ.differentiable (by simp)) t
  have hθzero : ∀ t, b < t → θ =ᶠ[𝓝 t] fun _ => 0 := by
    intro t ht
    filter_upwards [lt_mem_nhds ht] with s hs
    exact hθ0 s hs.le
  have hloc : ∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → ∀ v ∈ e.target,
      (e.symm v ∈ Ω → DifferentiableAt ℂ (G ∘ e.symm) v) ∧
      (e.symm v ∉ Ω → ((fun x => (θ (δ * ψ x) : ℂ) * G x) ∘ e.symm) =ᶠ[𝓝 v] fun _ => 0) := by
    intro e he v hv
    constructor
    · intro hvΩ
      exact (hG e he).differentiableAt
        ((e.isOpen_inter_preimage_symm hΩ).mem_nhds ⟨hv, hvΩ⟩)
    · intro hvΩ
      have hb : b < δ * ψ (e.symm v) := by
        by_contra h
        exact hvΩ (hsub _ (not_lt.1 h))
      have hc : ContinuousAt (fun w => δ * ψ (e.symm w)) v :=
        continuousAt_const.mul ((hψe e he).continuousOn.continuousAt (e.open_target.mem_nhds hv))
      filter_upwards [hc.eventually (lt_mem_nhds hb)] with w hw
      simp [hθ0 _ hw.le]
  refine ⟨?_, ?_⟩
  · intro e he v hv
    apply ContDiffAt.contDiffWithinAt
    by_cases hvΩ : e.symm v ∈ Ω
    · have hU := (e.isOpen_inter_preimage_symm hΩ).mem_nhds ⟨hv, hvΩ⟩
      have hGc : ContDiffAt ℝ ∞ (G ∘ e.symm) v :=
        ((contDiffOn_of_differentiableOn n _ _ (e.isOpen_inter_preimage_symm hΩ) (hG e he)).contDiffAt
          hU).restrict_scalars ℝ
      have hk : ContDiffAt ℝ ∞ (fun w => ((θ (δ * ψ (e.symm w)) : ℝ) : ℂ)) v :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp v
          (hθ.contDiffAt.comp v (contDiffAt_const.mul
            ((hψe e he).contDiffAt (e.open_target.mem_nhds hv))))
      exact hk.mul hGc
    · exact contDiffAt_const.congr_of_eventuallyEq ((hloc e he v hv).2 hvΩ)
  · intro x ξ
    obtain ⟨e, he, hx⟩ := exists_chart n X.z X.isLocalHomeomorph x
    have hzx : X.z x = e x := he hx
    have hv : X.z x ∈ e.target := by rw [hzx]; exact e.map_source hx
    have hsx : e.symm (X.z x) = x := by rw [hzx]; exact e.left_inv hx
    unfold dbarDot
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [db_eq_wdb n X.z e he j _ x hx, db_eq_wdb n X.z e he j _ x hx]
    by_cases hxΩ : x ∈ Ω
    · have hGd := (hloc e he _ hv).1 (by rw [hsx]; exact hxΩ)
      have hψd : DifferentiableAt ℝ (fun w => ψ (e.symm w)) (X.z x) :=
        ((hψe e he).contDiffAt (e.open_target.mem_nhds hv)).differentiableAt (by simp)
      have hkd : DifferentiableAt ℝ (fun t => θ (δ * t)) (ψ (e.symm (X.z x))) :=
        (hθd _).comp _ ((differentiableAt_id).const_mul δ)
      have hderiv : deriv (fun t => θ (δ * t)) (ψ (e.symm (X.z x))) =
          deriv θ (δ * ψ (e.symm (X.z x))) * δ := by
        have h1 : HasDerivAt (fun t : ℝ => δ * t) δ (ψ (e.symm (X.z x))) := by
          simpa using (hasDerivAt_id (ψ (e.symm (X.z x)))).const_mul δ
        exact ((hθd _).hasDerivAt.comp _ h1).deriv
      have h1 : ((fun y => (θ (δ * ψ y) : ℂ) * G y) ∘ e.symm) =
          fun w => (((fun t => θ (δ * t)) (ψ (e.symm w)) : ℝ) : ℂ) * (G ∘ e.symm) w := rfl
      have hkd' : DifferentiableAt ℝ (fun w => (((fun t => θ (δ * t)) (ψ (e.symm w)) : ℝ) : ℂ))
          (X.z x) := differentiableAt_ofReal (DifferentiableAt.comp (f := fun w => ψ (e.symm w)) (X.z x) hkd hψd)
      rw [h1, wdb_mul hkd' (hGd.restrictScalars ℝ), wdb_of_differentiableAt hGd,
        wdb_ofReal_comp (k := fun t => θ (δ * t)) (v := fun w => ψ (e.symm w)) hkd hψd, hderiv]
      have h2 : ((fun y => (ψ y : ℂ)) ∘ e.symm) = fun w => ((ψ (e.symm w) : ℝ) : ℂ) := rfl
      rw [h2]
      simp only [Function.comp_apply, hsx]
      push_cast
      ring
    · have hb : b < δ * ψ x := by
        by_contra h
        exact hxΩ (hsub _ (not_lt.1 h))
      rw [wdb_congr ((hloc e he _ hv).2 (by rw [hsx]; exact hxΩ)),
        ((hθzero _ hb).deriv_eq)]
      simp [wdb]

end GlobalTheory.L2Cutoff
