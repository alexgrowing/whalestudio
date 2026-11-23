import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveCoordinateGraph
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveRegularOffCentre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

theorem isCoordinateGraphNear_of_chart {n : ℕ} {X : Set (Fin n → ℂ)} {x : Fin n → ℂ}
    (A : (Fin n → ℂ) →L[ℂ] ℂ) (O : Set ℂ) (V : Set (Fin n → ℂ)) (g : ℂ → Fin n → ℂ)
    (hO : IsOpen O) (hV : IsOpen V) (hxV : x ∈ V) (hxX : x ∈ X) (hg : AnalyticOnNhd ℂ g O)
    (hAg : ∀ y ∈ O, A (g y) = y) (hXV : X ∩ V = g '' O) : IsCoordinateGraphNear X x := by
  obtain ⟨y₀, hy₀O, hgy₀⟩ : x ∈ g '' O := hXV ▸ ⟨hxX, hxV⟩

  have hAd : ∀ y ∈ O, A (deriv g y) = 1 := by
    intro y hy
    have h1 : HasDerivAt (fun t ↦ A (g t)) (A (deriv g y)) y :=
      A.hasFDerivAt.comp_hasDerivAt y (hg y hy).differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun t ↦ A (g t)) 1 y :=
      (hasDerivAt_id' y).congr_of_eventuallyEq (eventually_of_mem (hO.mem_nhds hy) hAg)
    exact h1.unique h2

  obtain ⟨i, hi⟩ : ∃ i, deriv g y₀ i ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : deriv g y₀ = 0 := funext h
    simpa [h0] using hAd y₀ hy₀O
  set φ : ℂ → ℂ := fun y ↦ g y i with hφdef
  have hφ : AnalyticOnNhd ℂ φ O := fun y hy ↦
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i).analyticAt (g y)).comp (hg y hy)
  have hφd : ∀ y ∈ O, HasDerivAt φ (deriv g y i) y := fun y hy ↦
    hasDerivAt_pi.1 (hg y hy).differentiableAt.hasDerivAt i

  set U : Set ℂ := O ∩ deriv φ ⁻¹' {0}ᶜ with hUdef
  have hU : IsOpen U := hφ.deriv.continuousOn.isOpen_inter_preimage hO isOpen_compl_singleton
  have hy₀U : y₀ ∈ U := ⟨hy₀O, by simpa [(hφd y₀ hy₀O).deriv] using hi⟩
  have hs : HasStrictDerivAt φ (deriv g y₀ i) y₀ := by
    simpa [(hφd y₀ hy₀O).deriv] using (hφ y₀ hy₀O).hasStrictDerivAt
  set e := ((hs.hasStrictFDerivAt_equiv hi).toOpenPartialHomeomorph φ).restrOpen U hU with hedef
  have he : ∀ y, e y = φ y := fun _ ↦ rfl
  have hsrc : ∀ {y}, y ∈ e.source → y ∈ U := fun hy ↦ hy.2
  have hy₀e : y₀ ∈ e.source := ⟨(hs.hasStrictFDerivAt_equiv hi).mem_toOpenPartialHomeomorph_source, hy₀U⟩
  refine ⟨hxX, V ∩ A ⁻¹' e.source ∩ (fun z ↦ z i) ⁻¹' e.target,
    (hV.inter (e.open_source.preimage A.continuous)).inter (e.open_target.preimage (continuous_apply i)),
    ⟨⟨hxV, ?_⟩, ?_⟩, i, e.target, fun t ↦ g (e.symm t), e.open_target, ?_, ?_, ?_⟩
  · show A x ∈ e.source
    rw [← hgy₀, hAg y₀ hy₀O]
    exact hy₀e
  · show x i ∈ e.target
    rw [← hgy₀, show g y₀ i = e y₀ from rfl]
    exact e.map_source hy₀e
  · intro t ht
    have hyt := hsrc (e.map_target ht)
    have hder : HasDerivAt e (deriv φ (e.symm t)) (e.symm t) :=
      (hφ _ hyt.1).differentiableAt.hasDerivAt
    exact ((hg _ hyt.1).differentiableAt.comp t
      (e.hasDerivAt_symm ht hyt.2 hder).differentiableAt).differentiableWithinAt
  · intro t ht
    have h := e.right_inv ht
    rw [he] at h
    exact h
  · rintro z ⟨⟨hzV, hzA⟩, hzi⟩
    constructor
    · intro hzX
      obtain ⟨y, hyO, rfl⟩ : z ∈ g '' O := hXV ▸ ⟨hzX, hzV⟩
      have hye : y ∈ e.source := by simpa [hAg y hyO] using hzA
      refine ⟨hzi, ?_⟩
      show g (e.symm (e y)) = g y
      rw [e.left_inv hye]
    · rintro ⟨ht, hgz⟩
      have hyO := (hsrc (e.map_target ht)).1
      have : z ∈ X ∩ V := hXV ▸ ⟨_, hyO, hgz⟩
      exact this.1

theorem CurveCoordinateGraph.proof (hR : CurveRegularOffCentre.Statement) : CurveCoordinateGraph.Statement := by
  intro n I q _ hdim
  obtain ⟨N, hN, hNx⟩ := hR n I q hdim
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hN
  refine ⟨ε, hε, fun x hxZ hxb hxq ↦ ?_⟩
  obtain ⟨A, O, V, g, hO, hV, hxV, hg, hAg, hZV⟩ := hNx x ⟨hxZ, hball hxb⟩ hxq
  exact isCoordinateGraphNear_of_chart A O V g hO hV hxV hxZ hg hAg hZV

end

end GroundTheory.Heights₂.Heights
