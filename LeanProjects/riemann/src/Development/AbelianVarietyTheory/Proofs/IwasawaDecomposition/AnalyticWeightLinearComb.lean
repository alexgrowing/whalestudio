import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V cHess)
open GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts
open scoped ContDiff ENNReal

namespace GlobalTheory.ChernTransfer

variable {k k' : Type} [CommRing k] [CommRing k'] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k'}
  {σ : k →+* ℂ} {σ' : k' →+* ℂ} {D : ℕ} {j : Y ⟶ X} {Φ : CxPts q σ' ≃ₜ CxPts p σ}
  (hΦ : ∀ z, (Φ z).1 = z.1 ≫ j) {B : LB X} {φ : Weight p σ B}

abbrev pullW (φ : Weight p σ B) : Weight q σ' (LB.LinComb B (K := PUnit) (fun _ => j) fun _ => 1) :=
  φ.linComb (κ := PUnit) (fun _ => j) (fun _ => 1) (fun _ => Φ) (fun _ => hΦ)

theorem pullW_φ (i : PUnit → B.ι) (z : CxPts q σ') :
    (pullW hΦ φ).φ i z = φ.φ (i PUnit.unit) (Φ z) :=
  (Fintype.sum_unique fun a : PUnit.{1} => ((1 : ℤ) : ℝ) * φ.φ (i a) (Φ z)).trans (by simp)

include hΦ in

theorem ev_app' (W : X.Opens) (g : Γ(X, W)) (z : CxPts q σ') :
    ev q σ' (j ⁻¹ᵁ W) (j.app W g) z = ev p σ W g (Φ z) := by
  rw [ev, ev, hΦ]
  exact (valR_comp z.1 j W g).symm

include hΦ in

theorem mem_preimage_iff (W : X.Opens) (z : CxPts q σ') :
    z ∈ ptsIn q σ' (j ⁻¹ᵁ W) ↔ Φ z ∈ ptsIn p σ W := by
  change _ ↔ ⊤ ≤ (Φ z).1 ⁻¹ᵁ W
  rw [hΦ]
  rfl

theorem isCInf_pullW (h : φ.IsCInf) : (pullW hΦ φ).IsCInf := fun i z hz => by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h _ _
    (mem_of_mem_linComb (m := fun _ => Φ z) (fun _ => hΦ z) hz PUnit.unit)
  refine ⟨j ⁻¹ᵁ W, ι, inferInstance, fun a => j.app W (g a), F, O, (mem_preimage_iff hΦ W z).2 h₁,
    h₂, ?_, h₄, ?_⟩
  · simpa only [ev_app' hΦ] using h₃
  · simp only [ev_app' hΦ]
    filter_upwards [Φ.continuous.continuousAt.eventually h₅] with w hw
    exact (pullW_φ hΦ i w).trans hw

include hΦ in

theorem holo_trans (c : AlgChart p σ D) (c' : AlgChart q σ' D) :
    DifferentiableOn ℂ (Φ.transOpenPartialHomeomorph c.e ∘ c'.e.symm)
      (c'.e.target ∩ c'.e.symm ⁻¹' (Φ.transOpenPartialHomeomorph c.e).source) :=
  differentiableOn_euclidean.2 fun a => ((c'.holo _ (j.app c.U (c.x a))).mono fun _ hv =>
    ⟨hv.1, (mem_preimage_iff hΦ _ _).2 (c.source_subset hv.2)⟩).congr fun _ hv =>
      (c.apply_eq _ hv.2 a).trans (ev_app' hΦ _ _ _).symm

theorem chernDens_pullW (h : φ.IsCInf) (c : AlgChart p σ D) (c' : AlgChart q σ' D)
    {z : CxPts q σ'} (hz : z ∈ c'.e.source) (hz' : Φ z ∈ c.e.source) :
    c'.chernDens (pullW hΦ φ) z =
      ‖transDet c'.e (Φ.transOpenPartialHomeomorph c.e) z‖ ^ 2 * c.chernDens φ (Φ z) := by
  set e := Φ.transOpenPartialHomeomorph c.e with he
  have ho := isOpen_over c'.e e.open_source
  have hm := mem_over c'.e hz (S := e.source) hz'
  have hi : z ∈ ptsIn q σ' ((LB.LinComb B (K := PUnit) (fun _ => j) fun _ => 1).U
      fun _ => pick φ.isLB (Φ z)) :=
    ptsIn_mono (fun _ hx => mem_iInter.2 fun _ => hx)
      ((mem_preimage_iff hΦ _ z).2 (mem_pick φ.isLB (Φ z)))
  have e₁ : (fun v => ((pullW hΦ φ).φ (fun _ => pick φ.isLB (Φ z)) (c'.e.symm v) : ℂ))
      =ᶠ[𝓝 (c'.e z)] (fun v => (φ.φ (pick φ.isLB (Φ z)) (c.e.symm v) : ℂ)) ∘ e ∘ c'.e.symm :=
    eventually_of_mem (ho.mem_nhds hm) fun v hv => by
      have : c.e.symm (e (c'.e.symm v)) = Φ (c'.e.symm v) := c.e.left_inv hv.2
      simp only [Function.comp_apply, this, pullW_φ]
  have e₂ : (e ∘ c'.e.symm) (c'.e z) = c.e (Φ z) := congrArg e (c'.e.left_inv hz)
  rw [c'.chernDens_eq (isCInf_pullW hΦ h) hz hi, AlgChart.chernDens]
  have e₃ : c'.hess (pullW hΦ φ) (fun _ => pick φ.isLB (Φ z)) z = _ :=
    ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e₁
  rw [e₃, AlgChart.hess,
    ReciprocityTheory.L2DbarEstimates.Y.cmpa_det_comp ho hm (holo_trans hΦ c c') (e₂ ▸
      Complex.ofRealCLM.contDiff.contDiffAt.comp _ (h.contDiffAt c hz' (mem_pick _ _))), e₂,
    Complex.re_ofReal_mul, transDet]
  ring

variable [SecondCountableTopology (CxPts p σ)] [SecondCountableTopology (CxPts q σ')]

theorem chernPart_pullW (R : AnRead p σ D) (R' : AnRead q σ' D) (h : φ.IsCInf) (ε : ℤˣ) :
    (pullW hΦ φ).chernPart D ε = (φ.chernPart D ε).map Φ.symm.toMeasurableEquiv := by
  refine ext_of_cover (fun a : R.ι × R'.ι => (R'.chart a.2).e.source ∩
    (Φ.transOpenPartialHomeomorph (R.chart a.1).e).source)
    (fun a => (R'.chart a.2).e.open_source.inter (OpenPartialHomeomorph.open_source _))
    (fun z => ?_) fun a A hA hs => ?_
  · obtain ⟨a, ha⟩ := R.cover (Φ z)
    obtain ⟨b, hb⟩ := R'.cover z
    exact ⟨(a, b), hb, ha⟩
  set c := R.chart a.1
  set c' := R'.chart a.2
  have h₁ : A ⊆ c'.e.source := hs.trans inter_subset_left
  have h₂ : A ⊆ (Φ.transOpenPartialHomeomorph c.e).source := hs.trans inter_subset_right
  have hA' : MeasurableSet (Φ.symm.toMeasurableEquiv ⁻¹' A) := Φ.symm.toMeasurableEquiv.measurable hA
  have h₃ : Φ.symm.toMeasurableEquiv ⁻¹' A ⊆ c.e.source := fun y hy => by
    have : Φ (Φ.symm y) ∈ c.e.source := h₂ hy
    rwa [Φ.apply_symm_apply] at this
  rw [MeasurableEquiv.map_apply, Weight.chernPart_apply (isCInf_pullW hΦ h) ε c' hA h₁,
    Weight.chernPart_apply h ε c hA' h₃,
    ← chartMeas_apply_of_subset c'.e
      (fun y => ENNReal.ofReal ((ε : ℤ) * c'.chernDens (pullW hΦ φ) y)) hA h₁,
    chartMeas_eq c'.e (Φ.transOpenPartialHomeomorph c.e)
      (ρ' := fun y => ENNReal.ofReal ((ε : ℤ) * c.chernDens φ (Φ y))) (holo_trans hΦ c c') hA h₁ h₂
      (fun y hy => by
        rw [chernDens_pullW hΦ h c c' (h₁ hy) (h₂ hy), mul_left_comm,
          ENNReal.ofReal_mul (sq_nonneg _)]),
    chartMeas_apply_of_subset _ _ hA h₂]
  have him : Φ.transOpenPartialHomeomorph c.e '' A = c.e '' (Φ.symm.toMeasurableEquiv ⁻¹' A) := by
    rw [show Φ.symm.toMeasurableEquiv ⁻¹' A = Φ '' A from (Φ.image_eq_preimage_symm A).symm,
      image_image]
    rfl
  rw [him]
  refine lintegral_congr fun v => ?_
  rw [show Φ ((Φ.transOpenPartialHomeomorph c.e).symm v) = c.e.symm v from Φ.apply_symm_apply _]

end GlobalTheory.ChernTransfer

open GlobalTheory GlobalTheory.ChernTransfer in

theorem GlobalTheory.chernInt_transfer (k k' : Type) [CommRing k] [CommRing k'] (X Y : Scheme.{0})
    (p : X ⟶ Sp k) (q : Y ⟶ Sp k') (σ : k →+* ℂ) (σ' : k' →+* ℂ) (D : ℕ) (j : Y ⟶ X)
    (Φ : CxPts q σ' ≃ₜ CxPts p σ) (hΦ : ∀ z, (Φ z).1 = z.1 ≫ j)
    [SecondCountableTopology (CxPts p σ)] [SecondCountableTopology (CxPts q σ')]
    (hR : Nonempty (AnRead p σ D)) (hR' : Nonempty (AnRead q σ' D)) (B : LB X) (φ : Weight p σ B)
    (h : φ.IsCInf) :
    (φ.linComb (κ := PUnit) (fun _ => j) (fun _ => 1) (fun _ => Φ) (fun _ => hΦ)).IsCInf ∧
      (φ.linComb (κ := PUnit) (fun _ => j) (fun _ => 1) (fun _ => Φ) (fun _ => hΦ)).chernInt D
        Set.univ (fun _ => 1) = φ.chernInt D Set.univ (fun _ => 1) := by
  obtain ⟨R⟩ := hR
  obtain ⟨R'⟩ := hR'
  refine ⟨isCInf_pullW hΦ h, ?_⟩
  change (pullW hΦ φ).chernInt D _ _ = _
  simp only [Weight.chernInt, Measure.restrict_univ, chernPart_pullW hΦ R R' h, integral_map_equiv]
