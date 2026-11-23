import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DdcCompositionLeviFormStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvaluationHolomorphicOnFramesStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

set_option autoImplicit false

noncomputable section

open Filter Topology

namespace GlobalTheory.ShFam.SmoothPull

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem dHol_congr {F G : Pt ι p q → ℂ} {z : Pt ι p q}
    (h : (fun v => F (unflat v)) =ᶠ[𝓝 (flat z)] fun v => G (unflat v)) (ξ : Pt ι p q) :
    dHol F z ξ = dHol G z ξ := by
  simp only [dHol, dR, h.fderiv_eq]

theorem dAnti_congr {F G : Pt ι p q → ℂ} {z : Pt ι p q}
    (h : (fun v => F (unflat v)) =ᶠ[𝓝 (flat z)] fun v => G (unflat v)) (ξ : Pt ι p q) :
    dAnti F z ξ = dAnti G z ξ := by
  simp only [dAnti, dR, h.fderiv_eq]

theorem ddc_congr {f g : Pt ι p q → ℝ} {z : Pt ι p q}
    (h : (fun v => f (unflat v)) =ᶠ[𝓝 (flat z)] fun v => g (unflat v)) (ξ : Pt ι p q) :
    ddc f z ξ = ddc g z ξ := by
  unfold ddc
  rw [dHol_congr (G := fun w => dAnti (fun u => (g u : ℂ)) w ξ) ?_ ξ]
  filter_upwards [h.eventuallyEq_nhds] with v hv
  exact dAnti_congr (F := fun u => (f u : ℂ)) (G := fun u => (g u : ℂ)) (z := unflat v)
    (hv.fun_comp fun x : ℝ => (x : ℂ)) ξ

end GlobalTheory.ShFam.SmoothPull

open GlobalTheory.ShFam.SmoothPull

theorem GlobalTheory.ShFam.smoothOn_toCpt_ddc : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp) (W : Set (CxPts (genStr s.T.Z) κ.σ₀)) (φ : CxPts (genStr s.T.Z) κ.σ₀ → ℝ), IsOpen W → (manifold s.T.Z κ.σ₀).SmoothOn W φ → IsOpen {v ∈ DomFlat D.what₂.Tau j (N - j) | s.toCpt L k (unflat v) ∈ W} ∧ ContDiffOn ℝ ∞ (fun v => φ (s.toCpt L k (unflat v))) {v ∈ DomFlat D.what₂.Tau j (N - j) | s.toCpt L k (unflat v) ∈ W} ∧ ∀ (c : AlgChart (genStr s.T.Z) κ.σ₀ S.Dw.dim), ∀ z ∈ DomI D.what₂.Tau j (N - j), s.toCpt L k z ∈ W → s.toCpt L k z ∈ c.e.source → ∀ ξ, ddc (φ ∘ s.toCpt L k) z ξ = ddcForm φ c (s.toCpt L k z) (fderiv ℂ (fun v => c.e (s.toCpt L k (unflat v))) (flat z) (flat ξ)).ofLp := by
  intro D A N j S κ s L k W φ hW hφ
  have hOU : ∀ U : (gen s.T.Z).Opens, IsOpen {v ∈ DomFlat D.what₂.Tau j (N - j) |
      s.toCpt L k (unflat v) ∈ ptsIn (genStr s.T.Z) κ.σ₀ U} := fun U =>
    (GlobalTheory.T.evaluation_holomorphic_on_frames D A N j S κ s L k U 0).1
  have hD : IsOpen (DomFlat D.what₂.Tau j (N - j)) := by
    convert hOU ⊤ using 1
    ext v
    simp only [Set.mem_setOf_eq, GlobalTheory.CxPts.mem_ptsIn_top, and_true]
  have hcont : ContinuousOn (fun v => s.toCpt L k (unflat v)) (DomFlat D.what₂.Tau j (N - j)) := by
    rw [continuousOn_iff_continuous_restrict]
    refine GlobalTheory.CxPts.continuous_iff.2 fun U => ⟨?_, fun f => ?_⟩
    · have := (hOU U).preimage (continuous_subtype_val (p := (· ∈ DomFlat D.what₂.Tau j (N - j))))
      convert this using 1
      ext v
      simp only [Set.mem_preimage, Set.restrict_apply, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨v.2, h⟩, fun h => h.2⟩
    · intro v hv
      have hm : (v : D.what₂.Tau × Fin j × Fin (N - j) → ℂ) ∈ {v ∈ DomFlat D.what₂.Tau j (N - j) |
          s.toCpt L k (unflat v) ∈ ptsIn (genStr s.T.Z) κ.σ₀ U} := ⟨v.2, hv⟩
      have hca := ((GlobalTheory.T.evaluation_holomorphic_on_frames D A N j S κ s L k U f).2.differentiableAt ((hOU U).mem_nhds hm)).continuousAt
      exact (hca.comp continuous_subtype_val.continuousAt).continuousWithinAt
  have hOc : ∀ c : AlgChart (genStr s.T.Z) κ.σ₀ S.Dw.dim, IsOpen {v ∈ DomFlat D.what₂.Tau j (N - j) |
      s.toCpt L k (unflat v) ∈ c.e.source} := fun c => hcont.isOpen_inter_preimage hD c.e.open_source
  have hdiff : ∀ c : AlgChart (genStr s.T.Z) κ.σ₀ S.Dw.dim, DifferentiableOn ℂ (fun v => c.e (s.toCpt L k (unflat v)))
      {v ∈ DomFlat D.what₂.Tau j (N - j) | s.toCpt L k (unflat v) ∈ c.e.source} := fun c =>
    differentiableOn_euclidean.2 fun a => ((GlobalTheory.T.evaluation_holomorphic_on_frames D A N j S κ s L k c.U (c.x a)).2.mono
      fun v hv => ⟨hv.1, c.source_subset hv.2⟩).congr fun v hv => c.apply_eq _ hv.2 a
  refine ⟨hcont.isOpen_inter_preimage hD hW, fun v hv => ?_, fun c z hz hzW hzc ξ => ?_⟩
  · obtain ⟨c, hc⟩ := (manifold s.T.Z κ.σ₀).cover (s.toCpt L k (unflat v))
    change AlgChart (genStr s.T.Z) κ.σ₀ S.Dw.dim at c
    change s.toCpt L k (unflat v) ∈ c.e.source at hc
    have hv' : v ∈ {v ∈ DomFlat D.what₂.Tau j (N - j) | s.toCpt L k (unflat v) ∈ c.e.source} := ⟨hv.1, hc⟩
    have h1 : ContDiffOn ℂ ∞ (fun v => c.e (s.toCpt L k (unflat v)))
        {v ∈ DomFlat D.what₂.Tau j (N - j) | s.toCpt L k (unflat v) ∈ c.e.source} := GlobalTheory.SCV.contDiffOn_of_differentiableOn (hOc c) (hdiff c) ∞
    have hF : ContDiffAt ℝ ∞ (fun v => c.e (s.toCpt L k (unflat v))) v :=
      (h1.restrict_scalars ℝ).contDiffAt ((hOc c).mem_nhds hv')
    have hφc : ContDiffAt ℝ ∞ (φ ∘ c.e.symm) (c.e (s.toCpt L k (unflat v))) :=
      (hφ.chart hW c).contDiffAt ((GlobalTheory.ChartGlue.isOpen_over c.e hW).mem_nhds (GlobalTheory.ChartGlue.mem_over c.e hc hv.2))
    refine ((hφc.comp v hF).congr_of_eventuallyEq ?_).contDiffWithinAt
    filter_upwards [(hOc c).mem_nhds hv'] with w hw
    simp only [Function.comp_apply, c.e.left_inv hw.2]
  · have hv' : flat z ∈ {v ∈ DomFlat D.what₂.Tau j (N - j) | s.toCpt L k (unflat v) ∈ c.e.source} := ⟨hz, hzc⟩
    have hev : ∀ᶠ v in 𝓝 (flat z), DifferentiableAt ℂ (fun w => c.e (s.toCpt L k (unflat w))) v :=
      eventually_of_mem ((hOc c).mem_nhds hv') fun v hv => (hdiff c).differentiableAt ((hOc c).mem_nhds hv)
    have h2 : ContDiffAt ℝ 2 (φ ∘ c.e.symm) (c.e (s.toCpt L k z)) := hφ.contDiffAt_two hW hzc hzW
    have chain := GlobalTheory.T.ddc_composition_levi_form D.what₂.Tau j (N - j) S.Dw.dim (fun z => c.e (s.toCpt L k z)) (φ ∘ c.e.symm) z hev h2 ξ
    rw [ddc_congr (g := (φ ∘ c.e.symm) ∘ fun z => c.e (s.toCpt L k z)) ?_ ξ, chain]
    · rfl
    · filter_upwards [(hOc c).mem_nhds hv'] with w hw
      simp only [Function.comp_apply, c.e.left_inv hw.2]
