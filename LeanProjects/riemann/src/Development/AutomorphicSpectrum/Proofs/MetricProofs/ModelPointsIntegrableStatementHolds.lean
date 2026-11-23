import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsModelPtsIntegrable
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalHolomorphicSectionOfPotentialStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralModelFormulaStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MeasureTheory Filter Topology ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
  GroundTheory.Heights₂.Heights.LowerBoundFree

section Transfer

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem modelChart_injOn (χ φ : OpenPartialHomeomorph X (Fin e → ℂ)) :
    Set.InjOn (φ ∘ χ.symm) (χ.target ∩ χ.symm ⁻¹' φ.source) := by
  intro u hu u' hu' h
  have h1 : χ.symm u = χ.symm u' := φ.injOn hu.2 hu'.2 h
  have h2 := congrArg χ h1
  rwa [χ.right_inv hu.1, χ.right_inv hu'.1] at h2

theorem modelChart_null (χ φ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hσ : AnalyticOnNhd ℂ (φ ∘ χ.symm) (χ.target ∩ χ.symm ⁻¹' φ.source)) (E : Set X)
    (hE : volume (χ.target ∩ χ.symm ⁻¹' E) = 0) :
    volume (φ.target ∩ φ.symm ⁻¹' (E ∩ χ.source)) = 0 := by
  have hd : DifferentiableOn ℝ (φ ∘ χ.symm)
      (χ.target ∩ χ.symm ⁻¹' φ.source ∩ χ.symm ⁻¹' E) :=
    (hσ.differentiableOn.restrictScalars ℝ).mono Set.inter_subset_left
  have h0 : volume (χ.target ∩ χ.symm ⁻¹' φ.source ∩ χ.symm ⁻¹' E) = 0 :=
    measure_mono_null (t := χ.target ∩ χ.symm ⁻¹' E) (fun u hu => ⟨hu.1.1, hu.2⟩) hE
  have himg := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hd h0
  refine measure_mono_null ?_ himg
  rintro y ⟨hy, hyE, hyχ⟩
  refine ⟨χ (φ.symm y), ⟨⟨χ.map_source hyχ, ?_⟩, ?_⟩, ?_⟩
  · show χ.symm (χ (φ.symm y)) ∈ φ.source
    rw [χ.left_inv hyχ]; exact φ.map_target hy
  · show χ.symm (χ (φ.symm y)) ∈ E
    rw [χ.left_inv hyχ]; exact hyE
  · simp [χ.left_inv hyχ, φ.right_inv hy]

theorem modelChart_integrableOn (χ φ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hσ : AnalyticOnNhd ℂ (φ ∘ χ.symm) (χ.target ∩ χ.symm ⁻¹' φ.source)) (v : X → ℝ)
    (hv : ∀ Q ⊆ χ.target, IsCompact Q → IntegrableOn (fun y => v (χ.symm y)) Q)
    {Q : Set (Fin e → ℂ)} (hQ : IsCompact Q) (hQs : Q ⊆ φ.target ∩ φ.symm ⁻¹' χ.source) :
    IntegrableOn (fun y => v (φ.symm y)) Q := by
  have hSo : IsOpen (χ.target ∩ χ.symm ⁻¹' φ.source) :=
    χ.isOpen_inter_preimage_symm φ.open_source
  have hρc : ContinuousOn (χ ∘ φ.symm) Q :=
    χ.continuousOn.comp (φ.continuousOn_symm.mono fun y hy => (hQs hy).1) fun y hy => (hQs hy).2
  have hQ' : IsCompact ((χ ∘ φ.symm) '' Q) := hQ.image_of_continuousOn hρc
  have hQS : (χ ∘ φ.symm) '' Q ⊆ χ.target ∩ χ.symm ⁻¹' φ.source := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨χ.map_source (hQs hy).2, ?_⟩
    show χ.symm (χ (φ.symm y)) ∈ φ.source
    rw [χ.left_inv (hQs hy).2]; exact φ.map_target (hQs hy).1
  have himg : (φ ∘ χ.symm) '' ((χ ∘ φ.symm) '' Q) = Q := by
    rw [Set.image_image]
    refine Set.ext fun y => ⟨?_, fun hy => ⟨y, hy, ?_⟩⟩
    · rintro ⟨y', hy', rfl⟩
      simpa [χ.left_inv (hQs hy').2, φ.right_inv (hQs hy').1] using hy'
    · simp [χ.left_inv (hQs hy).2, φ.right_inv (hQs hy).1]
  have hσR : AnalyticOnNhd ℝ (φ ∘ χ.symm) (χ.target ∩ χ.symm ⁻¹' φ.source) :=
    hσ.restrictScalars
  have hder : ∀ u ∈ (χ ∘ φ.symm) '' Q,
      HasFDerivWithinAt (φ ∘ χ.symm) (fderiv ℝ (φ ∘ χ.symm) u) ((χ ∘ φ.symm) '' Q) u :=
    fun u hu => ((hσR u (hQS hu)).differentiableAt.hasFDerivAt).hasFDerivWithinAt
  have hinj : Set.InjOn (φ ∘ χ.symm) ((χ ∘ φ.symm) '' Q) := (modelChart_injOn χ φ).mono hQS
  have hcont : ContinuousOn (fun u => |(fderiv ℝ (φ ∘ χ.symm) u).det|) ((χ ∘ φ.symm) '' Q) := by
    have h1 : ContinuousOn (fderiv ℝ (φ ∘ χ.symm)) (χ.target ∩ χ.symm ⁻¹' φ.source) :=
      (hσR.fderiv).continuousOn
    exact (ContinuousLinearMap.continuous_det.comp_continuousOn (h1.mono hQS)).abs
  have hint := (hv _ (fun u hu => (hQS hu).1) hQ').continuousOn_mul hcont hQ'
  rw [← himg]
  refine (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hQ'.measurableSet hder
    hinj _).2 ?_
  refine hint.congr_fun (fun u hu => ?_) hQ'.measurableSet
  have hu := hQS hu
  simp only [smul_eq_mul, Function.comp_apply, φ.left_inv hu.2]

theorem modelChart_integrableOn_cover {n : ℕ} (χ : Fin n → OpenPartialHomeomorph X (Fin e → ℂ))
    (φ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hσ : ∀ k, AnalyticOnNhd ℂ (φ ∘ (χ k).symm) ((χ k).target ∩ (χ k).symm ⁻¹' φ.source))
    (hcov : ∀ x, ∃ k, x ∈ (χ k).source) (v : X → ℝ)
    (hv : ∀ k, ∀ Q ⊆ (χ k).target, IsCompact Q → IntegrableOn (fun y => v ((χ k).symm y)) Q) :
    LocallyIntegrableOn (fun y => v (φ.symm y)) φ.target := by
  intro y hy
  obtain ⟨k, hk⟩ := hcov (φ.symm y)
  have hWo : IsOpen (φ.target ∩ φ.symm ⁻¹' (χ k).source) :=
    φ.isOpen_inter_preimage_symm (χ k).open_source
  obtain ⟨Q, hQn, hQs, hQc⟩ := local_compact_nhds (hWo.mem_nhds ⟨hy, hk⟩)
  exact ⟨Q, mem_nhdsWithin_of_mem_nhds hQn, modelChart_integrableOn (χ k) φ (hσ k) v (hv k) hQc hQs⟩

theorem modelChart_null_cover {n : ℕ} (χ : Fin n → OpenPartialHomeomorph X (Fin e → ℂ))
    (φ : OpenPartialHomeomorph X (Fin e → ℂ))
    (hσ : ∀ k, AnalyticOnNhd ℂ (φ ∘ (χ k).symm) ((χ k).target ∩ (χ k).symm ⁻¹' φ.source))
    (hcov : ∀ x, ∃ k, x ∈ (χ k).source) (E : Set X)
    (hE : ∀ k, volume ((χ k).target ∩ (χ k).symm ⁻¹' E) = 0) :
    volume (φ.target ∩ φ.symm ⁻¹' E) = 0 := by
  refine measure_mono_null (t := ⋃ k, φ.target ∩ φ.symm ⁻¹' (E ∩ (χ k).source)) ?_
    (measure_iUnion_null fun k => modelChart_null (χ k) φ (hσ k) E (hE k))
  rintro y ⟨hy, hyE⟩
  obtain ⟨k, hk⟩ := hcov (φ.symm y)
  exact Set.mem_iUnion.2 ⟨k, hy, hyE, hk⟩

end Transfer

theorem modelPtsIntegrable : ModelPtsIntegrable.Statement := by
  intro K _ ι _ P e M n ψ L c N E v g hV hL hN hψ hcov hE hv hg Ψ hΨ
  obtain ⟨Φ₀, hΦ₀, hloc⟩ := GlobalTheory.T.local_holomorphic_section_of_potential K ι P e M L hL
  have hΦ : IsPotential M.atlas (Φ₀.rsmul c) := isPotentialRsmul M.atlas c Φ₀ hΦ₀
  have hli : ∀ j, LocallyIntegrableOn (fun y => v ((M.atlas.chart j).symm y))
      (M.atlas.chart j).target := fun j =>
    modelChart_integrableOn_cover ψ (M.atlas.chart j) (fun k => (hψ k j).2) hcov v hv
  have hint : ∀ j, ∀ Q ⊆ (M.atlas.chart j).target, IsCompact Q →
      IntegrableOn (fun y => v ((M.atlas.chart j).symm y)) Q := fun j Q hQ hQc =>
    (hli j).integrableOn_compact_subset hQ hQc
  have hnull : ∀ j, volume ((M.atlas.chart j).target ∩
      (M.atlas.chart j).symm ⁻¹' ((Set.univ : Set M.Xc)ᶜ ∪ E)) = 0 := fun j => by
    simpa using modelChart_null_cover ψ (M.atlas.chart j) (fun k => (hψ k j).2) hcov E hE
  have hMI : MIntegrable M.atlas (fun _ : Fin e => Φ₀.rsmul c) v := fun j Q hQ hQc =>
    (hint j Q hQ hQc).mul_continuousOn
      ((locDensCont M.atlas _ (fun _ => hΦ) j).mono hQ) hQc
  refine ((GlobalTheory.T.mixed_integral_model_formula K ι P e M Ψ Set.univ E N (fun _ => c) (fun _ => L)
    (fun _ => Φ₀.rsmul c) g v hV hΨ isOpen_univ hnull hN ?_ ?_ ?_ ?_).2.2 hMI).1
  · exact fun _ x j => (hΦ.1 x j).mono fun y hy => ⟨hy.1, hy.2.1⟩
  · intro _ x y₀ hy₀
    obtain ⟨U, hUo, hyU, hUs, s, hs, hsh, G, hG, hGe⟩ := hloc x y₀ hy₀
    refine ⟨U, hUo, hyU, hUs, s, hs, hsh, fun z => (c : ℂ) * G z, holoOn_mul M.atlas hG c,
      fun y' hy' => ?_⟩
    have h1 : Φ₀.φ x y' - Real.log (L.h (s y')) = (G y').re := hGe y' hy'
    show c * Φ₀.φ x y' - c * Real.log (L.h (s y')) = ((c : ℂ) * G y').re
    rw [Complex.re_ofReal_mul, ← h1]
    ring
  · exact fun z hz hzN _ hzE => hg z hz hzN hzE
  · exact fun j => (hli j).aestronglyMeasurable

end GlobalTheory.CompanionTheory.Ar.Giv
