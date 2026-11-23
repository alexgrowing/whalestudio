import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrableRegularVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnMixedChernFormDensityInChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureComplOpenGenericPStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureChartApplyStatement

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory Metric
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixLogSec

theorem exists_integrableOn {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {D : ℕ} [SecondCountableTopology (CxPts p σ)] (hσ : Function.Injective σ) (L : Fin D → MLine p σ)
    (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (ε : ℤˣ) (c : AlgChart p σ D)
    {y : CxPts p σ} (hy : y ∈ c.e.source) :
    ∃ O ∈ 𝓝 y, IntegrableOn (M.logSec s) (ptsIn p σ (nonzeroLocus s) ∩ O) (part L ε) := by
  have : IsDomain k := hσ.isDomain σ
  set i := pick M.φ.isLB y
  have hi : y ∈ ptsIn p σ (M.B.U i) := mem_pick _ y
  have hT' := (isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (M.B.U i))).mem_nhds (mem_over c.e hy hi)
  have hd : ∀ᶠ v in 𝓝 (c.e y), DifferentiableAt ℂ (ev p σ _ (s.f i) ∘ c.e.symm) v :=
    (c.holo _ _).eventually_differentiableAt hT'
  have hfr : ∃ᶠ v in 𝓝 (c.e y), (ev p σ _ (s.f i) ∘ c.e.symm) v ≠ 0 := by
    have h := Measure.dense_of_ae (SemiPosBir.ae_mem hσ c (U := nonzeroLocus s) ⟨_, hs⟩)
    have h₁ := mem_closure_iff_frequently.1 (h (c.e y))
    refine (h₁.and_eventually hT').mono ?_
    rintro v ⟨h₂, h₃⟩
    exact (secVal_ne_zero_iff s h₃.2).2 (h₂ h₃.1)
  obtain ⟨δ, hδ, -, hint⟩ := exists_integrableOn_log_norm_of_frequently_ne_zero volume hd hfr
  obtain ⟨η, hη, hηs⟩ := nhds_basis_closedBall.mem_iff.1 (inter_mem hT' (ball_mem_nhds _ hδ))
  have hcont : ContinuousOn (fun v => dens L c (c.e.symm v)) c.e.target :=
    (GlobalTheory.T.continuousOn_mixedChernFormDensityInChart k X p σ D L c).comp c.e.continuousOn_symm c.e.mapsTo_symm
  obtain ⟨C, hC⟩ := (isCompact_closedBall (c.e y) η).exists_bound_of_continuousOn
    (hcont.mono fun v hv => (hηs hv).1.1)
  set O := c.e.source ∩ c.e ⁻¹' ball (c.e y) η
  have hO : IsOpen O := c.e.continuousOn.isOpen_inter_preimage c.e.open_source isOpen_ball
  set S := ptsIn p σ (nonzeroLocus s) ∩ O
  have hS : IsOpen S := (isOpen_ptsIn _).inter hO
  have hSs : S ⊆ c.e.source := fun z hz => hz.2.1
  have him : c.e '' S ⊆ closedBall (c.e y) η := by
    rintro _ ⟨z, hz, rfl⟩
    exact ball_subset_closedBall hz.2.2
  have hSi (z) (hz : z ∈ S) : z ∈ ptsIn p σ (M.B.U i) := by
    have := (hηs (him (mem_image_of_mem _ hz))).1.2
    rwa [mem_preimage, c.e.left_inv (hSs hz)] at this
  have hne (z) (hz : z ∈ S) : ev p σ _ (s.f i) z ≠ 0 := (secVal_ne_zero_iff s (hSi z hz)).2 hz.1
  have heq (z) (hz : z ∈ S) : M.logSec s z = Real.log ‖ev p σ _ (s.f i) z‖ - M.φ.φ i z / 2 := by
    rw [MLine.logSec, M.φ.nsq_eq (secVal_mem s) (hSi z hz), secVal_apply,
      Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 (hne z hz))) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp]
    push_cast
    ring
  have hm := measurableSet_image c.e hS.measurableSet hSs
  refine ⟨O, hO.mem_nhds ⟨hy, mem_ball_self hη⟩, LogNormInt.integrableOn_of_chart c.e
    (fun A hA hAs => GlobalTheory.T.mixedChernFormSignedPartMeasure_chart_apply k X p σ D L ε c A hA hAs) hS.measurableSet hSs
    (C := ENNReal.ofReal C) ENNReal.ofReal_ne_top (fun v hv => ENNReal.ofReal_le_ofReal ?_) ?_ ?_⟩
  · have h := hC v (him hv)
    rw [Real.norm_eq_abs, abs_le] at h
    rcases Int.units_eq_one_or ε with rfl | rfl
    · simpa using h.2
    · simpa [neg_le] using h.1
  · refine ContinuousOn.congr (fun z hz => ContinuousAt.continuousWithinAt ?_) heq
    exact ((((continuousOn_ev (s.f i)).continuousAt ((isOpen_ptsIn _).mem_nhds (hSi z hz))).norm.log
      (norm_ne_zero_iff.2 (hne z hz))).sub ((M.cInf i z (hSi z hz)).continuousAt.div_const 2))
  · have hsub : c.e '' S ⊆ ball (c.e y) δ := fun v hv => (hηs (him hv)).2
    have h₁ : IntegrableOn (fun v => (M.φ.φ i ∘ c.e.symm) v / 2) (c.e '' S) :=
      (((((contDiffOn_chart (M.cInf i) c).continuousOn.mono fun v hv => (hηs hv).1).div_const
        2).integrableOn_compact (isCompact_closedBall _ _)).mono_set him)
    refine ((hint.mono_set hsub).sub h₁).congr ?_
    filter_upwards [ae_restrict_mem hm] with v hv'
    obtain ⟨z, hz, rfl⟩ := hv'
    simp only [Function.comp_apply, Pi.sub_apply, c.e.left_inv (hSs hz)]
    exact (heq z hz).symm

theorem intg_logSec : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ (L : Fin D → MLine p σ) (M : MLine p σ) (s : M.B.Sec), genericPoint X ∈ nonzeroLocus s → Intg L (M.logSec s) := by
  intro F _ X _ _ p σ D hp hsm L M s hs
  have := CxPts.compactSpace σ hp
  have := CxPts.secondCountableTopology_of_isProjOver σ hp
  have key (ε : ℤˣ) : Integrable (M.logSec s) (part L ε) := by
    have h (y : CxPts p σ) : ∃ O ∈ 𝓝 y, IntegrableOn (M.logSec s) (ptsIn p σ (nonzeroLocus s) ∩ O) (part L ε) :=
      have ⟨c, hc⟩ := AlgChart.exists_mem_source (D := D) y
      exists_integrableOn σ.injective L M s hs ε c hc
    choose O hO hint using h
    obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover O fun y _ => hO y
    have h₁ : IntegrableOn (M.logSec s) (ptsIn p σ (nonzeroLocus s)) (part L ε) := by
      refine ((integrableOn_finset_iUnion (s := t)).2 fun y _ => hint y).mono_set fun z hz => ?_
      obtain ⟨y, hy, hz'⟩ := mem_iUnion₂.1 (ht (mem_univ z))
      exact mem_iUnion₂.2 ⟨y, hy, hz, hz'⟩
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (s := ptsIn p σ (nonzeroLocus s))
      (mem_ae_iff.2 (GlobalTheory.T.mixedChernFormSignedPartMeasure_compl_open_genericPoint_eq_zero F X p σ σ.injective hp D L ε _ hs))] at h₁
  exact ⟨key 1, key (-1)⟩

end GlobalTheory.MixLogSec
