import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMajorantStabCompact
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallAutomorphismInverseExists
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityOfBallPotentialStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityChangeOfVariablesStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas

open scoped Pointwise NNReal
open Measure

section Abstract

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]

def translHomeo {π : G → X} (hs : Function.Surjective π) {T : G → X → X} (hT : ∀ a, Continuous (T a))
    (hπ : ∀ a b, π (a * b) = T a (π b)) (a : G) : X ≃ₜ X where
  toFun := T a
  invFun := T a⁻¹
  left_inv x := by
    obtain ⟨b, rfl⟩ := hs x
    rw [← hπ, ← hπ, inv_mul_cancel_left]
  right_inv x := by
    obtain ⟨b, rfl⟩ := hs x
    rw [← hπ, ← hπ, mul_inv_cancel_left]
  continuous_toFun := hT a
  continuous_invFun := hT a⁻¹

theorem isOpenMap_orbit {π : G → X} (hc : Continuous π) (hs : Function.Surjective π) {T : G → X → X}
    (hT : ∀ a, Continuous (T a)) (hπ : ∀ a b, π (a * b) = T a (π b)) : IsOpenMap π := by
  have key : ∀ W ∈ 𝓝 (1 : G), π '' W ∈ 𝓝 (π 1) := by
    intro W hW
    obtain ⟨W', hW', hWW⟩ : ∃ V ∈ 𝓝 (1 : G), ∀ v ∈ V, ∀ w ∈ V, v⁻¹ * w ∈ W := by
      have hcont : ContinuousAt (fun p : G × G => p.1⁻¹ * p.2) ((1 : G), (1 : G)) := by fun_prop
      have h1 : (fun p : G × G => p.1⁻¹ * p.2) ⁻¹' W ∈ 𝓝 ((1 : G), (1 : G)) :=
        hcont (by simpa using hW)
      rw [nhds_prod_eq] at h1
      obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.mp h1
      exact ⟨A ∩ B, inter_mem hA hB, fun v hv w hw => hAB (Set.mk_mem_prod hv.1 hw.2)⟩
    obtain ⟨V, hV, hVW, hVc⟩ := local_compact_nhds hW'
    have hnb : ∀ x : G, (fun y => x * y) '' V ∈ 𝓝 x := by
      intro x
      have := (Homeomorph.mulLeft x).isOpenMap.image_mem_nhds hV
      simpa using this
    obtain ⟨s, hsc, hsu⟩ := TopologicalSpace.countable_cover_nhds hnb
    have hcl : ∀ g : s, IsClosed (π '' ((fun y => (g : G) * y) '' V)) := fun g =>
      ((hVc.image (continuous_const.mul continuous_id)).image hc).isClosed
    have hU : ⋃ g : s, π '' ((fun y => (g : G) * y) '' V) = Set.univ := by
      rw [Set.eq_univ_iff_forall]
      intro x
      obtain ⟨b, rfl⟩ := hs x
      have : b ∈ ⋃ x ∈ s, (fun y => x * y) '' V := hsu ▸ Set.mem_univ b
      simp only [Set.mem_iUnion] at this ⊢
      obtain ⟨g, hg, hb⟩ := this
      exact ⟨⟨g, hg⟩, b, hb, rfl⟩
    haveI : Countable s := hsc.to_subtype
    haveI : Nonempty X := ⟨π 1⟩
    obtain ⟨g, hg⟩ := nonempty_interior_of_iUnion_of_closed hcl hU
    obtain ⟨y, hy⟩ := hg
    obtain ⟨_, ⟨v, hv, rfl⟩, rfl⟩ := interior_subset hy
    set c : G := (g : G) * v with hcdef
    have hnb2 : π '' ((fun y => (g : G) * y) '' V) ∈ 𝓝 (π c) := mem_interior_iff_mem_nhds.mp hy
    have h3 := (translHomeo hs hT hπ c⁻¹).isOpenMap.image_mem_nhds hnb2
    have h4 : (translHomeo hs hT hπ c⁻¹) (π c) = π 1 := by
      show T c⁻¹ (π c) = π 1
      rw [← hπ, inv_mul_cancel]
    rw [h4] at h3
    refine Filter.mem_of_superset h3 ?_
    rintro _ ⟨_, ⟨_, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
    refine ⟨v⁻¹ * w, hWW v (hVW hv) w (hVW hw), ?_⟩
    show π (v⁻¹ * w) = T c⁻¹ (π ((g : G) * w))
    rw [← hπ]
    congr 1
    simp [hcdef, mul_assoc]
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨b, hb, rfl⟩
  have h1 : (fun y => b⁻¹ * y) '' U ∈ 𝓝 (1 : G) := by
    have := (Homeomorph.mulLeft b⁻¹).isOpenMap.image_mem_nhds (hU.mem_nhds hb)
    simpa using this
  have h2 := (translHomeo hs hT hπ b).isOpenMap.image_mem_nhds (key _ h1)
  have h3 : (translHomeo hs hT hπ b) (π 1) = π b := by
    show T b (π 1) = π b
    rw [← hπ, mul_one]
  rw [h3] at h2
  refine Filter.mem_of_superset h2 ?_
  rintro _ ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
  refine ⟨u, hu, ?_⟩
  show π u = T b (π (b⁻¹ * u))
  rw [← hπ, mul_inv_cancel_left]

theorem continuous_action {π : G → X} (hc : Continuous π) (hs : Function.Surjective π) {T : G → X → X}
    (hT : ∀ a, Continuous (T a)) (hπ : ∀ a b, π (a * b) = T a (π b)) :
    Continuous fun p : G × X => T p.1 p.2 := by
  have hop : IsOpenMap (Prod.map (id : G → G) π) := IsOpenMap.id.prodMap (isOpenMap_orbit hc hs hT hπ)
  have hq : Topology.IsQuotientMap (Prod.map (id : G → G) π) :=
    hop.isQuotientMap (continuous_id.prodMap hc) (Function.surjective_id.prodMap hs)
  rw [hq.continuous_iff]
  have : ((fun p : G × X => T p.1 p.2) ∘ Prod.map (id : G → G) π) = fun p : G × G => π (p.1 * p.2) := by
    funext p
    simp [hπ]
  rw [this]
  exact hc.comp (continuous_fst.mul continuous_snd)

theorem isCompact_preimage_orbit {π : G → X} (hc : Continuous π) (hs : Function.Surjective π) {T : G → X → X}
    (hT : ∀ a, Continuous (T a)) (hπ : ∀ a b, π (a * b) = T a (π b)) {K : Set G} (hK : IsCompact K)
    (hf : ∀ a b, π a = π b → a⁻¹ * b ∈ K) {C : Set X} (hC : IsCompact C) : IsCompact (π ⁻¹' C) := by
  have hop := isOpenMap_orbit hc hs hT hπ
  obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds (1 : G)
  have hnb : ∀ c ∈ C, ∃ g : G, π '' ((fun y => g * y) '' V) ∈ 𝓝 c := by
    intro c _
    obtain ⟨g, rfl⟩ := hs c
    refine ⟨g, hop.image_mem_nhds ?_⟩
    have := (Homeomorph.mulLeft g).isOpenMap.image_mem_nhds hV
    simpa using this
  choose! γ hγ using hnb
  obtain ⟨t, htC, htU⟩ := hC.elim_nhds_subcover _ hγ
  have hcomp : IsCompact (⋃ c ∈ t, ((fun y => γ c * y) '' V) * K) :=
    t.isCompact_biUnion fun c _ => (hVc.image (continuous_const.mul continuous_id)).mul hK
  refine hcomp.of_isClosed_subset (hC.isClosed.preimage hc) ?_
  intro a ha
  obtain ⟨c, hct, b, hb, hba⟩ : ∃ c ∈ t, ∃ b ∈ (fun y => γ c * y) '' V, π b = π a := by
    have := htU ha
    simp only [Set.mem_iUnion] at this
    obtain ⟨c, hc', b, hb, hba⟩ := this
    exact ⟨c, hc', b, hb, hba⟩
  simp only [Set.mem_iUnion]
  exact ⟨c, hct, Set.mem_mul.mpr ⟨b, hb, b⁻¹ * a, hf _ _ hba, by group⟩⟩

end Abstract

section Measure

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

theorem map_haar_eq_smul {π : G → X} (hc : Continuous π) (hs : Function.Surjective π) {T : G → X → X}
    (hT : ∀ a, Continuous (T a)) (hπ : ∀ a b, π (a * b) = T a (π b)) {K : Set G} (hK : IsCompact K)
    (hf : ∀ a b, π a = π b → a⁻¹ * b ∈ K) (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure X)
    [IsFiniteMeasureOnCompacts ν] (hν : ∀ a, ν.map (T a) = ν) (h0 : ν ≠ 0) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ.map π = c • ν := by
  have hm : Measurable π := hc.measurable
  have hTm : ∀ a, Measurable (T a) := fun a => (hT a).measurable
  set ν' : Measure X := μ.map π with hν'def
  haveI : IsFiniteMeasureOnCompacts ν' := ⟨fun C hC => by
    rw [hν'def, Measure.map_apply hm hC.measurableSet]
    exact (isCompact_preimage_orbit hc hs hT hπ hK hf hC).measure_lt_top⟩
  haveI : SigmaFinite ν' := inferInstance
  haveI : SigmaFinite ν := inferInstance
  have hν' : ∀ a, ν'.map (T a) = ν' := by
    intro a
    rw [hν'def, Measure.map_map (hTm a) hm]
    have h1 : T a ∘ π = π ∘ (fun y => a * y) := by
      funext b
      simp [hπ]
    rw [h1, ← Measure.map_map hm (measurable_const_mul a), map_mul_left_eq_self]
  have hpres : ∀ a, MeasurePreserving (T a) ν' ν' := fun a => ⟨hTm a, hν' a⟩
  have hac : ν ≪ ν' := by
    refine Measure.AbsolutelyContinuous.mk fun N hN h0' => ?_
    have hnull : μ (π ⁻¹' N) = 0 := by rwa [hν'def, Measure.map_apply hm hN] at h0'
    have hΘ : Measurable (fun p : G × X => T p.1 p.2) := (continuous_action hc hs hT hπ).measurable
    have hP : MeasurableSet ((fun p : G × X => T p.1 p.2) ⁻¹' N) := hΘ hN
    have e1 : (μ.prod ν) ((fun p : G × X => T p.1 p.2) ⁻¹' N) = ν N * μ Set.univ := by
      rw [Measure.prod_apply hP]
      have h2 : ∀ a, ν (Prod.mk a ⁻¹' ((fun p : G × X => T p.1 p.2) ⁻¹' N)) = ν N := by
        intro a
        have h3 : Prod.mk a ⁻¹' ((fun p : G × X => T p.1 p.2) ⁻¹' N) = T a ⁻¹' N := rfl
        rw [h3, ← Measure.map_apply (hTm a) hN, hν]
      simp [h2]
    have e2 : (μ.prod ν) ((fun p : G × X => T p.1 p.2) ⁻¹' N) = 0 := by
      rw [Measure.prod_apply_symm hP]
      have h2 : ∀ x, μ ((fun a => (a, x)) ⁻¹' ((fun p : G × X => T p.1 p.2) ⁻¹' N)) = 0 := by
        intro x
        obtain ⟨b, rfl⟩ := hs x
        have h3 : ((fun a => (a, π b)) ⁻¹' ((fun p : G × X => T p.1 p.2) ⁻¹' N)) =
            (fun a => a * b) ⁻¹' (π ⁻¹' N) := by
          ext a
          simp [hπ]
        rw [h3]
        exact (quasiMeasurePreserving_mul_right μ b).preimage_null hnull
      simp [h2]
    rw [e2] at e1
    have hu : μ Set.univ ≠ 0 := (isOpen_univ.measure_pos μ Set.univ_nonempty).ne'
    exact (mul_eq_zero.mp e1.symm).resolve_right hu
  set f : X → ℝ≥0∞ := ν.rnDeriv ν' with hfdef
  have hfm : Measurable f := Measure.measurable_rnDeriv ν ν'
  have hwd : ν'.withDensity f = ν := Measure.withDensity_rnDeriv_eq ν ν' hac
  have hinv : ∀ b, f ∘ T b =ᵐ[ν'] f := by
    intro b
    have h1 : ν'.withDensity (f ∘ T b) = ν'.withDensity f := by
      refine Measure.ext fun S hS => ?_
      rw [withDensity_apply _ hS, hwd]
      have hS' : MeasurableSet (T b⁻¹ ⁻¹' S) := hTm _ hS
      have e : T b ⁻¹' (T b⁻¹ ⁻¹' S) = S := by
        ext x
        obtain ⟨y, rfl⟩ := hs x
        simp [← hπ]
      have h2 := (hpres b).setLIntegral_comp_preimage hS' hfm
      rw [e] at h2
      calc ∫⁻ a in S, (f ∘ T b) a ∂ν' = ∫⁻ y in T b⁻¹ ⁻¹' S, f y ∂ν' := h2
        _ = ν'.withDensity f (T b⁻¹ ⁻¹' S) := (withDensity_apply _ hS').symm
        _ = ν (T b⁻¹ ⁻¹' S) := by rw [hwd]
        _ = ν S := by rw [← Measure.map_apply (hTm _) hS, hν]
    exact (withDensity_eq_iff_of_sigmaFinite (hfm.comp (hTm b)).aemeasurable hfm.aemeasurable).mp h1
  set lam : Measure G := μ.withDensity (f ∘ π) with hlam
  have hlamπ : lam.map π = ν := by
    refine Measure.ext fun S hS => ?_
    rw [Measure.map_apply hm hS, hlam, withDensity_apply _ (hm hS), ← hwd, withDensity_apply _ hS,
      hν'def, setLIntegral_map hS hfm hm]
    rfl
  haveI : IsMulLeftInvariant lam := ⟨fun a => by
    refine Measure.ext fun B hB => ?_
    rw [Measure.map_apply (measurable_const_mul a) hB, hlam,
      withDensity_apply _ (measurable_const_mul a hB), withDensity_apply _ hB]
    have hg := measurePreserving_mul_left μ a
    have hmeas : Measurable fun y => f (π (a⁻¹ * y)) := hfm.comp (hm.comp (measurable_const_mul _))
    have h1 := hg.setLIntegral_comp_preimage hB hmeas
    simp only [inv_mul_cancel_left] at h1
    have hae : (fun y => f (π (a⁻¹ * y))) =ᵐ[μ] f ∘ π := by
      have h2 := ae_of_ae_map hm.aemeasurable (hinv a⁻¹)
      filter_upwards [h2] with y hy
      simpa [hπ] using hy
    exact h1.trans (lintegral_congr_ae (ae_restrict_of_ae hae))⟩
  haveI : IsFiniteMeasureOnCompacts lam := ⟨fun C hC => by
    have hC' : IsCompact (π '' C) := hC.image hc
    calc lam C ≤ lam (π ⁻¹' (π '' C)) := measure_mono (Set.subset_preimage_image π C)
      _ = ν (π '' C) := by rw [← hlamπ, Measure.map_apply hm hC'.measurableSet]
      _ < ⊤ := hC'.measure_lt_top⟩
  have hsm := isMulLeftInvariant_eq_smul lam μ
  set c : ℝ≥0 := haarScalarFactor lam μ with hcdef
  have hνc : ν = (c : ℝ≥0∞) • ν' := by
    rw [← hlamπ, hsm, hν'def, Measure.map_smul]
    rfl
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    intro h
    apply h0
    rw [hνc, h, zero_smul]
  refine ⟨(c : ℝ≥0∞)⁻¹, ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top, ENNReal.inv_ne_top.mpr hc0, ?_⟩
  conv_rhs => rw [hνc]
  rw [smul_smul, ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top, one_smul]

end Measure

section Ball

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n)

open scoped ComplexOrder

theorem contDiff_ballDet (τ : Ψ) :
    ContDiff ℝ 2 fun t : Fin n → ℂ => (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det.re := by
  have he : ∀ i k, ContDiff ℝ 2 fun t : Fin n → ℂ => ((1 : Matrix (Fin j') (Fin j') ℂ) - (ballMat q t τ)ᴴ * ballMat q t τ) i k := by
    intro i k
    simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, ballMat, Matrix.of_apply]
    refine contDiff_const.sub (ContDiff.sum fun l _ => ContDiff.mul ?_ ?_)
    · exact Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ _)
    · exact contDiff_apply ℝ ℂ _
  have hd : ContDiff ℝ 2 fun t : Fin n → ℂ => (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det := by
    simp only [Matrix.det_apply]
    refine ContDiff.sum fun σ _ => ContDiff.const_smul _ (contDiff_prod fun i _ => he _ _)
  exact Complex.reCLM.contDiff.comp hd

theorem ballDet_pos {t : Fin n → ℂ} (ht : t ∈ ballDom q) (τ : Ψ) :
    0 < (1 - (ballMat q t τ)ᴴ * ballMat q t τ).det.re :=
  (Complex.lt_def.mp (ht τ).det_pos).1

theorem contDiffAt_ballPot {t : Fin n → ℂ} (ht : t ∈ ballDom q) : ContDiffAt ℝ 2 (ballPot q) t := by
  unfold ballPot
  refine ContDiffAt.neg (ContDiffAt.sum fun τ _ => ?_)
  exact (contDiff_ballDet q τ).contDiffAt.log (ballDet_pos q ht τ).ne'

theorem measurable_ballDens : Measurable (ballDens q) := by
  unfold ballDens ballPot
  refine Real.measurable_exp.comp (measurable_const.mul (Measurable.neg (Finset.measurable_sum _ fun τ _ => ?_)))
  exact Real.measurable_log.comp (contDiff_ballDet q τ).continuous.measurable

theorem continuousOn_ballDens : ContinuousOn (ballDens q) (ballDom q) := by
  intro t ht
  have h1 : ContinuousAt (ballPot q) t := (contDiffAt_ballPot q ht).continuousAt
  have h2 : ContinuousAt (ballDens q) t := by
    unfold ballDens
    exact Real.continuous_exp.continuousAt.comp (continuousAt_const.mul h1)
  exact h2.continuousWithinAt

def ballMeas : Measure (Fin n → ℂ) :=
  (volume.restrict (ballDom q)).withDensity fun t => ENNReal.ofReal (ballDens q t)

theorem ballMeas_apply {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) (hSD : S ⊆ ballDom q) :
    ballMeas q S = ∫⁻ t in S, ENNReal.ofReal (ballDens q t) := by
  rw [ballMeas, withDensity_apply _ hS, Measure.restrict_restrict hS, Set.inter_eq_left.mpr hSD]

theorem ballMeas_image {A : (Fin n → ℂ) → Fin n → ℂ} (hA : DifferentiableOn ℂ A (ballDom q))
    (hAD : ∀ t ∈ ballDom q, A t ∈ ballDom q) (hinj : Set.InjOn A (ballDom q))
    (hd : ∀ t ∈ ballDom q, ballDens q t =
      ‖LinearMap.det ((fderiv ℂ A t : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))‖ ^ 2 *
        ballDens q (A t))
    {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) (hSD : S ⊆ ballDom q) :
    ballMeas q (A '' S) = ballMeas q S := by
  have hD : IsOpen (ballDom q) := BallInverse.isOpen_ballDom q
  have hder : ∀ t ∈ S, HasFDerivWithinAt A ((fderiv ℂ A t).restrictScalars ℝ) S t := fun t ht =>
    (((hA.differentiableAt (hD.mem_nhds (hSD ht))).hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt
  have hinjS : Set.InjOn A S := hinj.mono hSD
  have hmeas : MeasurableSet (A '' S) := measurable_image_of_fderivWithin hS hder hinjS
  have himg : A '' S ⊆ ballDom q := by
    rintro _ ⟨t, ht, rfl⟩
    exact hAD t (hSD ht)
  rw [ballMeas_apply q hmeas himg, ballMeas_apply q hS hSD,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS hder hinjS]
  refine setLIntegral_congr_fun hS fun t ht => ?_
  have hdet : |((fderiv ℂ A t).restrictScalars ℝ : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)).det| =
      ‖LinearMap.det ((fderiv ℂ A t : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))‖ ^ 2 := by
    have h1 : ((fderiv ℂ A t).restrictScalars ℝ : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)).det =
        Algebra.norm ℝ (LinearMap.det ((fderiv ℂ A t : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))) :=
      LinearMap.det_restrictScalars (f := ((fderiv ℂ A t : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)))
    rw [h1, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity)]
  show ENNReal.ofReal _ * ENNReal.ofReal _ = ENNReal.ofReal _
  rw [hdet, ← ENNReal.ofReal_mul (by positivity), ← hd t (hSD ht)]

theorem ballDens_transform {A : (Fin n → ℂ) → Fin n → ℂ} {Gf : (Fin n → ℂ) → ℂ}
    (hA : DifferentiableOn ℂ A (ballDom q)) (hG : DifferentiableOn ℂ Gf (ballDom q))
    (hAD : ∀ t ∈ ballDom q, A t ∈ ballDom q)
    (hp : ∀ t ∈ ballDom q, ballPot q (A t) = ballPot q t + (Gf t).re) {t : Fin n → ℂ} (ht : t ∈ ballDom q) :
    ballDens q t =
      ‖LinearMap.det ((fderiv ℂ A t : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))‖ ^ 2 *
        ballDens q (A t) := by
  have hD : IsOpen (ballDom q) := BallInverse.isOpen_ballDom q
  obtain ⟨c, hc, hdens⟩ := GlobalTheory.T.monge_ampere_density_of_ball_potential Ψ j j' n q
  have hAan : AnalyticAt ℂ A t :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn hA (hD.mem_nhds ht)
  have hGan : AnalyticAt ℂ (fun t' => -(Gf t') / 2) t :=
    (GlobalTheory.SCV.analyticAt_of_differentiableOn hG (hD.mem_nhds ht)).neg.div_const
  have hev : ∀ᶠ t' in 𝓝 t, ballPot q t' / 2 = ballPot q (A t') / 2 + (-(Gf t') / 2).re := by
    filter_upwards [hD.mem_nhds ht] with t' ht'
    rw [hp t' ht']
    simp
    ring
  have hφ : ContDiffAt ℝ 2 (fun t' => ballPot q t' / 2) (A t) :=
    (contDiffAt_ballPot q (hAD t ht)).div_const 2
  have h := GlobalTheory.T.monge_ampere_density_change_of_variables n (fun t' => ballPot q t' / 2) (fun t' => ballPot q t' / 2) A
    (fun t' => -(Gf t') / 2) t hAan hGan hφ hev
  rw [hdens t ht, hdens _ (hAD t ht)] at h
  have hc' : c ≠ 0 := hc.ne'
  apply mul_left_cancel₀ hc'
  rw [h]
  ring

theorem ballMeas_compact_lt_top {C : Set (Fin n → ℂ)} (hC : IsCompact C) (hCD : C ⊆ ballDom q) :
    ballMeas q C < ⊤ := by
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn ((continuousOn_ballDens q).mono hCD)
  rw [ballMeas_apply q hC.measurableSet hCD]
  calc ∫⁻ t in C, ENNReal.ofReal (ballDens q t) ≤ ∫⁻ _ in C, ENNReal.ofReal M :=
        setLIntegral_mono measurable_const fun t ht =>
          ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hM t ht))
    _ = ENNReal.ofReal M * volume C := by simp
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.measure_lt_top

theorem ballMeas_ne_zero (hne : (ballDom q).Nonempty) : ballMeas q (ballDom q) ≠ 0 := by
  have hD : IsOpen (ballDom q) := BallInverse.isOpen_ballDom q
  rw [ballMeas_apply q hD.measurableSet subset_rfl]
  intro h'
  have h := (lintegral_eq_zero_iff (ENNReal.measurable_ofReal.comp (measurable_ballDens q))).mp h'
  have hF : ∀ᵐ _ ∂(volume.restrict (ballDom q)), False := h.mono fun t ht =>
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ht
  have h0 : volume.restrict (ballDom q) = 0 := by
    rw [← ae_eq_bot]
    exact Filter.eventually_false_iff_eq_bot.mp hF
  exact (hD.measure_pos volume hne).ne' (Measure.restrict_eq_zero.mp h0)

theorem ballMeas_restrict : (ballMeas q).restrict (ballDom q) = ballMeas q := by
  have hD : MeasurableSet (ballDom q) := (BallInverse.isOpen_ballDom q).measurableSet
  rw [ballMeas, restrict_withDensity hD, Measure.restrict_restrict hD, Set.inter_self]

end Ball

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem map_haar_eq (F : UnivFam E Ψ j j' n g Λ) (Δ : GroupDict F)
    (μ : Measure (archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))))) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ.map Δ.π =
      c • (volume.restrict (ballDom F.q)).withDensity fun t => ENNReal.ofReal (ballDens F.q t) := by
  have hD : IsOpen (ballDom F.q) := BallInverse.isOpen_ballDom F.q
  haveI : LocallyCompactSpace (ballDom F.q) := hD.locallyCompactSpace
  have hmem : ∀ a, Δ.π a ∈ ballDom F.q := fun a => Δ.π_range ▸ Set.mem_range_self a
  choose A Gf hA hG hπA hpot using Δ.act
  have hAD : ∀ a, ∀ t ∈ ballDom F.q, A a t ∈ ballDom F.q := by
    intro a t ht
    rw [← Δ.π_range] at ht
    obtain ⟨b, rfl⟩ := ht
    rw [← hπA]
    exact hmem _
  let π' : archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))) → ballDom F.q := fun a => ⟨Δ.π a, hmem a⟩
  let T : archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))) → ballDom F.q → ballDom F.q :=
    fun a x => ⟨A a x, hAD a x x.2⟩
  have hc : Continuous π' := Δ.π_cont.subtype_mk _
  have hs : Function.Surjective π' := by
    rintro ⟨t, ht⟩
    have ht' := ht
    rw [← Δ.π_range] at ht'
    obtain ⟨b, rfl⟩ := ht'
    exact ⟨b, rfl⟩
  have hT : ∀ a, Continuous (T a) := fun a => ((hA a).continuousOn.restrict).subtype_mk _
  have hπ : ∀ a b, π' (a * b) = T a (π' b) := fun a b => Subtype.ext (hπA a b)
  have hK : IsCompact (Δ.M.stab : Set (archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))))) :=
    MajorantStabCompact.proof Δ.h _ Δ.M
  have hf : ∀ a b, π' a = π' b → a⁻¹ * b ∈ (Δ.M.stab : Set (archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))))) :=
    fun a b h => (Δ.π_fibre a b).mp (congrArg Subtype.val h)
  have hemb : MeasurableEmbedding (Subtype.val : ballDom F.q → Fin n → ℂ) :=
    MeasurableEmbedding.subtype_coe hD.measurableSet
  let νX : Measure (ballDom F.q) := (ballMeas F.q).comap Subtype.val
  have hνX : ∀ S, νX S = ballMeas F.q (Subtype.val '' S) := fun S => hemb.comap_apply _ S
  haveI : IsFiniteMeasureOnCompacts νX := ⟨fun C hC => by
    rw [hνX]
    exact ballMeas_compact_lt_top F.q (hC.image continuous_subtype_val) (Subtype.coe_image_subset _ _)⟩
  have hinv : ∀ a, νX.map (T a) = νX := by
    intro a
    refine Measure.ext fun S hS => ?_
    rw [Measure.map_apply (hT a).measurable hS, hνX, hνX]
    have hS0 : MeasurableSet (Subtype.val '' (T a ⁻¹' S)) :=
      hemb.measurableSet_image.mpr ((hT a).measurable hS)
    have himg : A a '' (Subtype.val '' (T a ⁻¹' S)) = Subtype.val '' S := by
      ext y
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨T a x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        have e : T a ((translHomeo hs hT hπ a).symm x) = x := (translHomeo hs hT hπ a).apply_symm_apply x
        exact ⟨_, ⟨(translHomeo hs hT hπ a).symm x, by rw [Set.mem_preimage, e]; exact hx, rfl⟩,
          congrArg Subtype.val e⟩
    have hinj : Set.InjOn (A a) (ballDom F.q) := by
      intro t ht t' ht' e
      have h1 : T a ⟨t, ht⟩ = T a ⟨t', ht'⟩ := Subtype.ext e
      exact congrArg Subtype.val ((translHomeo hs hT hπ a).injective h1)
    rw [← himg, ballMeas_image F.q (hA a) (hAD a) hinj
      (fun t ht => ballDens_transform F.q (hA a) (hG a) (hAD a) (hpot a) ht) hS0
      (Subtype.coe_image_subset _ _)]
  have h0 : νX ≠ 0 := by
    intro h
    have h1 := hνX Set.univ
    rw [h, Subtype.coe_image_univ] at h1
    exact ballMeas_ne_zero F.q ⟨_, hmem 1⟩ h1.symm
  obtain ⟨c, hc0, hct, h⟩ := map_haar_eq_smul hc hs hT hπ hK hf μ νX hinv h0
  refine ⟨c, hc0, hct, ?_⟩
  have h1 : μ.map Δ.π = (μ.map π').map Subtype.val := by
    rw [Measure.map_map measurable_subtype_coe hc.measurable]
    rfl
  rw [h1, h, Measure.map_smul, map_comap_subtype_coe hD.measurableSet, ballMeas_restrict]
  rfl

end Main

end GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas

theorem GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas.haar_projects : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (Δ : GroupDict F) (μ : Measure (archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))))) [μ.IsHaarMeasure], ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ.map Δ.π = c • (volume.restrict (ballDom F.q)).withDensity fun t => ENNReal.ofReal (ballDens F.q t) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ F Δ μ _ => GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas.map_haar_eq F Δ μ
