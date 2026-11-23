import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TypeFin
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
import GroundTheory.AutomorphicForms.GKModules.Garding
import GroundTheory.AutomorphicForms.L2LocalComponents.ArchBump
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SmoothingFinite

section Lie

open MeasureTheory Set Filter Topology GroundTheory.Automorphic
open scoped ContDiff Manifold

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

private theorem partial_iter {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup Q]
    [NormedSpace ℝ Q] {Φ : P × Q → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (k : ℕ) :
    Continuous fun p : P × Q => iteratedFDeriv ℝ k (fun Y => Φ (Y, p.2)) p.1 := by
  set L := ContinuousLinearMap.inl ℝ P Q
  have hH : Continuous fun q : P × Q =>
      ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => L) (iteratedFDeriv ℝ k Φ q) :=
    (ContinuousLinearMap.continuous _).comp (hΦ.continuous_iteratedFDeriv (by exact_mod_cast le_top))
  convert hH using 2 with p
  obtain ⟨Y, Z⟩ := p
  have e : (fun Y => Φ (Y, Z)) = (fun w => Φ (w + (0, Z))) ∘ L := by
    funext Y; simp [L]
  have hZ : ContDiff ℝ ∞ fun w : P × Q => Φ (w + (0, Z)) := hΦ.comp (contDiff_id.add contDiff_const)
  simp only
  rw [e, L.iteratedFDeriv_comp_right hZ Y (by exact_mod_cast le_top), iteratedFDeriv_comp_add_right]
  simp [L]

private theorem chart_form {f : G → ℂ} (hf : h.IsSmoothFun f) (q₀ r₀ : G) :
    ContDiff ℝ ∞ fun p : 𝔤 × 𝔤 × 𝔤 => f (q₀ * h.expG p.2.1 * h.expG p.1 * (r₀ * h.expG p.2.2)) := by
  letI := h.chartedSpace
  haveI := h.lieGroup ∞
  have hm : ContMDiff 𝓘(ℝ, 𝔤 × 𝔤 × 𝔤) 𝓘(ℝ, 𝔤) ∞
      fun p : 𝔤 × 𝔤 × 𝔤 => q₀ * h.expG p.2.1 * h.expG p.1 * (r₀ * h.expG p.2.2) :=
    ((contMDiff_const.mul (h.contMDiff_expG_comp (contDiff_fst.comp contDiff_snd))).mul
      (h.contMDiff_expG_comp contDiff_fst)).mul
      (contMDiff_const.mul (h.contMDiff_expG_comp (contDiff_snd.comp contDiff_snd)))
  exact (ContMDiff.comp (I' := 𝓘(ℝ, 𝔤)) hf hm).contDiff

private theorem smooth_slice {f : G → ℂ} (hf : h.IsSmoothFun f) (q r : G) :
    ContDiff ℝ ∞ fun Y : 𝔤 => f (q * h.expG Y * r) := by
  have := (chart_form h hf q r).comp (contDiff_id.prodMk (contDiff_const (c := ((0 : 𝔤), (0 : 𝔤)))))
  simpa [Function.comp_def, h.expG_zero] using this

private theorem two_param {f : G → ℂ} (hf : h.IsSmoothFun f) (k : ℕ) :
    Continuous fun p : 𝔤 × G × G => iteratedFDeriv ℝ k (fun Y => f (p.2.1 * h.expG Y * p.2.2)) p.1 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨Y₀, q₀, r₀⟩
  letI := h.chartedSpace
  have hq : q₀ ∈ (h.chart q₀).source := mem_chart_source 𝔤 q₀
  have hr : r₀ ∈ (h.chart r₀).source := mem_chart_source 𝔤 r₀
  have hc := partial_iter (chart_form h hf q₀ r₀) k
  have hev : (fun p : 𝔤 × G × G => iteratedFDeriv ℝ k (fun Y => f (p.2.1 * h.expG Y * p.2.2)) p.1) =ᶠ[𝓝 (Y₀, q₀, r₀)]
      fun p => iteratedFDeriv ℝ k (fun Y => f (q₀ * h.expG (h.chart q₀ p.2.1) * h.expG Y *
        (r₀ * h.expG (h.chart r₀ p.2.2)))) p.1 := by
    filter_upwards [prod_mem_nhds univ_mem (prod_mem_nhds ((h.chart q₀).open_source.mem_nhds hq)
      ((h.chart r₀).open_source.mem_nhds hr))] with p hp
    rw [show q₀ * h.expG (h.chart q₀ p.2.1) = p.2.1 from (h.chart q₀).left_inv hp.2.1,
      show r₀ * h.expG (h.chart r₀ p.2.2) = p.2.2 from (h.chart r₀).left_inv hp.2.2]
  refine ContinuousAt.congr ?_ hev.symm
  exact hc.continuousAt.comp (f := fun p : 𝔤 × G × G => (p.1, h.chart q₀ p.2.1, h.chart r₀ p.2.2))
    (continuousAt_fst.prodMk ((((h.chart q₀).continuousAt hq).comp (continuousAt_fst.comp continuousAt_snd)).prodMk
      (((h.chart r₀).continuousAt hr).comp (continuousAt_snd.comp continuousAt_snd))))

private theorem smooth_family {S : Type*} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [CompactSpace S]
    [MeasurableSpace S] [OpensMeasurableSpace S] (ρ : Measure S) [IsFiniteMeasure ρ] {f : S → G → ℂ}
    (hf : ∀ s, h.IsSmoothFun (f s))
    (hl : ∀ s₀, ∃ β : S → G, Continuous β ∧ ∀ᶠ s in 𝓝 s₀, ∀ A, f s A = f s₀ (A * β s))
    {w : S → ℂ} (hw : Continuous w) {q r : S → G} (hq : Continuous q) (hr : Continuous r) :
    h.IsSmoothFun fun A => ∫ s, w s * f s (q s * A * r s) ∂ρ := by
  rw [h.isSmoothFun_iff]
  intro g
  let F : 𝔤 → S → ℂ := fun Y s => w s * f s (q s * (g * h.expG Y) * r s)
  refine contDiff_integral_of_iteratedFDeriv F (fun s => ?_) (fun k => ?_) (fun Y₀ => ?_)
  · have := smooth_slice h (hf s) (q s * g) (r s)
    exact contDiff_const.mul (by simpa only [mul_assoc] using this)
  · rw [continuous_iff_continuousAt]
    rintro ⟨Y₀, s₀⟩
    obtain ⟨β, hβ, hev₀⟩ := hl s₀
    have hc := two_param h (hf s₀) k
    have hev : (fun p : 𝔤 × S => ParamIntegral.iter F k p.1 p.2) =ᶠ[𝓝 (Y₀, s₀)] fun p => w p.2 •
        iteratedFDeriv ℝ k (fun Y => f s₀ (q p.2 * g * h.expG Y * (r p.2 * β p.2))) p.1 := by
      filter_upwards [prod_mem_nhds univ_mem hev₀] with p hp
      have hF : (fun Y => F Y p.2) = fun Y => w p.2 • f s₀ (q p.2 * g * h.expG Y * (r p.2 * β p.2)) := by
        funext Y
        simp only [F, smul_eq_mul]
        rw [hp.2]
        simp only [mul_assoc]
      rw [ParamIntegral.iter, hF]
      exact iteratedFDeriv_const_smul_apply' ((smooth_slice h (hf s₀) _ _).contDiffAt.of_le (by exact_mod_cast le_top))
    refine ContinuousAt.congr ?_ hev.symm
    refine Continuous.continuousAt ?_
    exact (hw.comp continuous_snd).smul (hc.comp (continuous_fst.prodMk
      (((hq.comp continuous_snd).mul continuous_const).prodMk ((hr.comp continuous_snd).mul (hβ.comp continuous_snd)))))
  · exact ⟨univ, univ_mem, univ, isCompact_univ, fun _ _ _ h => absurd trivial h⟩

end Lie

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section Adel

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem retract_self (z : G1 K n) : retractOne (z : AdelicGLn.AdelicGL K n) = z := by
  ext1
  rw [coe_retractOne, (mem_normOneGL_iff_detModule).1 z.2, map_one, inv_one, mul_one]

private theorem dec_near (x₀ : G1 K n) (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))) :
    ∀ᶠ y in 𝓝 x₀, ∃ u ∈ U, y = archP K n (infPart K n ((y * x₀⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n)) * finOne K n u * x₀ := by
  have hc : Continuous fun y : G1 K n => finPart K n ((y * x₀⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n) :=
    continuous_finPart.comp (continuous_subtype_val.comp (continuous_id.mul continuous_const))
  have ho : IsOpen ((finOpenSubgroup U hU : OpenSubgroup _) : Set (AdelicGLn.FiniteAdelicGL K n)) :=
    (finOpenSubgroup U hU).isOpen
  have h1 : (1 : AdelicGLn.FiniteAdelicGL K n) ∈ ((finOpenSubgroup U hU : OpenSubgroup _) : Set (AdelicGLn.FiniteAdelicGL K n)) :=
    (finOpenSubgroup U hU).one_mem
  filter_upwards [(ho.preimage hc).mem_nhds (by simpa using h1)] with y hy
  obtain ⟨u, hu, e⟩ : ∃ u ∈ U, ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n) =
      finPart K n ((y * x₀⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n) := by
    obtain ⟨u, hu, e⟩ := hy
    exact ⟨u, hu, e⟩
  refine ⟨u, hu, ?_⟩
  set z : G1 K n := y * x₀⁻¹ with hz
  have h2 := retractOne_mul_finEmb (infEmb K n (infPart K n (z : AdelicGLn.AdelicGL K n))) u.2
  have e' : infEmb K n (infPart K n (z : AdelicGLn.AdelicGL K n)) * finEmb K n (u : AdelicGLn.FiniteAdelicGL K n) =
      (z : AdelicGLn.AdelicGL K n) := by
    rw [e, infEmb_infPart_mul_finEmb_finPart]
  rw [e', retract_self, retract_infEmb] at h2
  rw [show archP K n (infPart K n (z : AdelicGLn.AdelicGL K n)) * finOne K n u = z from h2.symm, hz]
  simp

private theorem slide {b : G1 K n → ℂ} {U : Subgroup (AdelicGLn.integralFiniteGL K n)}
    (hinv : ∀ u ∈ U, ∀ x, b (finOne K n u * x) = b x) (B β : archGroup K n) {u : AdelicGLn.integralFiniteGL K n}
    (hu : u ∈ U) (x : G1 K n) :
    b (archP K n B * (archP K n β * finOne K n u * x)) = b (archP K n (B * β) * x) := by
  rw [map_mul, ← hinv u hu (archP K n B * archP K n β * x)]
  congr 1
  rw [archimedeanProjection_mul_finiteEmbedding_comm β u, mul_assoc (finOne K n u), ← mul_assoc (archP K n B), archimedeanProjection_mul_finiteEmbedding_comm B u]
  simp only [mul_assoc]

private theorem smooth_avg {S : Type*} [TopologicalSpace S] [T2Space S] [SecondCountableTopology S] [CompactSpace S]
    [MeasurableSpace S] [OpensMeasurableSpace S] (ρ : Measure S) [IsFiniteMeasure ρ] {b : G1 K n → ℂ}
    (hb : UpperTheory.ConvolutionTheory.C.IsLeftSmooth b) {w : S → ℂ} (hw : Continuous w) {q r : S → archGroup K n} (hq : Continuous q)
    (hr : Continuous r) {y : S → G1 K n} (hy : Continuous y) :
    (isExpLieAlgebra K n).IsSmoothFun fun A : archGroup K n => ∫ s, w s * b (archP K n (q s * A * r s) * y s) ∂ρ := by
  obtain ⟨hsm, U, hU, hinv⟩ := hb
  refine smooth_family (isExpLieAlgebra K n) ρ (f := fun s A => b (archP K n A * y s)) (fun s => hsm (y s)) (fun s₀ => ?_) hw hq hr
  refine ⟨fun s => infPart K n ((y s * (y s₀)⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n),
    continuous_infPart.comp (continuous_subtype_val.comp (hy.mul continuous_const)), ?_⟩
  filter_upwards [hy.continuousAt.preimage_mem_nhds (dec_near (y s₀) U hU)] with s hs A
  obtain ⟨u, hu, e⟩ := hs
  exact (congrArg (fun t => b (archP K n A * t)) e).trans (slide hinv _ _ hu (y s₀))

end Adel

section Gen

private theorem integ {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {U : Set X} (hU : IsCompact U) {ν : Measure X} [IsFiniteMeasure ν] (hs : ∀ᵐ k ∂ν, k ∈ U) {F : X → ℂ}
    (hF : Continuous F) : Integrable F ν := by
  have h := hF.continuousOn.integrableOn_compact (μ := ν) hU
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hs] at h

private theorem inv_preserved {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (ν : Measure G) [IsProbabilityMeasure ν] (U : Subgroup G) (hs : ∀ᵐ k ∂ν, k ∈ U)
    (hi : ∀ k ∈ U, MeasurePreserving (k * ·) ν ν) : ν.map (·⁻¹) = ν := by
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_map hφ measurable_inv]
  have hm : Measurable fun p : G × G => φ (p.1⁻¹ * p.2) := hφ.comp (measurable_fst.inv.mul measurable_snd)
  have a1 : ∫⁻ k, ∫⁻ x, φ (k⁻¹ * x) ∂ν ∂ν = ∫⁻ x, φ x ∂ν := by
    rw [lintegral_congr_ae (g := fun _ => ∫⁻ x, φ x ∂ν)
      (hs.mono fun k hk => (hi _ (U.inv_mem hk)).lintegral_comp hφ)]
    simp
  have a2 : ∫⁻ x, ∫⁻ k, φ (k⁻¹ * x) ∂ν ∂ν = ∫⁻ k, φ k⁻¹ ∂ν := by
    rw [lintegral_congr_ae (g := fun _ => ∫⁻ k, φ k⁻¹ ∂ν) (hs.mono fun x hx => ?_)]
    · simp
    · have := (hi _ hx).lintegral_comp (f := fun k => φ (k⁻¹ * x)) (hφ.comp (measurable_inv.mul_const x))
      rw [← this]
      simp
  rw [← a1, ← a2]
  exact (lintegral_lintegral_swap hm.aemeasurable).symm

end Gen

section Typ

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (D : TypeDat K n)

private theorem inv_int (φ : G1 K n → ℂ) : ∫ k, φ k⁻¹ ∂D.ν = ∫ k, φ k ∂D.ν := by
  haveI := D.prob
  have h := integral_map_equiv (μ := D.ν) (MeasurableEquiv.inv (G1 K n)) φ
  rw [show Measure.map (MeasurableEquiv.inv (G1 K n)) D.ν = D.ν from inv_preserved D.ν D.U D.supp D.inv] at h
  exact h.symm

private theorem integ₂ {F : G1 K n × G1 K n → ℂ} (hF : Continuous F) : Integrable F (D.ν.prod D.ν) := by
  haveI := D.prob
  have hU := (typeFin D).1
  refine integ (hU.prod hU) ?_ hF
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae D.supp, Measure.quasiMeasurePreserving_snd.ae D.supp] with z a b
  exact ⟨a, b⟩

private theorem cont_int {Φ : G1 K n → G1 K n → ℂ} (hΦ : Continuous (Function.uncurry Φ)) :
    Continuous fun x => ∫ k, Φ x k ∂D.ν := by
  haveI := D.prob
  have := continuous_parametric_integral_of_continuous (μ := D.ν) hΦ (typeFin D).1
  rwa [Measure.restrict_eq_self_of_ae_mem D.supp] at this

private theorem sub_int (f : G1 K n → ℂ) :
    ∫ k, f k ∂D.ν = ∫ s : (D.U : Set (G1 K n)), f s ∂(Measure.comap Subtype.val D.ν) := by
  rw [integral_subtype_comap (typeFin D).1.isClosed.measurableSet, Measure.restrict_eq_self_of_ae_mem D.supp]

private theorem fin_comap : IsFiniteMeasure (Measure.comap (Subtype.val : ↥(D.U : Set (G1 K n)) → G1 K n) D.ν) := by
  haveI := D.prob
  refine ⟨?_⟩
  rw [(MeasurableEmbedding.subtype_coe (typeFin D).1.isClosed.measurableSet).comap_apply]
  exact measure_lt_top _ _

private theorem idem_int {Φ : G1 K n → ℂ} (hΦ : Continuous Φ) :
    ∫ h, D.e h * ∫ k, D.e k * Φ (h * k) ∂D.ν ∂D.ν = ∫ k, D.e k * Φ k ∂D.ν := by
  haveI := D.prob
  have h1 : ∀ᵐ h ∂D.ν, D.e h * ∫ k, D.e k * Φ (h * k) ∂D.ν = ∫ k, D.e h * (D.e (h⁻¹ * k) * Φ k) ∂D.ν :=
    D.supp.mono fun h hh => by
      have := (D.inv h hh).integral_comp (measurableEmbedding_mulLeft h) (fun k => D.e (h⁻¹ * k) * Φ k)
      rw [integral_const_mul, ← this]
      simp
  rw [integral_congr_ae h1, integral_integral_swap
    (integ₂ D (F := Function.uncurry fun h k => D.e h * (D.e (h⁻¹ * k) * Φ k))
      ((D.cont.comp continuous_fst).mul ((D.cont.comp (continuous_fst.inv.mul continuous_snd)).mul (hΦ.comp continuous_snd))))]
  refine integral_congr_ae (D.supp.mono fun k hk => ?_)
  simp only [← mul_assoc]
  rw [integral_mul_const, D.idem k hk]

end Typ

section Ops

open scoped Pointwise

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem conj_arch (m : G1 K n) (A : archGroup K n) :
    m * archP K n A = archP K n (infPart K n (m : AdelicGLn.AdelicGL K n) * A * (infPart K n (m : AdelicGLn.AdelicGL K n))⁻¹) * m := by
  set κ := infPart K n (m : AdelicGLn.AdelicGL K n) with hκ
  have hA : ∀ a : archGroup K n, (archP K n a : AdelicGLn.AdelicGL K n) =
      infEmb K n a * (centralSection K n (detModule K n (infEmb K n a)))⁻¹ := fun a => by
    rw [← retract_infEmb, coe_retractOne]
  have hd : detModule K n (infEmb K n (κ * A * κ⁻¹)) = detModule K n (infEmb K n A) := by
    simp only [map_mul, map_inv]
    exact mul_inv_cancel_comm _ _
  have hm : (m : AdelicGLn.AdelicGL K n) = infEmb K n κ * finEmb K n (finPart K n (m : AdelicGLn.AdelicGL K n)) :=
    (infEmb_infPart_mul_finEmb_finPart _).symm
  have h1 : (m : AdelicGLn.AdelicGL K n) * infEmb K n A = infEmb K n (κ * A * κ⁻¹) * m := by
    conv_lhs => rw [hm, mul_assoc, ← infEmb_mul_finEmb_comm, ← mul_assoc, ← map_mul]
    conv_rhs => rw [hm, ← mul_assoc, ← map_mul, inv_mul_cancel_right]
  ext1
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hA, hA, hd, ← mul_assoc, h1, mul_assoc, ← centralSection_inv_mul_comm, ← mul_assoc]

private theorem fin_conj {m : G1 K n} (hm : (m : AdelicGLn.AdelicGL K n) ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)))
    (u : AdelicGLn.integralFiniteGL K n) :
    ∃ φ : AdelicGLn.integralFiniteGL K n, m * finOne K n u = finOne K n (φ * u * φ⁻¹) * m := by
  obtain ⟨φ, hφ⟩ : ∃ φ : AdelicGLn.integralFiniteGL K n,
      (φ : AdelicGLn.FiniteAdelicGL K n) = finPart K n (m : AdelicGLn.AdelicGL K n) := ⟨⟨_, finPart_mem_integralFiniteGL hm⟩, rfl⟩
  obtain ⟨κ, e⟩ : ∃ κ, (m : AdelicGLn.AdelicGL K n) = infEmb K n κ * finEmb K n (φ : AdelicGLn.FiniteAdelicGL K n) :=
    ⟨_, by rw [hφ, infEmb_infPart_mul_finEmb_finPart]⟩
  refine ⟨φ, ?_⟩
  ext1
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_finOne, coe_finOne, e]
  have hw := infEmb_mul_finEmb_comm κ ((φ * u * φ⁻¹ : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n)
  rw [← mul_assoc (finEmb K n _), ← hw, mul_assoc, mul_assoc]
  congr 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
  simp

variable (D : TypeDat K n)

private theorem exR (f : CC K n) : ∃ b : CC K n, (∀ g, b g = ∫ k, f (g * k⁻¹) * D.e k ∂D.ν) ∧
    (UpperTheory.ConvolutionTheory.C.IsLeftSmooth f → UpperTheory.ConvolutionTheory.C.IsLeftSmooth b) := by
  have hU := (typeFin D).1
  have hc : Continuous fun g => ∫ k, f (g * k⁻¹) * D.e k ∂D.ν :=
    cont_int D (Φ := fun g k => f (g * k⁻¹) * D.e k)
      ((f.continuous.comp (continuous_fst.mul continuous_snd.inv)).mul (D.cont.comp continuous_snd))
  have hz : ∀ g, g ∉ tsupport f * (D.U : Set (G1 K n)) → ∫ k, f (g * k⁻¹) * D.e k ∂D.ν = 0 := fun g hg => by
    refine integral_eq_zero_of_ae (D.supp.mono fun k hk => ?_)
    have : f (g * k⁻¹) = 0 := by
      by_contra h0
      exact hg ⟨_, subset_tsupport _ h0, k, hk, by simp⟩
    simp [this]
  refine ⟨⟨⟨_, hc⟩, HasCompactSupport.intro (f.hasCompactSupport.isCompact.mul hU) hz⟩, fun _ => rfl, fun hf => ⟨fun x => ?_, ?_⟩⟩
  · haveI : CompactSpace (D.U : Set (G1 K n)) := isCompact_iff_compactSpace.1 hU
    haveI := fin_comap D
    have := smooth_avg (Measure.comap Subtype.val D.ν) hf (w := fun s : (D.U : Set (G1 K n)) => D.e s)
      (D.cont.comp continuous_subtype_val) (q := fun _ => 1) (r := fun _ => 1) continuous_const continuous_const
      (y := fun s => x * (s : G1 K n)⁻¹) (continuous_const.mul continuous_subtype_val.inv)
    convert this using 2 with A
    change ∫ k, f (archP K n A * x * k⁻¹) * D.e k ∂D.ν = _
    rw [sub_int]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp [mul_comm (D.e _), mul_assoc]
  · obtain ⟨-, U, hUo, hinv⟩ := hf
    refine ⟨U, hUo, fun u hu x => ?_⟩
    change ∫ k, f (finOne K n u * x * k⁻¹) * D.e k ∂D.ν = ∫ k, f (x * k⁻¹) * D.e k ∂D.ν
    simp only [mul_assoc, hinv u hu]

private theorem exL (f : CC K n) : ∃ c : CC K n, (∀ g, c g = ∫ k, D.e k * f (k⁻¹ * g) ∂D.ν) ∧
    (UpperTheory.ConvolutionTheory.C.IsLeftSmooth f → UpperTheory.ConvolutionTheory.C.IsLeftSmooth c) := by
  have hU := (typeFin D).1
  have hc : Continuous fun g => ∫ k, D.e k * f (k⁻¹ * g) ∂D.ν :=
    cont_int D (Φ := fun g k => D.e k * f (k⁻¹ * g))
      ((D.cont.comp continuous_snd).mul (f.continuous.comp (continuous_snd.inv.mul continuous_fst)))
  have hz : ∀ g, g ∉ (D.U : Set (G1 K n)) * tsupport f → ∫ k, D.e k * f (k⁻¹ * g) ∂D.ν = 0 := fun g hg => by
    refine integral_eq_zero_of_ae (D.supp.mono fun k hk => ?_)
    have : f (k⁻¹ * g) = 0 := by
      by_contra h0
      exact hg ⟨k, hk, _, subset_tsupport _ h0, by simp⟩
    simp [this]
  refine ⟨⟨⟨_, hc⟩, HasCompactSupport.intro (hU.mul f.hasCompactSupport.isCompact) hz⟩, fun _ => rfl, fun hf => ⟨fun x => ?_, ?_⟩⟩
  · haveI : CompactSpace (D.U : Set (G1 K n)) := isCompact_iff_compactSpace.1 hU
    haveI := fin_comap D
    let κ : ↥(D.U : Set (G1 K n)) → archGroup K n := fun s => infPart K n (((s : G1 K n)⁻¹ : G1 K n) : AdelicGLn.AdelicGL K n)
    have hκ : Continuous κ := continuous_infPart.comp (continuous_subtype_val.comp continuous_subtype_val.inv)
    have := smooth_avg (Measure.comap Subtype.val D.ν) hf (w := fun s : (D.U : Set (G1 K n)) => D.e s)
      (D.cont.comp continuous_subtype_val) (q := κ) (r := fun s => (κ s)⁻¹) hκ hκ.inv (y := fun s => (s : G1 K n)⁻¹ * x)
      (continuous_subtype_val.inv.mul continuous_const)
    convert this using 2 with A
    change ∫ k, D.e k * f (k⁻¹ * (archP K n A * x)) ∂D.ν = _
    rw [sub_int]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [← mul_assoc]
    rw [conj_arch]
  · obtain ⟨-, U, hUo, hinv⟩ := hf
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo U.one_mem
    refine ⟨N.toOpenSubgroup.toSubgroup, N.toOpenSubgroup.isOpen, fun u hu x => ?_⟩
    change ∫ k, D.e k * f (k⁻¹ * (finOne K n u * x)) ∂D.ν = ∫ k, D.e k * f (k⁻¹ * x) ∂D.ν
    refine integral_congr_ae (D.supp.mono fun k hk => ?_)
    have hk' : k⁻¹ ∈ KG K n := SetLike.le_def.1 (typeFin D).2.1 (D.U.inv_mem hk)
    rw [KG, Subgroup.mem_comap] at hk'
    obtain ⟨φ, hφ⟩ := fin_conj (m := k⁻¹) hk' u
    beta_reduce
    rw [← mul_assoc, hφ, mul_assoc, hinv _ (hN (N.isNormal'.conj_mem u hu φ))]

end Ops

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.heckify :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (D : TypeDat K n) (a₀ : CC K n), CuspidalProjection.ccStar a₀ = a₀ → UpperTheory.ConvolutionTheory.C.IsLeftSmooth a₀ →
      ∃ a : CC K n, D.Hecke a ∧ CuspidalProjection.ccStar a = a ∧ UpperTheory.ConvolutionTheory.C.IsLeftSmooth a ∧
        ∀ g, a g = ∫ k, ∫ k', D.e k * a₀ (k⁻¹ * g * k'⁻¹) * D.e k' ∂D.ν ∂D.ν := by
  intro K _ _ n μ _ D a₀ hst hsm
  haveI := D.prob
  obtain ⟨b, hb, hbs⟩ := exR D a₀
  obtain ⟨a, ha, has⟩ := exL D b
  have hform : ∀ g, a g = ∫ k, ∫ k', D.e k * a₀ (k⁻¹ * g * k'⁻¹) * D.e k' ∂D.ν ∂D.ν := fun g => by
    rw [ha]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    beta_reduce
    rw [hb, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun k' => ?_)
    simp only [mul_assoc]
  have hs₀ : ∀ y, conj (a₀ y) = a₀ y⁻¹ := fun y => by
    have := DFunLike.congr_fun hst y⁻¹
    rwa [CuspidalProjection.ccStar_apply, inv_inv] at this
  have hTc : Continuous fun p : G1 K n × G1 K n => a₀ (p.1 * p.2) := a₀.continuous.comp (continuous_fst.mul continuous_snd)
  have key : ∀ g, conj (a g⁻¹) = a g := fun g => by
    let T : G1 K n → G1 K n → ℂ := fun k k' => D.e k * a₀ (k⁻¹ * g * k'⁻¹) * D.e k'
    have hT : Continuous (Function.uncurry fun k k' => T k' k) :=
      ((D.cont.comp continuous_snd).mul (a₀.continuous.comp ((continuous_snd.inv.mul continuous_const).mul
        continuous_fst.inv))).mul (D.cont.comp continuous_fst)
    calc conj (a g⁻¹) = ∫ k, ∫ k', T k'⁻¹ k⁻¹ ∂D.ν ∂D.ν := by
          rw [hform, ← integral_conj]
          refine integral_congr_ae (D.supp.mono fun k hk => ?_)
          beta_reduce
          rw [← integral_conj]
          refine integral_congr_ae (D.supp.mono fun k' hk' => ?_)
          simp only [T, map_mul, ← D.star k hk, ← D.star k' hk', hs₀, mul_inv_rev, inv_inv, mul_assoc]
          ring
      _ = ∫ k, ∫ k', T k' k⁻¹ ∂D.ν ∂D.ν :=
          integral_congr_ae (Eventually.of_forall fun k => inv_int D fun k' => T k' k⁻¹)
      _ = ∫ k, ∫ k', T k' k ∂D.ν ∂D.ν := inv_int D fun k => ∫ k', T k' k ∂D.ν
      _ = ∫ k', ∫ k, T k' k ∂D.ν ∂D.ν := integral_integral_swap (integ₂ D hT)
      _ = a g := (hform g).symm
  have hL : ∀ g, ∫ k, D.e k * a (k⁻¹ * g) ∂D.ν = a g := fun g => by
    rw [ha g, ← idem_int D (Φ := fun k => b (k⁻¹ * g)) (b.continuous.comp (continuous_inv.mul continuous_const))]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    beta_reduce
    rw [ha]
    simp only [mul_inv_rev, mul_assoc]
  have hR : ∀ g, ∫ k, a (g * k⁻¹) * D.e k ∂D.ν = a g := fun g => by
    have h2 := inv_int D fun k => D.e k * a (k⁻¹ * g⁻¹)
    simp only [inv_inv] at h2
    rw [hL] at h2
    rw [← key g, ← h2, ← integral_conj]
    refine integral_congr_ae (D.supp.mono fun k hk => ?_)
    simp only [map_mul, D.star k hk, Complex.conj_conj]
    rw [show k * g⁻¹ = (g * k⁻¹)⁻¹ by simp, key, mul_comm]
  refine ⟨a, fun g => ⟨hL g, hR g⟩, ?_, has (hbs hsm), hform⟩
  ext g
  rw [CuspidalProjection.ccStar_apply, key]
