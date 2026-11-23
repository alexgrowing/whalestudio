import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private noncomputable def trCc {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (h : G)
    (β : CompactlySupportedContinuousMap G ℂ) : CompactlySupportedContinuousMap G ℂ where
  toFun x := β (h⁻¹ * x)
  continuous_toFun := β.continuous.comp (continuous_const_mul h⁻¹)
  hasCompactSupport' := by
    refine HasCompactSupport.intro (β.hasCompactSupport.isCompact.image (continuous_const_mul h))
      fun x hx => ?_
    by_contra hne
    exact hx ⟨h⁻¹ * x, subset_tsupport _ hne, by simp⟩

private theorem map_integrated_trCc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsMulLeftInvariant]
    [IsFiniteMeasureOnCompacts ν] (π : UnitaryRep G H) (h : G)
    (β : CompactlySupportedContinuousMap G ℂ) (v : H) :
    π h (π.integrated ν (UnitaryRep.ccToL1 ν β) v) =
      π.integrated ν (UnitaryRep.ccToL1 ν (trCc h β)) v := by
  have e := π.map_comp_integrated ν h (UnitaryRep.ccToL1 ν β)
  have e2 : UnitaryRep.leftTranslate ν h (UnitaryRep.ccToL1 ν β) =
      UnitaryRep.ccToL1 ν (trCc h β) := by
    refine Lp.ext ?_
    have hc := (β.continuous.memLp_of_hasCompactSupport (μ := ν) (p := 1) β.hasCompactSupport).coeFn_toLp
    have hc' := ((trCc h β).continuous.memLp_of_hasCompactSupport (μ := ν) (p := 1)
      (trCc h β).hasCompactSupport).coeFn_toLp
    filter_upwards [UnitaryRep.coeFn_leftTranslate ν h (UnitaryRep.ccToL1 ν β), hc',
      (measurePreserving_mul_left ν h⁻¹).quasiMeasurePreserving.ae_eq_comp hc] with x h1 h2 h3
    rw [h1]
    change (UnitaryRep.ccToL1 ν β : G → ℂ) (h⁻¹ * x) = (UnitaryRep.ccToL1 ν (trCc h β)) x
    rw [show (UnitaryRep.ccToL1 ν β : G → ℂ) (h⁻¹ * x) = β (h⁻¹ * x) from h3,
      show (UnitaryRep.ccToL1 ν (trCc h β) : G → ℂ) x = trCc h β x from h2]
    rfl
  rw [e2] at e
  exact congrArg (fun A : H →L[ℂ] H => A v) e

private theorem ccToL1_smul {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] (a : ℂ) (f : CompactlySupportedContinuousMap G ℂ) :
    UnitaryRep.ccToL1 ν (a • f) = a • UnitaryRep.ccToL1 ν f := by
  unfold UnitaryRep.ccToL1
  rw [← MemLp.toLp_const_smul]
  rfl

private theorem ccToL1_finsetSum {G ι : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] (s : Finset ι) (f : ι → CompactlySupportedContinuousMap G ℂ) :
    UnitaryRep.ccToL1 ν (∑ i ∈ s, f i) = ∑ i ∈ s, UnitaryRep.ccToL1 ν (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    unfold UnitaryRep.ccToL1
    exact MemLp.toLp_zero _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    unfold UnitaryRep.ccToL1
    rw [← MemLp.toLp_add]
    rfl

private theorem integrated_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {G ι : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
    (ν : Measure G) [IsFiniteMeasureOnCompacts ν] (π : UnitaryRep G H) (s : Finset ι) (a : ι → ℂ)
    (f : ι → CompactlySupportedContinuousMap G ℂ) :
    π.integrated ν (UnitaryRep.ccToL1 ν (∑ i ∈ s, a i • f i)) = ∑ i ∈ s, a i • π.integrated ν (UnitaryRep.ccToL1 ν (f i)) := by
  rw [ccToL1_finsetSum, map_sum]
  simp only [ccToL1_smul, map_smul]

private theorem Ofin_sum {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] {ι : Type*} (s : Finset ι) (a : ι → ℂ) (f : ι → TF K n) :
    Ofin μ m (∑ i ∈ s, a i • f i) = ∑ i ∈ s, a i • Ofin μ m (f i) :=
  integrated_sum m ((rightRegularRep (rationalGLOne K n) μ).compHom (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj) s a f

private theorem rhoF_comp_Ofin {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] (y : AdelicGLn.FiniteAdelicGL K n) (e : TF K n) :
    rhoF μ y ∘L Ofin μ m e = Ofin μ m (trCc y e) := by
  refine ContinuousLinearMap.ext fun v => ?_
  exact map_integrated_trCc m
    ((rightRegularRep (rationalGLOne K n) μ).compHom (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj) y e v

private theorem cf_local {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (y : GL (Fin n) (w.adicCompletion K))
    (x : AdelicGLn.FiniteAdelicGL K n) : cf w (AdelicGLn.localEmbedding w y * x) = y * cf w x := by
  unfold cf
  rw [map_mul, finAt_mul, (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.1]

private theorem exists_cover {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G)
    (hJ : IsOpen (J : Set G)) (h : G → ℂ) (hc : HasCompactSupport h) :
    ∃ t : Finset (G ⧸ J), ∀ y, h y ≠ 0 → (QuotientGroup.mk y : G ⧸ J) ∈ t := by
  have hop : ∀ c : G ⧸ J, IsOpen ((QuotientGroup.mk : G → G ⧸ J) ⁻¹' {c}) := fun c => by
    have : (QuotientGroup.mk : G → G ⧸ J) ⁻¹' {c} = (fun g => c.out⁻¹ * g) ⁻¹' (J : Set G) := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      exact eq_comm
    rw [this]
    exact hJ.preimage (continuous_const_mul _)
  obtain ⟨t, ht⟩ := hc.isCompact.elim_finite_subcover _ hop fun y _ =>
    Set.mem_iUnion.2 ⟨QuotientGroup.mk y, rfl⟩
  refine ⟨t, fun y hy => ?_⟩
  obtain ⟨c, hc', hyc⟩ := Set.mem_iUnion₂.1 (ht (subset_tsupport _ hy))
  rw [show (QuotientGroup.mk y : G ⧸ J) = c from hyc]
  exact hc'

private theorem coset_sum {G : Type*} [Group G] (J : Subgroup G) (h : G → ℂ) (hinv : ∀ k ∈ J, ∀ x, h (x * k) = h x)
    (t : Finset (G ⧸ J)) (ht : ∀ y, h y ≠ 0 → (QuotientGroup.mk y : G ⧸ J) ∈ t) (y : G) :
    ∑ c ∈ t, h c.out * (J : Set G).indicator (1 : G → ℂ) (c.out⁻¹ * y) = h y := by
  classical
  have hind : ∀ c : G ⧸ J, (J : Set G).indicator (1 : G → ℂ) (c.out⁻¹ * y) = if (QuotientGroup.mk y : G ⧸ J) = c then 1 else 0 := fun c => by
    have : c.out⁻¹ * y ∈ (J : Set G) ↔ (QuotientGroup.mk y : G ⧸ J) = c := by
      rw [SetLike.mem_coe, ← QuotientGroup.eq, QuotientGroup.out_eq']
      exact eq_comm
    by_cases hh : (QuotientGroup.mk y : G ⧸ J) = c
    · rw [if_pos hh, Set.indicator_of_mem (this.2 hh)]; rfl
    · rw [if_neg hh, Set.indicator_of_notMem (fun q => hh (this.1 q))]
  have hout : h (QuotientGroup.mk y : G ⧸ J).out = h y := by
    have hk : (QuotientGroup.mk y : G ⧸ J).out⁻¹ * y ∈ J := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    have := hinv _ hk (QuotientGroup.mk y : G ⧸ J).out
    rw [mul_inv_cancel_left] at this
    exact this.symm
  simp only [hind, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hm
  · exact hout
  · by_contra hne
    exact hm (ht y (Ne.symm hne))

theorem UpperTheory.ConvolutionTheory.GM.stepFin :
    StepFin := by
  intro K _ _ n hn μ _ m _ w J hJ h hc hinv r hr e₀ e₁ h0 h1
  have htr : ∀ (y : GL (Fin n) (w.adicCompletion K)) x,
      trCc (AdelicGLn.localEmbedding w y) e₀ x =
        r x * (J : Set _).indicator 1 (y⁻¹ * cf w x) := fun y x => by
    show e₀ ((AdelicGLn.localEmbedding w y)⁻¹ * x) = _
    rw [h0, ← map_inv, hr, cf_local]
  refine ⟨fun u => ?_, ?_⟩
  · refine ((UpperTheory.ConvolutionTheory.Tf.commPrj K n μ _).2.1 _).2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have e : trCc (AdelicGLn.localEmbedding w k) e₀ = e₀ := by
      ext x
      rw [htr, h0]
      congr 1
      by_cases hx : cf w x ∈ (J : Set _)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (J.mul_mem (J.inv_mem hk) hx)]; rfl
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem]
        intro q
        exact hx (by simpa using J.mul_mem hk q)
    have := congrArg (fun A : LL μ →L[ℂ] LL μ => A u) (rhoF_comp_Ofin μ m (AdelicGLn.localEmbedding w k) e₀)
    simpa [e] using this
  · obtain ⟨t, ht⟩ := exists_cover J hJ h hc
    have hfs : (∑ᶠ c : GL (Fin n) (w.adicCompletion K) ⧸ J, h c.out • rhoL μ w c.out) = ∑ c ∈ t, h c.out • rhoL μ w c.out := by
      refine finsum_eq_sum_of_support_subset _ fun c hc' => ?_
      have hne : h c.out ≠ 0 := fun q => hc' (by simp [q])
      have := ht _ hne
      rwa [QuotientGroup.out_eq'] at this
    have he : e₁ = ∑ c ∈ t, h c.out • trCc (AdelicGLn.localEmbedding w c.out) e₀ := by
      ext x
      rw [h1, CompactlySupportedContinuousMap.sum_apply]
      simp only [CompactlySupportedContinuousMap.smul_apply, htr, smul_eq_mul]
      rw [← coset_sum J h hinv t ht (cf w x), Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [hfs, he]
    rw [Ofin_sum]
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← rhoF_comp_Ofin]
    rfl
