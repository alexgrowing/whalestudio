import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.TensF
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.PrjFix
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LeftSm
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopLevel
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CompatEx
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RrTens
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.InnerOps
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.UiwPow
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.StepFin
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.InvSmooth
import Development.AutomorphicArithmetic.AdelicGluing.LevFIsOpenIsCompactLeIntegral
import Development.AutomorphicArithmetic.AdelicGluing.ExistsOpenSubgroupRightInvariantFiniteAdelicGL
import Development.AutomorphicArithmetic.AdelicGluing.RhoFCompOfinOfLeftInvariant
import Development.AutomorphicArithmetic.AdelicGluing.OfinDoubleCosetIndicatorEqHop
import Development.AutomorphicArithmetic.AdelicGluing.FactorizableFinprodEqAwayFinprodMulLocalFactor

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped ComplexConjugate
open scoped ContDiff Manifold Pointwise

private theorem star_cc {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (e : CompactlySupportedContinuousMap G ℂ) :
    ∃ e' : CompactlySupportedContinuousMap G ℂ, ∀ h, e' h = conj (e h⁻¹) := by
  have hc : Continuous fun h : G => conj (e h⁻¹) :=
    Complex.continuous_conj.comp (e.continuous.comp continuous_inv)
  have hs : HasCompactSupport fun h : G => conj (e h⁻¹) :=
    (e.hasCompactSupport.comp_homeomorph (Homeomorph.inv G)).comp_left (g := fun z : ℂ => conj z) (map_zero _)
  exact ⟨⟨⟨_, hc⟩, hs⟩, fun _ => rfl⟩

private theorem cf_mul {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (a b : AdelicGLn.FiniteAdelicGL K n) :
    cf w (a * b) = cf w a * cf w b := by
  simp only [cf, map_mul, finAt_mul]

private theorem cf_inv {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) (a : AdelicGLn.FiniteAdelicGL K n) :
    cf w a⁻¹ = (cf w a)⁻¹ := by
  simp only [cf, map_inv, finAt_inv]

private theorem dc_fwd {G : Type} [Group G] (U : Subgroup G) (y z : G) (hz : z⁻¹ ∈ (U : Set G) * {y⁻¹} * (U : Set G)) :
    z ∈ (U : Set G) * {y} * (U : Set G) := by
  obtain ⟨p, hp, b, hb, h⟩ := Set.mem_mul.1 hz
  obtain ⟨a, ha, y', hy', rfl⟩ := Set.mem_mul.1 hp
  rw [Set.mem_singleton_iff] at hy'
  subst hy'
  refine Set.mem_mul.2 ⟨b⁻¹ * y, Set.mem_mul.2 ⟨b⁻¹, inv_mem hb, y, rfl, rfl⟩, a⁻¹, inv_mem ha, ?_⟩
  rw [← inv_inj, ← h]
  group

private theorem dc_inv {G : Type} [Group G] (U : Subgroup G) (y z : G) :
    z⁻¹ ∈ (U : Set G) * {y⁻¹} * (U : Set G) ↔ z ∈ (U : Set G) * {y} * (U : Set G) := by
  refine ⟨dc_fwd U y z, fun h => ?_⟩
  refine dc_fwd U y⁻¹ z⁻¹ ?_
  simpa using h

private theorem comm_abs {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Submodule ℂ H}
    (A B E E' X Y : H →L[ℂ] H) (Z : H →L[ℂ] H)
    (hAB : ContinuousLinearMap.adjoint A = B) (hEE : ContinuousLinearMap.adjoint E = E')
    (h1 : E = X ∘L A) (h2 : E' = Y ∘L B) (hc : X * prj V = prj V * X)
    (h4 : ContinuousLinearMap.adjoint (Y ∘L prj V) = X ∘L prj V) (hPB : prj V ∘L B = B) :
    Commute A X := by
  have hsa : ContinuousLinearMap.adjoint (prj V) = prj V := (isSelfAdjoint_starProjection _).adjoint_eq
  have hAP : A ∘L prj V = A := by
    have := congrArg ContinuousLinearMap.adjoint hPB
    rw [ContinuousLinearMap.adjoint_comp, hsa, ← hAB, ContinuousLinearMap.adjoint_adjoint] at this
    exact this
  have h3 : E = A ∘L ContinuousLinearMap.adjoint Y := by
    have := congrArg ContinuousLinearMap.adjoint h2
    rw [← hEE, ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.adjoint_comp, ← hAB,
      ContinuousLinearMap.adjoint_adjoint] at this
    exact this
  have h5 : prj V ∘L ContinuousLinearMap.adjoint Y = X ∘L prj V := by
    rw [ContinuousLinearMap.adjoint_comp, hsa] at h4
    exact h4
  have hc' : X ∘L prj V = prj V ∘L X := hc
  have hfin : X ∘L A = A ∘L X := by
    calc X ∘L A = A ∘L ContinuousLinearMap.adjoint Y := h1.symm.trans h3
      _ = (A ∘L prj V) ∘L ContinuousLinearMap.adjoint Y := by rw [hAP]
      _ = A ∘L (X ∘L prj V) := by rw [ContinuousLinearMap.comp_assoc, h5]
      _ = (A ∘L prj V) ∘L X := by rw [hc', ContinuousLinearMap.comp_assoc]
      _ = A ∘L X := by rw [hAP]
  exact hfin.symm

private theorem hopComm {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
    (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (x : GL (Fin n) (w.adicCompletion K))
    (hJo : IsOpen (J : Set (GL (Fin n) (w.adicCompletion K)))) (hJc : IsCompact (J : Set (GL (Fin n) (w.adicCompletion K))))
    (r : AdelicGLn.FiniteAdelicGL K n → ℂ) (hl : Free w r)
    (hr : ∀ y z, r (z * AdelicGLn.localEmbedding w y) = r z) (e E : TF K n)
    (he : ∀ z, e z = r z * (J : Set (GL (Fin n) (w.adicCompletion K))).indicator 1 (cf w z))
    (hE : ∀ z, E z = r z * {g : GL (Fin n) (w.adicCompletion K) | ∃ a ∈ J, ∃ b ∈ J, g = a * x * b}.indicator 1 (cf w z))
    (U : Subgroup (AdelicGLn.FiniteAdelicGL K n)) (hUo : IsOpen (U : Set (AdelicGLn.FiniteAdelicGL K n)))
    (hUc : IsCompact (U : Set (AdelicGLn.FiniteAdelicGL K n)))
    (hJU : J.map (AdelicGLn.localEmbedding w) ≤ U) (hUJ : ∀ u ∈ U, finAt w (finEmb K n u) ∈ J)
    (hUi : ∀ u ∈ U, ∀ z, e (z * u) = e z) :
    Commute (Ofin μ m e) (Hop μ w J x) := by
  classical
  obtain ⟨e', he'⟩ := star_cc e
  obtain ⟨E', hE'⟩ := star_cc E
  have adj := (UpperTheory.ConvolutionTheory.Tf.opAlg K n μ ν m).2.2.2.2.1
  let r' : AdelicGLn.FiniteAdelicGL K n → ℂ := fun z => conj (r z⁻¹)
  have hl' : Free w r' := fun y z => by
    show conj (r (AdelicGLn.localEmbedding w y * z)⁻¹) = conj (r z⁻¹)
    rw [mul_inv_rev, ← map_inv, hr]
  have he'f : ∀ z, e' z = r' z * (J : Set (GL (Fin n) (w.adicCompletion K))).indicator 1 (cf w z) := fun z => by
    rw [he', he, map_mul, cf_inv]
    congr 1
    by_cases h : cf w z ∈ J
    · rw [Set.indicator_of_mem (show (cf w z)⁻¹ ∈ (J : Set _) from inv_mem h),
        Set.indicator_of_mem (show cf w z ∈ (J : Set _) from h)]
      simp
    · rw [Set.indicator_of_notMem (show (cf w z)⁻¹ ∉ (J : Set _) from fun h' => h (by simpa using inv_mem h')),
        Set.indicator_of_notMem (show cf w z ∉ (J : Set _) from h)]
      simp
  have hE'f : ∀ z, E' z = r' z * {g : GL (Fin n) (w.adicCompletion K) | ∃ a ∈ J, ∃ b ∈ J, g = a * x⁻¹ * b}.indicator 1 (cf w z) := fun z => by
    rw [hE', hE, map_mul, cf_inv]
    congr 1
    have key : (cf w z)⁻¹ ∈ {g : GL (Fin n) (w.adicCompletion K) | ∃ a ∈ J, ∃ b ∈ J, g = a * x * b} ↔
        cf w z ∈ {g : GL (Fin n) (w.adicCompletion K) | ∃ a ∈ J, ∃ b ∈ J, g = a * x⁻¹ * b} := by
      constructor
      · rintro ⟨a, ha, b, hb, h⟩
        refine ⟨b⁻¹, inv_mem hb, a⁻¹, inv_mem ha, ?_⟩
        rw [← inv_inj, h]
        group
      · rintro ⟨a, ha, b, hb, h⟩
        refine ⟨b⁻¹, inv_mem hb, a⁻¹, inv_mem ha, ?_⟩
        rw [h]
        group
    by_cases h : (cf w z)⁻¹ ∈ {g : GL (Fin n) (w.adicCompletion K) | ∃ a ∈ J, ∃ b ∈ J, g = a * x * b}
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (key.1 h)]
      simp
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (key.2 h'))]
      simp
  have h1 : Ofin μ m E = Hop μ w J x ∘L Ofin μ m e :=
    UpperTheory.Ofin_doubleCoset_indicator_eq_Hop K n hn μ m w J x hJo hJc r hl e E he hE
  have h2 : Ofin μ m E' = Hop μ w J x⁻¹ ∘L Ofin μ m e' :=
    UpperTheory.Ofin_doubleCoset_indicator_eq_Hop K n hn μ m w J x⁻¹ hJo hJc r' hl' e' E' he'f hE'f
  have hAB : ContinuousLinearMap.adjoint (Ofin μ m e) = Ofin μ m e' := adj e e' he'
  have hEE : ContinuousLinearMap.adjoint (Ofin μ m E) = Ofin μ m E' := adj E E' hE'
  obtain ⟨hc, ξ, hξ, hξo⟩ := UpperTheory.ConvolutionTheory.Tf.hopLevel K n μ m w J x U hJo hJc hUo hUc hJU hUJ
  obtain ⟨-, ξ', hξ', hξo'⟩ := UpperTheory.ConvolutionTheory.Tf.hopLevel K n μ m w J x⁻¹ U hJo hJc hUo hUc hJU hUJ
  have hξs : ∀ z, ξ z = conj (ξ' z⁻¹) := fun z => by
    rw [hξ, hξ', map_inv]
    by_cases h : z ∈ (U : Set (AdelicGLn.FiniteAdelicGL K n)) * {AdelicGLn.localEmbedding w x} * (U : Set (AdelicGLn.FiniteAdelicGL K n))
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((dc_inv U _ z).2 h)]
      simp
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((dc_inv U _ z).1 h'))]
      simp
  have h4 : ContinuousLinearMap.adjoint (Ofin μ m ξ') = Ofin μ m ξ := adj ξ' ξ hξs
  rw [hξo, hξo'] at h4
  have hcp := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ U
  have hPB : prj (fixF μ U) ∘L Ofin μ m e' = Ofin μ m e' := by
    refine ContinuousLinearMap.ext fun v => ?_
    refine hcp.2.2.2.1 _ ((hcp.2.1 _).2 fun u hu => ?_)
    have := UpperTheory.rhoF_comp_Ofin_of_left_invariant K n μ m e' u (fun z => by
      rw [he', he', mul_inv_rev, hUi _ (inv_mem hu)])
    exact congrArg (fun T : LL μ →L[ℂ] LL μ => T v) this
  exact comm_abs (H := LL μ) (V := fixF μ U) _ _ _ _ _ _ 0 hAB hEE h1 h2 hc.eq h4 hPB

private theorem smooth_star {K : Type} [Field K] [NumberField K] {n : ℕ} (β β' : TI K n)
    (h : ∀ a, β' a = conj (β a⁻¹)) (hb : SmoothT β) : SmoothT β' := by
  have h0 := (UpperTheory.ConvolutionTheory.Tf.invSmooth K n (fun g => β g) hb).1
  have h1 : (isExpLieAlgebra K n).IsSmoothFun (fun g => β g⁻¹) := h0
  have hf : (fun g => β' g) = fun g => (Complex.conjCLE : ℂ →L[ℝ] ℂ) (β g⁻¹) := funext h
  unfold SmoothT
  rw [hf]
  letI := (isExpLieAlgebra K n).chartedSpace
  exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contMDiff h1

private theorem iw_zero {K : Type} [Field K] [NumberField K] {n : ℕ} (w : Pl K) :
    iwCoset w (0 : Fin n → ℤ) = (GLnLocal.iwahori (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K))) := by
  have h1 : Cartan.diagPow (w.adicCompletion K) n (0 : Fin n → ℤ) = 1 := by
    apply Units.ext
    rw [Cartan.coe_diagPow]
    simp
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [h1, mul_one]
    exact mul_mem ha hb
  · intro hg
    exact ⟨g, hg, 1, one_mem _, by rw [h1]; simp⟩

private theorem dc_test {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (J : Subgroup G)
    (hJo : IsOpen (J : Set G)) (hJc : IsCompact (J : Set G)) (y : G) :
    IsLocallyConstant ({g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b}.indicator (1 : G → ℂ)) ∧
      HasCompactSupport ({g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b}.indicator (1 : G → ℂ)) := by
  have hset : {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b} = (fun p : G × G => p.1 * y * p.2) '' ((J : Set G) ×ˢ (J : Set G)) := by
    ext g
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  have hc : IsCompact {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b} := by
    rw [hset]
    exact (hJc.prod hJc).image (by fun_prop)
  have ho : IsOpen {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b} := by
    have : {g : G | ∃ a ∈ J, ∃ b ∈ J, g = a * y * b} = ⋃ a ∈ J, (fun b => a * y * b) '' (J : Set G) := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, SetLike.mem_coe, exists_prop]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨a, ha, b, hb, rfl⟩
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨a, ha, b, hb, rfl⟩
    rw [this]
    exact isOpen_biUnion fun a _ => (Homeomorph.mulLeft (a * y)).isOpenMap _ hJo
  refine ⟨?_, ?_⟩
  · exact (LocallyConstant.indicator (⟨(1 : G → ℂ), IsLocallyConstant.const 1⟩ : LocallyConstant G ℂ) ⟨hc.isClosed, ho⟩).isLocallyConstant
  · exact HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _

theorem UpperTheory.ConvolutionTheory.GM.sideF : SideF := by
  classical
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ q w₀ νF _ aF hA L ν
  set I := GLnLocal.iwahori (q.adicCompletion F) n with hI
  have hIo : IsOpen (I : Set (GL (Fin n) (q.adicCompletion F))) := GLnLocal.isOpen_iwahori _ _
  have hIc : IsCompact (I : Set (GL (Fin n) (q.adicCompletion F))) := GLnLocal.isCompact_iwahori _ _
  obtain ⟨hfq, hUq⟩ : L.f q = (iwCoset q 0).indicator 1 ∧ L.UF q = I := ⟨L.at_q.2.1, L.at_q.2.2.2⟩
  let S' : Finset (Pl F) := insert q L.S
  have hS' : ∀ v, v ∉ S' → v ∉ L.S ∧ v ≠ q := fun v hv => by
    simp only [S', Finset.mem_insert, not_or] at hv
    exact ⟨hv.2, hv.1⟩
  obtain ⟨hUo, hUc, hUle, hUmap⟩ := UpperTheory.levF_isOpen_isCompact_le_integral F n L.UF S'
    (fun v hv => by
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [hUq]; exact ⟨hIo, GLnLocal.iwahori_le_integralGL _ _⟩
      · exact ⟨(L.lev v hv).2.2.1, (L.lev v hv).2.2.2⟩)
    (fun v hv => (L.off v (hS' v hv).1 (hS' v hv).2).2.2.2)
  obtain ⟨m, hm, hC⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx F n hn).2.1 μ νF
  obtain ⟨e₀, he₀, he₀o⟩ := UpperTheory.ConvolutionTheory.Tf.prjFix F n μ m (levF L.UF) hUo hUc

  have hdc : ∀ ν' : Fin n → ℤ, IsLocallyConstant ((iwCoset q ν').indicator (1 : GL (Fin n) (q.adicCompletion F) → ℂ)) ∧ HasCompactSupport ((iwCoset q ν').indicator (1 : GL (Fin n) (q.adicCompletion F) → ℂ)) :=
    fun ν' => dc_test I hIo hIc _
  have hf : ∀ v ∈ S', IsLocallyConstant (L.f v) ∧ HasCompactSupport (L.f v) := fun v hv => by
    rcases Finset.mem_insert.1 hv with rfl | hv
    · rw [hfq]; exact hdc 0
    · exact ⟨(L.test v hv).2.2.1, (L.test v hv).2.2.2⟩
  have hoff : ∀ v, v ∉ S' → L.f v = (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1 :=
    fun v hv => (L.off v (hS' v hv).1 (hS' v hv).2).2.1
  let f₁ : ∀ v : Pl F, GL (Fin n) (v.adicCompletion F) → ℂ := Function.update L.f q ((iwCoset q ν).indicator 1)
  have hf₁q : f₁ q = (iwCoset q ν).indicator 1 := Function.update_self ..
  have hf₁ne : ∀ v, v ≠ q → f₁ v = L.f v := fun v hv => Function.update_of_ne hv ..
  have hoff₁ : ∀ v, v ∉ S' → f₁ v = (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1 :=
    fun v hv => by rw [hf₁ne v (hS' v hv).2]; exact hoff v hv
  obtain ⟨eg, hegc, hegf, hegt⟩ := UpperTheory.ConvolutionTheory.GM.avgF F n hn S' aF L.f hf hoff
  obtain ⟨E₁, -, hE₁f, -⟩ := UpperTheory.ConvolutionTheory.GM.avgF F n hn S' aF f₁
    (fun v hv => by
      by_cases hvq : v = q
      · subst hvq; rw [hf₁q]; exact hdc ν
      · rw [hf₁ne v hvq]; exact hf v hv) hoff₁
  let r : AdelicGLn.FiniteAdelicGL F n → ℂ := fun z => ∏ᶠ v, if v = q then (1 : ℂ) else L.f v (cf v z)
  have hegr : ∀ z, eg z = r z * (I : Set (GL (Fin n) (q.adicCompletion F))).indicator 1 (cf q z) := fun z => by
    rw [hegf, UpperTheory.factorizable_finprod_eq_away_finprod_mul_local_factor F n L.f S' hoff q z, hfq, iw_zero]
  have hE₁r : ∀ z, E₁ z = r z * {g : GL (Fin n) (q.adicCompletion F) | ∃ a ∈ I, ∃ b ∈ I, g = a * Cartan.diagPow (q.adicCompletion F) n ν * b}.indicator 1 (cf q z) := fun z => by
    rw [hE₁f, UpperTheory.factorizable_finprod_eq_away_finprod_mul_local_factor F n f₁ S' hoff₁ q z, hf₁q]
    congr 1
    refine finprod_congr fun v => ?_
    by_cases hv : v = q
    · simp [hv]
    · simp [hv, hf₁ne v hv]
  have hloc := UpperTheory.ConvolutionTheory.Tf.locEmb F n q
  have cfl : ∀ v, v ≠ q → ∀ y, cf v (AdelicGLn.localEmbedding q y : AdelicGLn.FiniteAdelicGL F n) = 1 := fun v hv y => hloc.2.2.1 v hv y
  have cfq : ∀ y : GL (Fin n) (q.adicCompletion F), cf q (AdelicGLn.localEmbedding q y : AdelicGLn.FiniteAdelicGL F n) = y := hloc.2.1
  have hrl : Free q r := fun y z => finprod_congr fun v => by
    by_cases hv : v = q
    · simp [hv]
    · simp only [hv, if_false, cf_mul, cfl v hv, one_mul]
  have hrr : ∀ y z, r (z * AdelicGLn.localEmbedding q y) = r z := fun y z => finprod_congr fun v => by
    by_cases hv : v = q
    · simp [hv]
    · simp only [hv, if_false, cf_mul, cfl v hv, mul_one]
  obtain ⟨W, hWo, hWi⟩ := UpperTheory.exists_open_subgroup_rightInvariant_finiteAdelicGL F n eg hegc

  let St : Subgroup (AdelicGLn.FiniteAdelicGL F n) :=
    { carrier := {k | ∀ x, eg (x * k) = eg x}
      one_mem' := fun x => by rw [mul_one]
      mul_mem' := fun {a b} ha hb x => by rw [← mul_assoc, hb, ha]
      inv_mem' := fun {a} ha x => by
        have := ha (x * a⁻¹)
        rw [inv_mul_cancel_right] at this
        exact this.symm }
  have hSt : ∀ k, k ∈ St ↔ ∀ x, eg (x * k) = eg x := fun k => Iff.rfl
  have hU'o : IsOpen ((St ⊓ levF L.UF : Subgroup _) : Set (AdelicGLn.FiniteAdelicGL F n)) :=
    Subgroup.isOpen_mono (H₁ := W ⊓ levF L.UF) (inf_le_inf_right _ fun k hk => hWi k hk) (hWo.inter hUo)
  have hU'c : IsCompact ((St ⊓ levF L.UF : Subgroup _) : Set (AdelicGLn.FiniteAdelicGL F n)) :=
    hUc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hU'o) (fun _ h => h.2)
  have hIU : I.map (AdelicGLn.localEmbedding q) ≤ St ⊓ levF L.UF := by
    refine le_inf ?_ (hUmap q I hUq.ge)
    rintro _ ⟨k, hk, rfl⟩ x
    rw [hegr, hegr, hrr, cf_mul, cfq]
    congr 1
    by_cases h : cf q x ∈ I
    · rw [Set.indicator_of_mem (show cf q x * k ∈ (I : Set _) from mul_mem h hk), Set.indicator_of_mem (show cf q x ∈ (I : Set _) from h)]
      rfl
    · rw [Set.indicator_of_notMem (show cf q x * k ∉ (I : Set _) from fun h' => h (by simpa using mul_mem h' (inv_mem hk))),
        Set.indicator_of_notMem (show cf q x ∉ (I : Set _) from h)]
  have hcomF : Commute (Ofin μ m eg) (Uiw μ q ν) :=
    hopComm hn μ νF m q I _ hIo hIc r hrl hrr eg E₁ hegr hE₁r (St ⊓ levF L.UF) hU'o hU'c hIU
      (fun u hu => by
        have := hu.2 q
        rw [hUq] at this
        exact this)
      (fun u hu z => hu.1 z)
  have hopA := UpperTheory.ConvolutionTheory.Tf.opAlg F n μ νF m
  have hhb := fun x => (UpperTheory.ConvolutionTheory.Tf.hopBasic F n μ q I x hIo hIc).2.2.2.2.1
  have hcomI : ∀ β : TI F n, Commute (Oinf μ νF β) (Uiw μ q ν) := fun β =>
    hhb _ _ fun g => hopA.2.2.2.2.2.2.2.2 β _
  have hcomP : Commute (Uiw μ q ν) (prj (fixF μ (levF L.UF))) :=
    (UpperTheory.ConvolutionTheory.Tf.hopLevel F n μ m q I _ (levF L.UF) hIo hIc hUo hUc (hUmap q I hUq.ge)
      (fun u hu => by
        have := hu q
        rw [hUq] at this
        exact this)).1
  have hrrT := UpperTheory.ConvolutionTheory.Tf.rrTens F n hn μ νF m hC
  have hop_a : Rop μ (tens aF e₀) = Oinf μ νF aF ∘L prj (fixF μ (levF L.UF)) := by
    have := hrrT aF e₀
    rw [he₀o] at this
    exact this
  have hop_g : Rop μ (tens aF eg) = Oinf μ νF aF ∘L Ofin μ m eg := hrrT aF eg
  have hcomG : Commute (Rop μ (tens aF eg)) (Uiw μ q ν) := by
    rw [hop_g]
    exact (hcomI aF).mul_left hcomF
  have hsm := UpperTheory.ConvolutionTheory.Tf.leftSm F n hn aF
  obtain ⟨β', hβ'⟩ := star_cc aF
  obtain ⟨e', he'⟩ := star_cc eg
  have hgs : IsLeftSmooth (CuspidalProjection.ccStar (tens aF eg)) := by
    rw [(hsm eg).2 β' e' hβ' he']
    refine (UpperTheory.ConvolutionTheory.Tf.leftSm F n hn β' e').1 (smooth_star aF β' hβ' hA.1) ⟨W, hWo, fun u hu h => ?_⟩
    rw [he', he', mul_inv_rev, hWi _ (inv_mem hu)]
  have has : IsLeftSmooth (tens aF e₀) := (hsm e₀).1 hA.1 ⟨levF L.UF, hUo, fun u hu h => by
    rw [he₀, he₀]
    by_cases hh : h ∈ levF L.UF
    · rw [Set.indicator_of_mem (show u * h ∈ (levF L.UF : Set _) from mul_mem hu hh), Set.indicator_of_mem (show h ∈ (levF L.UF : Set _) from hh)]
    · rw [Set.indicator_of_notMem (show u * h ∉ (levF L.UF : Set _) from fun h' => hh (by simpa using mul_mem (inv_mem hu) h')),
        Set.indicator_of_notMem (show h ∉ (levF L.UF : Set _) from hh)]⟩
  have hinner : Inner μ (Uiw μ q ν) := fun V hV hVi =>
    (UpperTheory.ConvolutionTheory.Tf.innerOps F n μ).2.2.2.2.2 q I _ hIo hIc V hV hVi
  refine ⟨{ ν := νF, a₀ := aF, smooth := hA.1, fin := hA.2.1, S := (S' : Set (Pl F)), finS := S'.finite_toSet,
            U := levF L.UF, le := hUle, isOpen := hUo,
            max := fun w hw => hUmap w _ (by
              have hw' : w ∉ S' := fun h => hw h
              exact (L.off w (hS' w hw').1 (hS' w hw').2).2.2.2.ge),
            pos := hA.2.2.1, norm_le := hA.2.2.2,
            a := tens aF e₀, a_op := hop_a, a_smooth := has, g := tens aF eg, g_smooth := hgs,
            Uq := fun _ => Uiw μ q ν, Uq_inner := fun _ => hinner, Uq_comm := fun _ _ => Commute.refl _,
            Uq_amp := fun _ => ?_, Uq_perm := fun _ => ?_ }, rfl, rfl, ?_, rfl, hegt, rfl⟩
  · have h1 := (hcomI aF).symm
    exact h1.mul_right hcomP
  · have h2 : Rop μ (tens aF eg) ∘L Uiw μ q ν = Uiw μ q ν ∘L Rop μ (tens aF eg) := hcomG.eq
    exact h2
  · intro v
    simp [S']
    tauto
