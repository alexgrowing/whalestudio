import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.HodgeTateFromSandwich

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.GJStandardL GroundTheory.Automorphic.GodementJacquet
open GroundTheory.Automorphic.GLnLocal
open scoped SchwartzMap Classical

noncomputable section

namespace UpperTheory.V.Z.Inf.Bridge

open NumberField.mixedEmbedding GroundTheory.Automorphic.GJMatrix GroundTheory.Global

variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ)

private theorem hms_infEq (x : Cinf K) : homeomorphMixedSpace K (infEq K x) = Cm.mixEq K x :=
  homeomorphMixedSpace_apply K _

private theorem coe_infEq : ⇑(infEq K) = (homeomorphMixedSpace K).symm ∘ Cm.mixEq K := by
  funext x
  rw [Function.comp_apply, ← hms_infEq, Homeomorph.symm_apply_apply]

private theorem coe_infEq_symm : ⇑(infEq K).symm = (Cm.mixEq K).symm ∘ homeomorphMixedSpace K := by
  funext x
  obtain ⟨y, rfl⟩ := (infEq K).surjective x
  rw [Function.comp_apply, hms_infEq, RingEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]

private def matC : Matrix (Fin n) (Fin n) (Cinf K) ≃ₜ* Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) :=
  { (infEq K).mapMatrix.toMulEquiv with
    continuous_toFun := by
      refine Continuous.matrix_map (f := infEq K) continuous_id ?_
      rw [coe_infEq]
      exact (homeomorphMixedSpace K).symm.continuous.comp
        (Cm.mixEq K).toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
    continuous_invFun := by
      refine Continuous.matrix_map (f := (infEq K).symm) continuous_id ?_
      rw [coe_infEq_symm]
      exact (Cm.mixEq K).symm.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional.comp
        (homeomorphMixedSpace K).continuous }

private def grpC : GL (Fin n) (Cinf K) ≃ₜ* AdelicGLn.InfiniteAdelicGL K n :=
  Units.mapContinuousMulEquiv (matC K n)

private theorem archComp_infGL (y : GL (Fin n) (Cinf K)) : archComp K n (infGL K n y) = grpC K n y := by
  refine Units.ext ?_
  rw [coe_archComp]
  exact Matrix.ext fun i j => Cm.infGL_entry y i j

private theorem symm_archComp (y : GL (Fin n) (Cinf K)) :
    (AdelicGLn.prodEquiv K n).symm (archComp K n (infGL K n y), 1) = infGL K n y := by
  rw [ContinuousMulEquiv.symm_apply_eq]
  exact Prod.ext rfl (pFin_infGL y).symm

private theorem archAbsDet_grpC (y : GL (Fin n) (Cinf K)) : archAbsDet (grpC K n y) = nrm (toL y.val) := by
  unfold archAbsDet nrm
  refine Finset.prod_congr rfl fun w _ => ?_
  have h : ((grpC K n y).val).det = infEq K (y.val).det := ((infEq K).map_det y.val).symm
  rw [h, Cm.infEq_apply, InfinitePlace.mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩]
  congr 1
  have := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)
    ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm (y.val.det w))
  rw [← this]
  exact congrArg _ ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).apply_symm_apply _)

private def linC : Lie K n ≃L[ℝ] (Fin n × Fin n → mixedSpace K) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x p => Cm.mixEq K (x p.1 p.2)
      invFun := fun z i j => (Cm.mixEq K).symm (z (i, j))
      map_add' := fun x y => funext fun p => map_add (Cm.mixEq K) _ _
      map_smul' := fun c x => funext fun p => map_smul (Cm.mixEq K) c _
      left_inv := fun x => funext fun i => funext fun j => (Cm.mixEq K).symm_apply_apply _
      right_inv := fun z => funext fun p => (Cm.mixEq K).apply_symm_apply _ }

private theorem archSchwartz_grpC (φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ)) (y : GL (Fin n) (Cinf K)) :
    archSchwartz φ (grpC K n y).val = φ (linC K n (toL y.val)) :=
  congrArg φ (funext fun p => hms_infEq K _)

private theorem trace_mixEq (x : Cinf K) : mixedTrace K (Cm.mixEq K x) = 2 * ∑ w, (x w).re := by
  haveI : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2⟩
  rw [mixedTrace_apply, Finset.univ_eq_empty, Finset.sum_empty, zero_add, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.subtypeUnivEquiv (IsTotallyComplex.isComplex (K := K))) _ _ fun w => ?_
  exact congrArg (fun z : ℂ => 2 * z.re) (Cm.mixRing_snd x w)

private theorem pairing (x y : Lie K n) :
    mixedPairingPi K (linC K n x) (swapCLE K n (linC K n y)) = 2 * ∑ w, ((Matrix.of x * Matrix.of y).trace w).re := by
  rw [← trace_mixEq, trace_mul_eq_sum, map_sum, map_sum, mixedPairingPi]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [mixedTraceForm_apply, map_mul (Cm.mixEq K)]
  rfl

private theorem vol_haar : (volume : Measure (Lie K n)).IsAddHaarMeasure := by
  haveI : (volume : Measure (Cinf K)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Fin n → Cinf K)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

private theorem four_eq : ∃ c' : ℂ, c' ≠ 0 ∧ ∀ (φ : 𝓢(Fin n × Fin n → mixedSpace K, ℂ)) (y : Lie K n),
    archMatrixFourier φ (linC K n y) = c' * four (-4 * Real.pi) (fun x => φ (linC K n x)) y := by
  haveI := vol_haar K n
  haveI : (Measure.map (linC K n) (volume : Measure (Lie K n))).IsAddHaarMeasure :=
    (linC K n).isAddHaarMeasure_map _
  set ν := Measure.map (linC K n) (volume : Measure (Lie K n)) with hν
  have h := Measure.isAddLeftInvariant_eq_smul (mixedMeasurePi K : Measure (Fin n × Fin n → mixedSpace K)) ν
  have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
    (mixedMeasurePi K : Measure (Fin n × Fin n → mixedSpace K)) ν
  generalize Measure.addHaarScalarFactor (mixedMeasurePi K : Measure (Fin n × Fin n → mixedSpace K)) ν = c at h hpos
  refine ⟨((c : ℝ) : ℂ), by exact_mod_cast hpos.ne', fun φ y => ?_⟩
  have e1 : archMatrixFourier φ (linC K n y) = mixedFourierPi K φ (swapCLE K n (linC K n y)) := by
    rw [← mixedFourierPiSchwartz_apply]
    rfl
  rw [e1, mixedFourierPi, h, integral_smul_nnreal_measure, hν,
    MeasurableEmbedding.integral_map (f := linC K n) (linC K n).toHomeomorph.measurableEmbedding, NNReal.smul_def, Complex.real_smul, four]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [pairing, Circle.smul_def, smul_eq_mul, mul_comm, Real.fourierChar_apply]
  congr 2
  push_cast
  ring

private theorem nrm_pos {x : Lie K n} (hx : x ∈ invSet K n) : 0 < nrm x := by
  have h : IsUnit (Matrix.of x).det := (Matrix.isUnit_iff_isUnit_det _).1 hx
  exact Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (Pi.isUnit_iff.1 h w).ne_zero) _

private theorem continuous_nrm : Continuous (nrm : Lie K n → ℝ) := by
  have h : Continuous fun x : Lie K n => (Matrix.of x).det := Continuous.matrix_det continuous_id
  exact continuous_finset_prod _ fun w _ => (((continuous_apply w).comp h).norm).pow 2

private theorem haar_eq (hH : HaarL) (μ : Measure (AdelicGLn.InfiniteAdelicGL K n)) [μ.IsHaarMeasure] :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ (F : AdelicGLn.InfiniteAdelicGL K n → ℂ) (H : Lie K n → ℂ), ContinuousOn H (invSet K n) →
      (∀ y, F (grpC K n y) = H (toL y.val)) → ∫ x, F x ∂μ = c * ∫ x in invSet K n, ((nrm x)⁻¹ ^ n : ℝ) • H x := by
  letI : MeasurableSpace (GL (Fin n) (Cinf K)) := borel _
  haveI : BorelSpace (GL (Fin n) (Cinf K)) := ⟨rfl⟩
  obtain ⟨m, hm, hmap⟩ := hH K n
  haveI : (Measure.map (grpC K n) m).IsHaarMeasure := (grpC K n).isHaarMeasure_map _
  have h := Measure.isMulLeftInvariant_eq_smul μ (Measure.map (grpC K n) m)
  have hpos := Measure.haarScalarFactor_pos_of_isHaarMeasure μ (Measure.map (grpC K n) m)
  generalize Measure.haarScalarFactor μ (Measure.map (grpC K n) m) = c at h hpos
  refine ⟨((c : ℝ) : ℂ), by exact_mod_cast hpos.ne', fun F H hc hF => ?_⟩
  have hme : MeasurableEmbedding (grpC K n) := (grpC K n).toHomeomorph.measurableEmbedding
  have hv : Continuous fun g : GL (Fin n) (Cinf K) => toL g.val :=
    Units.continuous_val (M := Matrix (Fin n) (Fin n) (Cinf K))
  have hms : MeasurableSet (invSet K n) := isOpen_invSet.measurableSet
  rw [h, integral_smul_nnreal_measure, hme.integral_map, NNReal.smul_def, Complex.real_smul]
  congr 1
  simp_rw [hF]
  rw [← integral_map hv.measurable.aemeasurable, hmap, integral_withDensity_eq_integral_toReal_smul]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [ENNReal.toReal_ofReal]
    exact pow_nonneg (inv_nonneg.2 (Finset.prod_nonneg fun w _ => sq_nonneg _)) _
  · exact (((continuous_nrm K n).measurable.inv).pow_const n).ennreal_ofReal
  · exact Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  · rw [hmap]
    exact (hc.aestronglyMeasurable hms).mono_ac (withDensity_absolutelyContinuous _ _)

end UpperTheory.V.Z.Inf.Bridge

open UpperTheory.V.Z.Inf UpperTheory.V.Z.Inf.Bridge in
theorem UpperTheory.V.Z.Inf.bridgeOf :
    UpperTheory.V.Z.Inf.BridgeOf := by
  intro hH K _ _ _ n μ _
  obtain ⟨c, hc, hz⟩ := haar_eq K n hH μ
  obtain ⟨c', hc', hf⟩ := four_eq K n
  simp only [archComp_infGL]
  refine ⟨(grpC K n).surjective, fun y => by rw [← archComp_infGL, symm_archComp], archAbsDet_grpC K n,
    -4 * Real.pi, c, c', mul_ne_zero (by norm_num) Real.pi_ne_zero, hc, hc', fun Φ hΦ => ?_⟩
  have h1 : HasCompactSupport (Φ ∘ (linC K n).symm) := hΦ.2.1.comp_homeomorph (linC K n).symm.toHomeomorph
  have h2 := hΦ.1.comp (linC K n).symm.contDiff
  have h3 : ∀ x, h1.toSchwartzMap h2 (linC K n x) = Φ x := fun x =>
    congrArg Φ ((linC K n).symm_apply_apply x)
  refine ⟨h1.toSchwartzMap h2, fun fi f hcf hfi s => ?_, fun y => ?_⟩
  · rw [archZeta, hz _ (fun x => Φ x * f x * ((nrm x : ℝ) : ℂ) ^ (s + ((n : ℂ) - 1) / 2))]
    · congr 1
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := invSet K n) (μ := volume)]
      · refine setIntegral_congr_fun isOpen_invSet.measurableSet fun x hx => ?_
        have h0 : ((nrm x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (nrm_pos K n hx).ne'
        rw [Complex.cpow_sub _ _ h0, Complex.cpow_natCast, Complex.real_smul]
        push_cast
        rw [inv_pow, div_eq_mul_inv]
        ring
      · intro x hx
        rw [image_eq_zero_of_notMem_tsupport fun h => hx (hΦ.2.2 h), zero_mul, zero_mul]
    · refine (hΦ.1.continuous.continuousOn.mul hcf).mul ?_
      exact ContinuousOn.cpow_const (Complex.continuous_ofReal.comp (continuous_nrm K n)).continuousOn
        fun x hx => Complex.ofReal_mem_slitPlane.2 (nrm_pos K n hx)
    · intro y
      rw [archIntegrand, archSchwartz_grpC, h3, hfi, archDetPow, archAbsDet_grpC]
  · rw [archSchwartz_grpC, hf]
    simp only [h3]
