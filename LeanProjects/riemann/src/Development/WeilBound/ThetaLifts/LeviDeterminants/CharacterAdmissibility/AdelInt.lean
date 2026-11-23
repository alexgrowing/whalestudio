import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.ResAdm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddHaarLeftRightMulAdelicMatricesModule
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.DiagForm GlobalTheory.GaugeEx GlobalTheory.ModuLR

noncomputable section
namespace PositivityTheory.ThKF0.Chr

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem distrib_eq [IsTotallyReal F] (u : (AF F)ˣ) :
    (distribHaarChar (AF F) u : ℝ) = (∏ w, ‖(fstA F u.1) w‖) * ∏ᶠ v, ‖evalV F v (sndA F u.1)‖ := by
  have hM : IsUnit (Matrix.diagonal fun _ : Unit => u.1).det := by simp
  have h := chi_AF F (Matrix.diagonal fun _ : Unit => u.1) hM
  rw [show (Matrix.diagonal fun _ : Unit => u.1).det = u.1 by simp] at h
  rw [← h]
  let e : AF F ≃ₜ+ AF F :=
    { toFun := fun x => u.1 * x, invFun := fun x => (u⁻¹).1 * x, left_inv := fun x => by simp, right_inv := fun x => by simp
      map_add' := mul_add _, continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  let j : AF F →+ (Unit → AF F) := { toFun := fun x _ => x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hj : IsOpenEmbedding j := (Homeomorph.funUnique Unit (AF F)).symm.isOpenEmbedding
  rw [GlobalTheory.T.addEquivAddHaarChar_eq_of_isOpenEmbedding_restrict _ _ j hj _ e (fun x => by funext i; simp [mulVecCE_apply, Matrix.mulVec_diagonal, j, e])]
  congr 1
  obtain ⟨K, hK⟩ := exists_compact_mem_nhds (0 : AF F)
  let μ : Measure (AF F) := Measure.addHaar
  have h0 : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hK.2).ne'
  refine distribHaarChar_eq_of_measure_smul_eq_mul h0 hK.1.measure_lt_top.ne ?_
  have := addEquivAddHaarChar_smul_preimage μ (X := e '' K) e
  rw [Set.preimage_image_eq _ e.injective] at this
  exact this.symm

theorem chi_eq [IsTotallyReal F] [DecidableEq κ] (M : Matrix κ κ (AF F)) (hM : IsUnit M.det) :
    addEquivAddHaarChar (mulVecCE M hM) = distribHaarChar (AF F) hM.unit :=
  NNReal.coe_injective (by rw [chi_AF, distrib_eq, hM.unit_spec])

theorem absE_eq [IsTotallyReal F] {E : Type} [Field E] [NumberField E] [Algebra F E] (t : (AF F ⊗[F] E)ˣ) :
    GlobalTheory.Doubling.absE F E t = distribHaarChar (AF F) (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) t) :=
  NNReal.coe_injective (by rw [distrib_eq, ← GlobalTheory.T.tensorIdeleNormalizedAbs_eq_adelic_abs_norm]; rfl)

theorem continuous_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

variable (F κ) in

def glueE : (Vi F κ × Vf F κ) ≃ₜ+ (κ → AF F) where
  toFun := glue
  invFun := shiftOf
  left_inv p := by
    refine Prod.ext ?_ rfl
    simp [shiftOf, glue]
  right_inv x := by
    funext i
    refine Prod.ext ?_ rfl
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ ((eI F κ).symm _) i) = _
    rw [ContinuousLinearEquiv.apply_symm_apply, RingEquiv.symm_apply_apply]
  map_add' p q := by
    funext i
    refine Prod.ext ?_ rfl
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ (p.1 + q.1) i) = _
    rw [map_add, Pi.add_apply, map_add]
    rfl
  continuous_toFun := continuous_pi fun i =>
    (continuous_ofMixed.comp ((continuous_apply i).comp ((eI F κ).continuous.comp continuous_fst))).prodMk
      ((continuous_apply i).comp continuous_snd)
  continuous_invFun := ((eI F κ).symm.continuous.comp (continuous_pi fun i =>
    continuous_toMixed.comp (continuous_fst.comp (continuous_apply i)))).prodMk
      (continuous_pi fun i => continuous_snd.comp (continuous_apply i))

theorem axInt [IsTotallyReal F] : AxInt (adeleClass F) := by
  intro κ _
  classical
  let r : ((κ → AF F) → ℂ) →ₗ[ℂ] (Vi F κ × Vf F κ → ℂ) := LinearMap.funLeft ℂ ℂ glue
  let cI : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (Vi F κ) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F κ)
  have hp : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) g, r (pureA F f g) = fun p => cI f p.1 * g p.2 :=
    fun f g => funext fun p => by
      show f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _)) * g p.2 = _
      simp only [RingEquiv.apply_symm_apply]
      rfl
  have hg : ∀ g ∈ SB (Vf F κ), Integrable g (Measure.addHaar : Measure (Vf F κ)) := fun g hg =>
    hg.1.continuous.integrable_of_hasCompactSupport hg.2
  have hi : ∀ φ ∈ schA F κ, Integrable (r φ) (mu F κ) := fun φ hφ => by
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, g, hg', rfl⟩ := hx
      rw [hp]
      exact (cI f).integrable.mul_prod (hg g hg')
    | zero => rw [map_zero]; exact integrable_zero _ _ _
    | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
    | smul c x _ hx => rw [map_smul]; exact hx.smul c
  have : (mu F κ).IsAddHaarMeasure := by unfold mu; infer_instance
  let ν : Measure (κ → AF F) := (mu F κ).map (glueE F κ)
  have : ν.IsAddHaarMeasure := (glueE F κ).isAddHaarMeasure_map _
  have hI : ∀ φ ∈ schA F κ, (Lext F κ ∘ₗ r) φ = ∫ x, φ x ∂ν := fun φ hφ => by
    rw [LinearMap.comp_apply, Lext_apply _ (hi φ hφ)]
    exact ((glueE F κ).toHomeomorph.toMeasurableEquiv.measurableEmbedding.integral_map φ).symm
  refine ⟨Lext F κ ∘ₗ r, fun g hg' => ?_, ?_, fun a φ hφ => ?_, fun g φ hφ hφ' => ?_⟩
  · refine ⟨(∫ v : Vf F κ, g v ∂Measure.addHaar) • ((SchwartzMap.integralCLM ℂ (volume : Measure (Vi F κ))).comp cI),
      fun f => ?_⟩
    rw [LinearMap.comp_apply, Lext_apply _ (hi _ (Submodule.subset_span ⟨f, g, hg', rfl⟩)), hp, mu,
      integral_prod_mul (fun u => cI f u) g, mul_comm]
    rfl
  · obtain ⟨hO, hK⟩ := PI.IntAdCpctOpenWork.main F
    set O := {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}
    have h0 : (0 : FiniteAdeleRing (𝓞 F) F) ∈ O := fun v => (v.adicCompletionIntegers F).zero_mem
    set U : Set (Vf F κ) := Set.univ.pi fun _ => O
    have hUo : IsOpen U := isOpen_set_pi Set.finite_univ fun _ _ => hO
    have hUc : IsCompact U := isCompact_univ_pi fun _ => hK
    set g : Vf F κ → ℂ := U.indicator fun _ => 1
    have hg' : g ∈ SB (Vf F κ) :=
      ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hUc.isClosed, hUo⟩).isLocallyConstant,
        HasCompactSupport.intro hUc fun z hz => Set.indicator_of_notMem hz _⟩
    have hc : (∫ v : Vf F κ, g v ∂Measure.addHaar) ≠ 0 := by
      rw [integral_indicator_const _ hUo.measurableSet]
      have hpos : 0 < (Measure.addHaar : Measure (Vf F κ)) U := hUo.measure_pos _ ⟨0, fun i _ => h0⟩
      have hfin : (Measure.addHaar : Measure (Vf F κ)) U < ⊤ := hUc.measure_lt_top
      have : 0 < (Measure.addHaar : Measure (Vf F κ)).real U := ENNReal.toReal_pos hpos.ne' hfin.ne
      simpa using this.ne'
    let b : ContDiffBump (0 : Vi F κ) := ⟨1, 2, one_pos, one_lt_two⟩
    have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
      b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    let f₀ : SchwartzMap (Vi F κ) ℂ := h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
    let f := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F κ).symm f₀
    have e : ∀ u, cI f u = ((b u : ℝ) : ℂ) := fun u => by
      show f₀ ((eI F κ).symm (eI F κ u)) = _
      rw [ContinuousLinearEquiv.symm_apply_apply]
      rfl
    refine ⟨pureA F f g, Submodule.subset_span ⟨f, g, hg', rfl⟩, ?_⟩
    rw [LinearMap.comp_apply, Lext_apply _ (hi _ (Submodule.subset_span ⟨f, g, hg', rfl⟩)), hp, mu,
      integral_prod_mul (fun u => cI f u) g]
    refine mul_ne_zero ?_ hc
    simp only [e, integral_complex_ofReal]
    exact_mod_cast (b.integral_pos (μ := volume)).ne'
  · have e : r (fun x => φ (x + a)) = fun p => r φ (p + shiftOf a) := funext fun p =>
      congrArg φ (glue_add_shiftOf p a).symm
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e, Lext_apply _ ((hi φ hφ).comp_add_right _), Lext_apply _ (hi φ hφ),
      integral_add_right_eq_self]
  · let M := LinearMap.toMatrix' g.toLinearMap
    have hd : M.det = (LinearEquiv.det g : (AF F)ˣ) := by
      rw [LinearEquiv.coe_det, LinearMap.det_toMatrix']
    have hM : IsUnit M.det := hd ▸ Units.isUnit _
    have hu : hM.unit = LinearEquiv.det g := Units.ext hd
    have hge : ∀ x, mulVecCE M hM x = g x := fun x => LinearMap.toMatrix'_mulVec _ _
    rw [hI _ hφ', hI _ hφ]
    conv_lhs => rw [← addEquivAddHaarChar_smul_map ν (mulVecCE M hM)]
    rw [integral_smul_nnreal_measure, chi_eq, hu,
      MeasurableEmbedding.integral_map (f := mulVecCE M hM) (mulVecCE M hM).toHomeomorph.toMeasurableEquiv.measurableEmbedding]
    simp only [hge, LinearEquiv.symm_apply_apply, NNReal.smul_def, Complex.real_smul]
    rfl

end PositivityTheory.ThKF0.Chr
