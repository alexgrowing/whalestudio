import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SliceFacts
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLActs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicVectorsBoundsPureTensorsSlices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

namespace SliceP

def injL (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (κ' κ'' : Type) :
    (κ' → V) →L[ℝ] (κ' ⊕ κ'' → V) :=
  ContinuousLinearMap.pi fun i => Sum.elim (fun a => (ContinuousLinearMap.proj a : (κ' → V) →L[ℝ] V))
    (fun _ => (0 : (κ' → V) →L[ℝ] V)) i

theorem injL_apply (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (κ' κ'' : Type) (x : κ' → V) :
    injL V κ' κ'' x = Sum.elim x 0 := by
  funext i
  cases i <;> rfl

theorem norm_le_injL (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (κ' κ'' : Type) [Fintype κ'] [Fintype κ'']
    (x : κ' → V) : ‖x‖ ≤ ‖injL V κ' κ'' x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun a => ?_
  rw [injL_apply]
  exact norm_le_pi_norm (Sum.elim x 0 : κ' ⊕ κ'' → V) (Sum.inl a)

def sliceCLM (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (κ' κ'' : Type) [Fintype κ'] [Fintype κ''] :
    SchwartzMap (κ' ⊕ κ'' → V) ℂ →L[ℂ] SchwartzMap (κ' → V) ℂ :=
  SchwartzMap.compCLM ℂ (injL V κ' κ'').hasTemperateGrowth ⟨1, 1, fun x => by
    have := norm_le_injL V κ' κ'' x
    have h0 := norm_nonneg (injL V κ' κ'' x)
    simp only [pow_one, one_mul]
    linarith⟩

theorem sliceCLM_apply (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (κ' κ'' : Type) [Fintype κ'] [Fintype κ'']
    (f : SchwartzMap (κ' ⊕ κ'' → V) ℂ) (x : κ' → V) : sliceCLM V κ' κ'' f x = f (Sum.elim x 0) := by
  simp [sliceCLM, injL_apply]

variable {F : Type} [Field F] [NumberField F]

theorem continuous_sumElim_zero (X : Type) [TopologicalSpace X] [Zero X] (κ' κ'' : Type) :
    Continuous fun x : κ' → X => (Sum.elim x 0 : κ' ⊕ κ'' → X) := by
  refine continuous_pi fun i => ?_
  cases i with
  | inl a => exact continuous_apply a
  | inr b => exact continuous_const

theorem sb_slice {κ' κ'' : Type} {g : (κ' ⊕ κ'' → Af F) → ℂ} (hg : g ∈ SB (κ' ⊕ κ'' → Af F)) :
    (fun x : κ' → Af F => g (Sum.elim x 0)) ∈ SB (κ' → Af F) := by
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  have hc := continuous_sumElim_zero (Af F) κ' κ''
  have hemb : IsClosedEmbedding fun x : κ' → Af F => (Sum.elim x 0 : κ' ⊕ κ'' → Af F) :=
    Function.LeftInverse.isClosedEmbedding (f := fun y : κ' ⊕ κ'' → Af F => y ∘ Sum.inl)
      (fun x => rfl) (continuous_pi fun a => continuous_apply (Sum.inl a)) hc
  exact ⟨hg.1.comp_continuous hc, hg.2.comp_isClosedEmbedding hemb⟩

theorem slice0_pureA {κ' κ'' : Type} [Fintype κ'] [Fintype κ''] (f : SchwartzMap (κ' ⊕ κ'' → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ' ⊕ κ'' → Af F) → ℂ) :
    slice0 κ' κ'' (pureA F f g) = pureA F (sliceCLM _ κ' κ'' f) (fun x => g (Sum.elim x 0)) := by
  funext x
  simp only [slice0, LinearMap.coe_mk, AddHom.coe_mk, pureA, sliceCLM_apply]
  congr 2
  · funext i
    cases i with
    | inl a => rfl
    | inr b => exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  · funext i
    cases i <;> rfl

theorem slice_mem {κ' κ'' : Type} [Fintype κ'] [Fintype κ''] :
    ∀ Ψ ∈ schA F (κ' ⊕ κ''), slice0 κ' κ'' Ψ ∈ schA F κ' := by
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    rw [slice0_pureA]
    exact GlobalTheory.CharInvForm.mem_schA _ (sb_slice hg)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem slice_adm {κ' κ'' : Type} [Fintype κ'] [Fintype κ''] :
    ∀ l ∈ (adeleClass F).adm κ', l ∘ₗ slice0 κ' κ'' ∈ (adeleClass F).adm (κ' ⊕ κ'') := by
  intro l hl g hg
  obtain ⟨T, hT⟩ := hl _ (sb_slice hg)
  refine ⟨T.comp (sliceCLM _ κ' κ''), fun f => ?_⟩
  rw [LinearMap.comp_apply, slice0_pureA, ContinuousLinearMap.comp_apply, hT]

theorem exists_schwartz_one_cpt (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ f₀ : SchwartzMap V ℂ, f₀ 0 = 1 ∧ HasCompactSupport f₀ := by
  obtain ⟨f, -, hc, hs, -, h1⟩ :=
    exists_contDiff_tsupport_subset (x := (0 : V)) (s := Set.univ) (n := ⊤) Filter.univ_mem
  have hc' : HasCompactSupport (fun x => (f x : ℂ)) := hc.comp_left Complex.ofReal_zero
  have hs' : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hs
  exact ⟨hc'.toSchwartzMap hs', by simp [h1], hc'⟩

theorem exists_sb_one (κ : Type) [Fintype κ] : ∃ g ∈ SB (κ → Af F), g 0 = 1 := by
  obtain ⟨g, hg, y, hy⟩ := PositivityTheory.RL.SeminormBoundRestriction.exists_SB (F := F) (κ := κ)
  have hc : Continuous fun x : κ → Af F => x + y := continuous_add_right y
  refine ⟨fun x => g (x + y), ⟨hg.1.comp_continuous hc, ?_⟩, by simpa using hy⟩
  exact hg.2.comp_homeomorph (Homeomorph.addRight y)

theorem continuous_of_mem {κ : Type} [Fintype κ] {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ := by
  have h := GlobalTheory.WeilAdm.HaarSplit.continuous_comp_splitE F κ Φ hΦ
  have e : Φ = fun x => Φ (GlobalTheory.WeilAdm.HaarSplit.splitE F κ ((GlobalTheory.WeilAdm.HaarSplit.splitE F κ).symm x)) :=
    funext fun x => by rw [AddEquiv.apply_symm_apply]
  rw [e]
  exact h.comp (GlobalTheory.WeilAdm.HaarSplit.continuous_splitE_symm F κ)

theorem exists_one (κ'' : Type) [Fintype κ''] : ∃ φ₀ ∈ schA F κ'', φ₀ 0 = 1 ∧
    ∀ μ'' : @Measure (κ'' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ'' →
      ∫⁻ x, ‖φ₀ x‖ₑ ^ 2 ∂μ'' ≠ 0 ∧ ∫⁻ x, ‖φ₀ x‖ₑ ^ 2 ∂μ'' ≠ ⊤ := by
  obtain ⟨f₀, hf₀, hf₀c⟩ := exists_schwartz_one_cpt (κ'' → mixedEmbedding.mixedSpace F)
  obtain ⟨g₀, hg₀, hg₀1⟩ := exists_sb_one (F := F) κ''
  have hmem : pureA F f₀ g₀ ∈ schA F κ'' := GlobalTheory.CharInvForm.mem_schA f₀ hg₀
  have h0 : pureA F f₀ g₀ 0 = 1 := by rw [GlobalTheory.CharInvForm.pureA_zero, hf₀, hg₀1, one_mul]
  refine ⟨pureA F f₀ g₀, hmem, h0, fun μ'' hμ => ?_⟩
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  letI m2 : MeasurableSpace (κ'' → AF F) := borel _
  haveI : BorelSpace (κ'' → AF F) := ⟨rfl⟩
  haveI := hμ
  set φ₀ := pureA F f₀ g₀ with hφ₀
  have hc : Continuous φ₀ := continuous_of_mem hmem

  set sp := GlobalTheory.WeilAdm.HaarSplit.splitE F κ'' with hsp
  have hK : IsCompact (sp '' (tsupport f₀ ×ˢ tsupport g₀)) :=
    (hf₀c.isCompact.prod hg₀.2.isCompact).image (GlobalTheory.WeilAdm.HaarSplit.continuous_splitE F κ'')
  have hzero : ∀ x, x ∉ sp '' (tsupport f₀ ×ˢ tsupport g₀) → φ₀ x = 0 := by
    intro x hx
    have e : φ₀ x = f₀ (sp.symm x).1 * g₀ (sp.symm x).2 := by
      rw [hφ₀, show x = sp (sp.symm x) from (AddEquiv.apply_symm_apply _ _).symm,
        GlobalTheory.WeilAdm.HaarSplit.pureA_splitE, AddEquiv.apply_symm_apply]
    rw [e]
    by_cases h1 : (sp.symm x).1 ∈ tsupport f₀
    · by_cases h2 : (sp.symm x).2 ∈ tsupport g₀
      · exact absurd ⟨sp.symm x, ⟨h1, h2⟩, AddEquiv.apply_symm_apply _ _⟩ hx
      · rw [image_eq_zero_of_notMem_tsupport h2, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]
  have hcs : HasCompactSupport φ₀ := by
    refine HasCompactSupport.intro hK hzero
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  constructor
  ·
    set U : Set (κ'' → AF F) := {x | (1 / 2 : ℝ) < ‖φ₀ x‖} with hU
    have hUo : IsOpen U := isOpen_lt continuous_const hc.norm
    have hU0 : (0 : κ'' → AF F) ∈ U := by
      show (1 / 2 : ℝ) < ‖φ₀ 0‖
      rw [h0, norm_one]
      norm_num
    have hpos : 0 < μ'' U := hUo.measure_pos μ'' ⟨0, hU0⟩
    refine ne_of_gt (lt_of_lt_of_le ?_ (lintegral_mono (g := fun x => ‖φ₀ x‖ₑ ^ 2)
      (f := U.indicator fun _ => ENNReal.ofReal (1 / 2) ^ 2) fun x => ?_))
    · rw [lintegral_indicator_const hUo.measurableSet]
      exact ENNReal.mul_pos (pow_ne_zero 2 (ENNReal.ofReal_pos.2 (by norm_num)).ne') hpos.ne'
    · by_cases hx : x ∈ U
      · rw [Set.indicator_of_mem hx]
        have : (1 / 2 : ℝ) < ‖φ₀ x‖ := hx
        have hle : ENNReal.ofReal (1 / 2) ≤ ‖φ₀ x‖ₑ := by
          rw [← ofReal_norm_eq_enorm]
          exact ENNReal.ofReal_le_ofReal this.le
        exact pow_le_pow_left₀ bot_le hle 2
      · rw [Set.indicator_of_notMem hx]
        exact bot_le
  ·
    set K := sp '' (tsupport f₀ ×ˢ tsupport g₀)
    have hKm : MeasurableSet K := hK.isClosed.measurableSet
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono (g := K.indicator fun _ => ENNReal.ofReal C ^ 2) fun x => ?_) ?_)
    · by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx, ← ofReal_norm_eq_enorm]
        exact pow_le_pow_left₀ bot_le (ENNReal.ofReal_le_ofReal (hC x)) 2
      · rw [Set.indicator_of_notMem hx, hzero x hx]
        simp
    · rw [lintegral_indicator_const hKm]
      exact ENNReal.mul_lt_top (by simp) hK.measure_lt_top

theorem box_norm {κ' κ'' : Type} [Fintype κ'] [Fintype κ''] (μ' : @Measure (κ' → AF F) (borel _))
    (μ'' : @Measure (κ'' → AF F) (borel _)) (h' : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ')
    (h'' : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ'') :
    ∃ μ : @Measure (κ' ⊕ κ'' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
      ∀ φ' ∈ schA F κ', ∀ φ'' ∈ schA F κ'',
        ∫⁻ x, ‖boxFun φ' φ'' x‖ₑ ^ 2 ∂μ = (∫⁻ x, ‖φ' x‖ₑ ^ 2 ∂μ') * ∫⁻ x, ‖φ'' x‖ₑ ^ 2 ∂μ'' := by
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  letI m1 : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  letI m2 : MeasurableSpace (κ'' → AF F) := borel _
  haveI : BorelSpace (κ'' → AF F) := ⟨rfl⟩
  letI m3 : MeasurableSpace (κ' ⊕ κ'' → AF F) := borel _
  haveI : BorelSpace (κ' ⊕ κ'' → AF F) := ⟨rfl⟩
  haveI : MeasurableAdd (κ' → AF F) := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ'' → AF F) := ContinuousAdd.measurableAdd
  haveI := h'
  haveI := h''
  haveI : (μ'.prod μ'').IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure μ' μ''
  let e : ((κ' → AF F) × (κ'' → AF F)) ≃+ (κ' ⊕ κ'' → AF F) :=
    { toFun := fun p => Sum.elim p.1 p.2
      invFun := fun x => (x ∘ Sum.inl, x ∘ Sum.inr)
      left_inv := fun p => rfl
      right_inv := fun x => Sum.elim_comp_inl_inr x
      map_add' := fun p q => by funext i; cases i <;> rfl }
  have hc : Continuous e := continuous_pi fun i => by
    cases i with
    | inl a => exact (continuous_apply a).comp continuous_fst
    | inr b => exact (continuous_apply b).comp continuous_snd
  have hc' : Continuous e.symm :=
    (continuous_pi fun a => continuous_apply (Sum.inl a)).prodMk (continuous_pi fun b => continuous_apply (Sum.inr b))
  refine ⟨(μ'.prod μ'').map e, e.isAddHaarMeasure_map _ hc hc', fun φ' hφ' φ'' hφ'' => ?_⟩
  let em : ((κ' → AF F) × (κ'' → AF F)) ≃ᵐ (κ' ⊕ κ'' → AF F) := (Homeomorph.mk e.toEquiv hc hc').toMeasurableEquiv
  have hint : ∀ h : (κ' ⊕ κ'' → AF F) → ℝ≥0∞, ∫⁻ x, h x ∂((μ'.prod μ'').map e) = ∫⁻ p, h (e p) ∂(μ'.prod μ'') :=
    fun h => lintegral_map_equiv h em
  rw [hint]
  have e1 : ∀ p : (κ' → AF F) × (κ'' → AF F), ‖boxFun φ' φ'' (e p)‖ₑ ^ 2 = ‖φ' p.1‖ₑ ^ 2 * ‖φ'' p.2‖ₑ ^ 2 := by
    intro p
    rw [show boxFun φ' φ'' (e p) = φ' p.1 * φ'' p.2 from rfl, enorm_mul, mul_pow]
  simp_rw [e1]
  exact lintegral_prod_mul ((continuous_of_mem hφ').measurable.enorm.pow_const 2).aemeasurable
    ((continuous_of_mem hφ'').measurable.enorm.pow_const 2).aemeasurable

end SliceP

theorem sliceFacts : SliceFacts := fun F _ _ κ' κ'' _ _ =>
  ⟨SliceP.slice_mem, SliceP.slice_adm, SliceP.exists_one κ'', fun μ' μ'' h' h'' => SliceP.box_norm μ' μ'' h' h''⟩

end PositivityTheory.SiegelWeilFormula.Ald

end
