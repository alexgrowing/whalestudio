import Mathlib
import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanUnitIdempotentSmulMixedSpaceVecPairAs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.WeilBound.ThetaLifts.CartanFactorisation.EqOfInner

noncomputable section

namespace PositivityTheory.ThKF.A

open scoped TensorProduct NNReal ENNReal Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Real RealInnerProductSpace Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels PositivityTheory.ThKF.W GlobalTheory.HeisSchA

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_sb_one : ∃ g ∈ SB (κ → Af F), g 0 = 1 := by
  haveI : LocallyCompactSpace (Af F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  haveI := nonarch_finiteAdeleRing (F := F)
  haveI : NonarchimedeanAddGroup (κ → Af F) := nonarch_pi
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : κ → Af F)
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean K hK0
  have hc : IsCompact (V : Set (κ → Af F)) := hK.of_isClosed_subset V.isClosed hV
  refine ⟨(V : Set (κ → Af F)).indicator fun _ => 1, ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ))
    V.isClopen).isLocallyConstant, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩,
    Set.indicator_of_mem V.zero_mem _⟩

theorem exists_char_ne {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {z : κ → Af F} (hz : z ≠ 0) :
    ∃ w : κ → Af F, finChar ψ (z ⬝ᵥ w) ≠ 1 := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hz
  have : ∃ v, evalV F v (z i) ≠ 0 := by
    by_contra h
    push Not at h
    exact hi (af_ext fun u => by rw [h u]; simp)
  obtain ⟨v, hv⟩ := this
  obtain ⟨t, ht⟩ := DFunLike.ne_iff.1 (GlobalTheory.PsiNontriv.psiAt_ne_one ψ hψ v)
  refine ⟨Pi.single i (singleFin v (t / evalV F v (z i))), ?_⟩
  have e : z i * singleFin v (t / evalV F v (z i)) = singleFin v t := af_ext fun u => by
    by_cases h : u = v
    · subst h
      rw [map_mul, evalV_singleFin_self, evalV_singleFin_self, mul_div_cancel₀ _ hv]
    · rw [map_mul, evalV_singleFin_ne h, evalV_singleFin_ne h, mul_zero]
  rw [dotProduct_single, e]
  exact ht

theorem finE_dot (x : κ → AF F) (w : κ → Af F) : x ⬝ᵥ finE F w = ((0, (fun i => (x i).2) ⬝ᵥ w) : AF F) := by
  simp only [dotProduct, finE]
  refine Prod.ext ?_ ?_
  · exact (map_sum (p1 (F := F)) _ _).trans (Finset.sum_eq_zero fun i _ => mul_zero (x i).1)
  · exact map_sum (p2 (F := F)) _ _

theorem schr_mod (ψ : AddChar (AF F) ℂ) (w : κ → Af F) (Φ : (κ → AF F) → ℂ) (x : κ → AF F) :
    schr ψ (finE2 F (0, w)) Φ x = finChar ψ ((fun i => (x i).2) ⬝ᵥ w) * Φ x := by
  have : finE F (0 : κ → Af F) = 0 := rfl
  simp only [schr, finE2, this, zero_dotProduct, mul_zero, add_zero]
  rw [finE_dot]
  rfl

theorem schr_tr (ψ : AddChar (AF F) ℂ) (z : κ → Af F) (Φ : (κ → AF F) → ℂ) (x : κ → AF F) :
    schr ψ (finE2 F (z, 0)) Φ x = Φ (x + finE F z) := by
  have : finE F (0 : κ → Af F) = 0 := rfl
  simp [schr, finE2, this]

theorem pureA_mem (f : SInf F κ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) : pureA F f g ∈ schA F κ :=
  Submodule.subset_span ⟨f, g, hg, rfl⟩

theorem apply_pure {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (S : Module.End ℂ ((κ → AF F) → ℂ))
    (hS : ∀ m, ∀ Φ ∈ schA F κ, S (schr ψ (finE2 F m) Φ) = schr ψ (finE2 F m) (S Φ)) (f : SInf F κ)
    {g₀ : (κ → Af F) → ℂ} (h₀ : g₀ ∈ SB (κ → Af F)) (h₁ : g₀ 0 = 1) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    S (pureA F f g) = pureA F (slice F (S (pureA F f g₀)) 0) g := by
  classical
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  let L : ((κ → Af F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) :=
    { toFun := fun g => pureA F f g
      map_add' := fun a b => funext fun x => by simp [pureA, mul_add]
      map_smul' := fun c a => funext fun x => by simp [pureA, mul_left_comm] }
  have key : ∀ φ ∈ SB (κ → Af F), φ 0 = 0 → ∀ y, S (pureA F f φ) (infE F y) = 0 := fun φ hφ h0 y => by
    let e : (κ → Af F) → (κ → Af F) → ℂ := fun w z => finChar ψ (z ⬝ᵥ w) - 1
    have he : ∀ w, IsLocallyConstant (e w) := fun w =>
      ((finChar_isLocallyConstant ψ hψ.1).comp_continuous (continuous_id.dotProduct continuous_const)).comp (· - 1)
    have hts : tsupport φ = Function.support φ := by
      refine IsClosed.closure_eq ⟨?_⟩
      have := hφ.1.isOpen_fiber 0
      convert this using 1
      ext x
      simp
    have hex : ∀ z : tsupport φ, ∃ w, e w z ≠ 0 := fun z => by
      have hz : (z : κ → Af F) ≠ 0 := fun h => by
        have : (z : κ → Af F) ∈ Function.support φ := hts ▸ z.2
        exact this (h ▸ h0)
      obtain ⟨w, hw⟩ := exists_char_ne hψ hz
      exact ⟨w, sub_ne_zero.2 hw⟩
    choose w hw using hex
    obtain ⟨t, ht⟩ := (hφ.2 : IsCompact (tsupport φ)).elim_nhds_subcover' (fun z hz => {x | e (w ⟨z, hz⟩) x ≠ 0})
      fun z hz => ((he _).continuous.isOpen_preimage _ isOpen_ne).mem_nhds (hw ⟨z, hz⟩)
    let G : (κ → Af F) → ℂ := fun x => ∑ z ∈ t, e (w z) x * (starRingEnd ℂ) (e (w z) x)
    have hG : IsLocallyConstant G := by
      rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      filter_upwards [(Filter.eventually_all_finset t).2 fun z _ => (he (w z)).eventually_eq x] with y hy
      exact Finset.sum_congr rfl fun z hz => by rw [hy z hz]
    have hG0 : ∀ x, φ x ≠ 0 → G x ≠ 0 := fun x hx => by
      obtain ⟨z, hz, hzx⟩ : ∃ z ∈ t, e (w z) x ≠ 0 := by simpa using ht (subset_tsupport _ hx)
      simp only [G, Complex.mul_conj]
      rw [← Complex.ofReal_sum, Complex.ofReal_ne_zero]
      exact (Finset.sum_pos' (f := fun i => Complex.normSq (e (w i) x)) (fun _ _ => Complex.normSq_nonneg _) ⟨z, hz, Complex.normSq_pos.2 hzx⟩).ne'
    let φ' : tsupport φ → (κ → Af F) → ℂ := fun z x => (starRingEnd ℂ) (e (w z) x) * (G x)⁻¹ * φ x
    have hφ' : ∀ z, φ' z ∈ SB (κ → Af F) := fun z =>
      ⟨((((he (w z)).comp (starRingEnd ℂ)).mul (hG.comp (·⁻¹))).mul hφ.1), hφ.2.mul_left⟩
    have hsum : pureA F f φ = ∑ z ∈ t, (schr ψ (finE2 F (0, w z)) (pureA F f (φ' z)) - pureA F f (φ' z)) := by
      funext x
      simp only [Finset.sum_apply, Pi.sub_apply, schr_mod, pureA, φ']
      by_cases hx : φ (fun i => (x i).2) = 0
      · simp [hx]
      · have := hG0 _ hx
        have e2 : ∀ (a b c d k : ℂ), a * (k * (b * c * d)) - k * (b * c * d) = ((a - 1) * b) * (k * c * d) := fun _ _ _ _ _ => by
          ring
        simp only [e2, ← Finset.sum_mul]
        change _ = G _ * _
        field_simp
    rw [hsum, map_sum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [map_sub, hS _ _ (pureA_mem f (hφ' z)), Pi.sub_apply, schr_mod]
    have : (fun i => (infE F y i).2) = 0 := rfl
    rw [this, zero_dotProduct, AddChar.map_zero_eq_one, one_mul, sub_self]
  funext x
  set z : κ → Af F := fun i => (x i).2 with hz
  set y := infPart x with hy
  have hx : x = infE F y + finE F z := funext fun i => Prod.ext
    (by show _ = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ + 0
        rw [add_zero]; exact (RingEquiv.symm_apply_apply _ _).symm) (zero_add (x i).2).symm
  have hg' : (fun u => g (u + z)) ∈ SB (κ → Af F) :=
    ⟨hg.1.comp_continuous (continuous_add_right z), hg.2.comp_homeomorph (Homeomorph.addRight z)⟩
  have e1 : schr ψ (finE2 F (z, 0)) (pureA F f g) = pureA F f fun u => g (u + z) := funext fun a => by
    rw [schr_tr]
    simp only [pureA]
    congr 2
    funext i
    exact congrArg _ (add_zero _)
  have e2 := key _ (sub_mem hg' (Submodule.smul_mem _ (g z) h₀)) (by simp [h₁]) y
  have e3 : pureA F f ((fun u => g (u + z)) - g z • g₀) = pureA F f (fun u => g (u + z)) - g z • pureA F f g₀ := by
    have := map_sub L (fun u => g (u + z)) (g z • g₀)
    rw [map_smul] at this
    exact this
  rw [e3, map_sub, map_smul, ← e1, hS _ _ (pureA_mem f hg), Pi.sub_apply, schr_tr, ← hx, sub_eq_zero] at e2
  rw [e2, Pi.smul_apply, smul_eq_mul, mul_comm]
  rfl

theorem pureA_inj {f f' : (κ → mixedEmbedding.mixedSpace F) → ℂ} {g : (κ → Af F) → ℂ} (hg : g 0 = 1)
    (h : pureA F f g = pureA F f' g) : f = f' := funext fun y => by
  have := congrFun h (infE F y)
  have e : (fun i => (infE F y i).2) = 0 := rfl
  have e' : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (infE F y i).1) = y := infPart_infE y
  simpa only [pureA, e, e', hg, mul_one] using this

theorem exists_lin {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (S : Module.End ℂ ((κ → AF F) → ℂ))
    (hp : ∀ Φ ∈ schA F κ, S Φ ∈ schA F κ)
    (hS : ∀ m, ∀ Φ ∈ schA F κ, S (schr ψ (finE2 F m) Φ) = schr ψ (finE2 F m) (S Φ)) :
    ∃ T : SInf F κ →ₗ[ℂ] SInf F κ, ∀ f : SInf F κ, ∀ g ∈ SB (κ → Af F), S (pureA F f g) = pureA F (T f) g := by
  obtain ⟨g₀, h₀, h₁⟩ := exists_sb_one (F := F) (κ := κ)
  choose T hT using fun f : SInf F κ => exists_schwartz_slice _ (hp _ (pureA_mem f h₀)) 0
  have h : ∀ f : SInf F κ, ∀ g ∈ SB (κ → Af F), S (pureA F f g) = pureA F (T f) g := fun f g hg => by
    rw [apply_pure hψ S hS f h₀ h₁ hg, show ⇑(T f) = _ from funext (hT f)]
  refine ⟨⟨⟨T, fun a b => DFunLike.coe_injective (pureA_inj h₁ ?_)⟩, fun c a => DFunLike.coe_injective (pureA_inj h₁ ?_)⟩, h⟩
  · rw [← h _ _ h₀, show ⇑(a + b) = ⇑a + ⇑b from rfl, pureA_add, map_add, h _ _ h₀, h _ _ h₀, ← pureA_add]
    rfl
  · rw [← h _ _ h₀, show ⇑(c • a) = c • ⇑a from rfl, pureA_smul, map_smul, h _ _ h₀, ← pureA_smul]
    rfl

theorem lintegral_eq {S : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    (hU : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖S φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) {f f' : SInf F κ}
    (h : ∀ g ∈ SB (κ → Af F), S (pureA F f g) = pureA F f' g) : ∫⁻ x, ‖f' x‖ₑ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  obtain ⟨g, hg, h₁⟩ := exists_sb_one (F := F) (κ := κ)
  haveI := HaarSplit.volume_isAddHaar F κ
  haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI mY : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : SigmaCompactSpace (κ → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  set ν : Measure (κ → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
  haveI : SFinite ν := inferInstance
  haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : ((volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (κ → mixedEmbedding.mixedSpace F)) ν
  have hμH : Measure.IsAddHaarMeasure ((volume.prod ν).map (HaarSplit.splitE F κ)) :=
    (HaarSplit.splitE F κ).isAddHaarMeasure_map _ (HaarSplit.continuous_splitE F κ) (HaarSplit.continuous_splitE_symm F κ)
  let em : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ᵐ (κ → AdeleRing (𝓞 F) F) :=
    (Homeomorph.mk (HaarSplit.splitE F κ).toEquiv (HaarSplit.continuous_splitE F κ)
      (HaarSplit.continuous_splitE_symm F κ)).toMeasurableEquiv
  have hint : ∀ h : (κ → AdeleRing (𝓞 F) F) → ℝ≥0∞,
      ∫⁻ x, h x ∂((volume.prod ν).map (HaarSplit.splitE F κ)) = ∫⁻ p, h (HaarSplit.splitE F κ p) ∂(volume.prod ν) :=
    fun h => lintegral_map_equiv h em
  have hgc : Continuous g := hg.1.continuous
  have hC : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≠ ⊤ := by
    have h1 : ∫⁻ y, ‖g y * g y‖ₑ ∂ν < ⊤ :=
      ((hgc.mul hgc).integrable_of_hasCompactSupport (hg.2.mul_left (f := g))).2
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) h1)
    rw [enorm_mul, sq]
  have hC0 : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≠ 0 := fun h0 => by
    rw [lintegral_eq_zero_iff (hgc.measurable.enorm.pow_const 2)] at h0
    have h2 : g =ᵐ[ν] 0 := h0.mono fun y hy => by simpa using hy
    have := congrFun ((hgc.ae_eq_iff_eq ν continuous_zero).1 h2) 0
    simp [h₁] at this
  have hp : ∀ a : SInf F κ, ∫⁻ x, ‖pureA F a g x‖ₑ ^ 2 ∂((volume.prod ν).map (HaarSplit.splitE F κ)) =
      (∫⁻ x, ‖a x‖ₑ ^ 2) * ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν := fun a => by
    rw [hint]
    have e1 : ∀ p, ‖pureA F a g (HaarSplit.splitE F κ p)‖ₑ ^ 2 = ‖a p.1‖ₑ ^ 2 * ‖g p.2‖ₑ ^ 2 := by
      intro p
      rw [HaarSplit.pureA_splitE, enorm_mul, mul_pow]
    simp_rw [e1]
    rw [lintegral_prod_mul (a.continuous.measurable.enorm.pow_const 2).aemeasurable
      (hgc.measurable.enorm.pow_const 2).aemeasurable]
  have := hU _ hμH _ (pureA_mem f hg)
  rw [h g hg, hp, hp] at this
  exact (ENNReal.mul_left_inj hC0 hC).1 this

theorem exists_adm (L : SInf F κ →L[ℂ] ℂ) : ∃ l ∈ (adeleClass F).adm κ, ∀ f : SInf F κ, ∀ g ∈ SB (κ → Af F),
    l (pureA F f g) = g 0 * L f := by
  choose s hs using fun Φ : schA F κ => exists_schwartz_slice Φ.1 Φ.2 0
  let s' : schA F κ →ₗ[ℂ] SInf F κ :=
    { toFun := s
      map_add' := fun a b => SchwartzMap.ext fun z => by rw [SchwartzMap.add_apply, hs, hs, hs]; rfl
      map_smul' := fun c a => SchwartzMap.ext fun z => by rw [SchwartzMap.smul_apply, hs, hs]; rfl }
  obtain ⟨l, hl⟩ := LinearMap.exists_extend (L.toLinearMap ∘ₗ s')
  have h : ∀ f : SInf F κ, ∀ g ∈ SB (κ → Af F), l (pureA F f g) = g 0 * L f := fun f g hg => by
    have h1 := LinearMap.congr_fun hl ⟨_, pureA_mem f hg⟩
    have h2 : s ⟨_, pureA_mem f hg⟩ = g 0 • f := SchwartzMap.ext fun z => by
      rw [hs]
      simp only [SchwartzMap.smul_apply, smul_eq_mul, slice, pureA, RingEquiv.apply_symm_apply]
      exact mul_comm _ _
    refine h1.trans ?_
    show L (s _) = _
    rw [h2, map_smul, smul_eq_mul]
  exact ⟨l, fun g hg => ⟨g 0 • L, fun f => h f g hg⟩, h⟩

end PositivityTheory.ThKF.A
