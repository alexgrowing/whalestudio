import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfAtOfPiInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleWithArchimedeanComponents
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

noncomputable section

namespace GlobalTheory.ArchIdeleDecay

open MeasureTheory Measure Set
open scoped ENNReal

theorem secondCountable_unitsC : SecondCountableTopology ℂˣ :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology

theorem borel_unitsC : BorelSpace ℂˣ where
  measurable_eq := by
    rw [congrArg (@borel ℂˣ) Units.isOpenEmbedding_val.isInducing.eq_induced, borel_comap,
      ← BorelSpace.measurable_eq (α := ℂ)]
    rfl

attribute [local instance] secondCountable_unitsC borel_unitsC

variable {ι : Type} [Fintype ι]

def invSqWt (b : ι → ℂ) : ℝ≥0∞ := ∏ i, ‖b i‖ₑ⁻¹ ^ 2

def wVol (ι : Type) [Fintype ι] : Measure (ι → ℂ) := (volume : Measure (ι → ℂ)).withDensity invSqWt

def toUnits (b : ι → ℂ) : ι → ℂˣ := fun i => if h : b i = 0 then 1 else Units.mk0 (b i) h

def unitsHaar (ι : Type) [Fintype ι] : Measure (ι → ℂˣ) := (wVol ι).map toUnits

def scaleMap (t : ι → ℂˣ) : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) :=
  LinearMap.pi fun i => (Algebra.lmul ℝ ℂ (t i : ℂ)).comp (LinearMap.proj i)

omit [Fintype ι] in
theorem scaleMap_apply (t : ι → ℂˣ) (b : ι → ℂ) (i : ι) : scaleMap t b i = (t i : ℂ) * b i := by
  simp [scaleMap]

theorem det_scaleMap (t : ι → ℂˣ) : LinearMap.det (scaleMap t) = ∏ i, Complex.normSq (t i : ℂ) := by
  rw [scaleMap, LinearMap.det_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Algebra.norm_apply, Algebra.norm_complex_apply]

theorem measurable_units_val : Measurable (Units.val : ℂˣ → ℂ) := fun _ hs => ⟨_, hs, rfl⟩

theorem measurable_to_units {α : Type} [MeasurableSpace α] {f : α → ℂˣ} (hf : Measurable fun x => (f x : ℂ)) :
    Measurable f := by
  rintro _ ⟨t, ht, rfl⟩
  exact hf ht

theorem measurable_invSqWt : Measurable (invSqWt : (ι → ℂ) → ℝ≥0∞) :=
  Finset.measurable_prod _ fun i _ => ((measurable_pi_apply i).enorm.inv).pow_const 2

omit [Fintype ι] in
theorem measurable_toUnits : Measurable (toUnits : (ι → ℂ) → ι → ℂˣ) := by
  refine measurable_pi_lambda _ fun i => measurable_to_units ?_
  have : (fun b : ι → ℂ => ((toUnits b i : ℂˣ) : ℂ)) = fun b => if b i = 0 then 1 else b i := by
    funext b
    by_cases h : b i = 0 <;> simp [toUnits, h]
  rw [this]
  exact Measurable.ite ((measurableSet_singleton 0).preimage (measurable_pi_apply i)) measurable_const
    (measurable_pi_apply i)

theorem ae_ne_zero : ∀ᵐ b ∂(volume : Measure (ι → ℂ)), ∀ i, b i ≠ 0 := by
  have h0 : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  exact ae_all_iff.2 fun i =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : ι => (volume : Measure ℂ)) (i := i)).eventually h0

theorem ae_ne_zero_w : ∀ᵐ b ∂(wVol ι), ∀ i, b i ≠ 0 :=
  (withDensity_absolutelyContinuous _ _).ae_le ae_ne_zero

theorem map_scaleMap (t : ι → ℂˣ) : (wVol ι).map (scaleMap t) = wVol ι := by
  have hL : Measurable (scaleMap t) := (scaleMap t).continuous_of_finiteDimensional.measurable
  have hDpos : 0 < ∏ i, Complex.normSq (t i : ℂ) :=
    Finset.prod_pos fun i _ => Complex.normSq_pos.2 (t i).ne_zero
  have hD : LinearMap.det (scaleMap t) ≠ 0 := by rw [det_scaleMap]; exact hDpos.ne'
  set κ : ℝ≥0∞ := ∏ i, ‖(t i : ℂ)‖ₑ ^ 2 with hκdef
  have hκ0 : κ ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (enorm_ne_zero.2 (t i).ne_zero)
  have hκtop : κ ≠ ⊤ := ENNReal.prod_ne_top fun i _ => ENNReal.pow_ne_top enorm_ne_top
  have hκD : ENNReal.ofReal (∏ i, Complex.normSq (t i : ℂ)) = κ := by
    rw [ENNReal.ofReal_prod_of_nonneg fun i _ => Complex.normSq_nonneg _]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_norm_sq, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hκ : κ * ENNReal.ofReal |(LinearMap.det (scaleMap t))⁻¹| = 1 := by
    rw [det_scaleMap, abs_of_pos (inv_pos.2 hDpos), ENNReal.ofReal_inv_of_pos hDpos, hκD,
      ENNReal.mul_inv_cancel hκ0 hκtop]
  have hW : ∀ b, invSqWt b = κ * invSqWt (scaleMap t b) := by
    intro b
    rw [invSqWt, invSqWt, hκdef, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    have h0 : ‖(t i : ℂ)‖ₑ ≠ 0 := enorm_ne_zero.2 (t i).ne_zero
    rw [scaleMap_apply, enorm_mul, ENNReal.mul_inv (Or.inl h0) (Or.inl enorm_ne_top), mul_pow,
      ← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel h0 enorm_ne_top, one_pow, one_mul]
  ext s hs
  rw [map_apply hL hs, wVol, withDensity_apply _ (hL hs), withDensity_apply _ hs,
    ← lintegral_indicator (hL hs), ← lintegral_indicator hs]
  have hind : (scaleMap t ⁻¹' s).indicator invSqWt =
      fun b => κ * s.indicator invSqWt (scaleMap t b) := by
    funext b
    by_cases hb : scaleMap t b ∈ s
    · rw [indicator_of_mem (show b ∈ scaleMap t ⁻¹' s from hb), indicator_of_mem hb, hW]
    · rw [indicator_of_notMem (show b ∉ scaleMap t ⁻¹' s from hb), indicator_of_notMem hb, mul_zero]
  have hm : Measurable (s.indicator (invSqWt : (ι → ℂ) → ℝ≥0∞)) := measurable_invSqWt.indicator hs
  rw [hind]
  beta_reduce
  rw [lintegral_const_mul _ (f := fun b => s.indicator invSqWt (scaleMap t b)) (hm.comp hL),
    ← lintegral_map hm hL, map_linearMap_addHaar_eq_smul_addHaar _ hD, lintegral_smul_measure, smul_eq_mul,
    ← mul_assoc, hκ, one_mul]

instance : IsMulLeftInvariant (unitsHaar ι) := by
  refine ⟨fun s => ?_⟩
  have hL : Measurable (scaleMap s) := (scaleMap s).continuous_of_finiteDimensional.measurable
  have hae : (fun x => s * x) ∘ toUnits =ᵐ[wVol ι] toUnits ∘ scaleMap s := by
    filter_upwards [ae_ne_zero_w] with b hb
    funext i
    have hsb : scaleMap s b i ≠ 0 := by
      rw [scaleMap_apply]; exact mul_ne_zero (s i).ne_zero (hb i)
    simp only [Function.comp, toUnits, Pi.mul_apply, dif_neg (hb i), dif_neg hsb]
    ext
    simp only [Units.val_mul, Units.val_mk0, scaleMap_apply]
  rw [unitsHaar, map_map (measurable_const_mul s) measurable_toUnits, Measure.map_congr hae,
    ← map_map measurable_toUnits hL, map_scaleMap]

instance : IsFiniteMeasureOnCompacts (unitsHaar ι) := by
  refine ⟨fun K hK => ?_⟩
  let φ : (ι → ℂˣ) → ℝ := fun a => ∑ i, (‖(a i : ℂ)‖ + ‖(((a i)⁻¹ : ℂˣ) : ℂ)‖)
  have hφ : Continuous φ := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact (Units.continuous_val.comp (continuous_apply i)).norm.add
      (Units.continuous_val.comp ((continuous_apply i).inv)).norm
  obtain ⟨R₀, hR₀⟩ := (hK.image hφ).bddAbove
  set R := max R₀ 0
  have hbd : ∀ a ∈ K, ∀ i, ‖(a i : ℂ)‖ ≤ R ∧ ‖(((a i)⁻¹ : ℂˣ) : ℂ)‖ ≤ R := by
    intro a ha i
    have h1 : φ a ≤ R₀ := hR₀ ⟨a, ha, rfl⟩
    have h2 : ‖(a i : ℂ)‖ + ‖(((a i)⁻¹ : ℂˣ) : ℂ)‖ ≤ φ a :=
      Finset.single_le_sum (f := fun j => ‖(a j : ℂ)‖ + ‖(((a j)⁻¹ : ℂˣ) : ℂ)‖)
        (fun j _ => by positivity) (Finset.mem_univ i)
    have := le_max_left R₀ 0
    constructor <;> linarith [norm_nonneg (a i : ℂ), norm_nonneg (((a i)⁻¹ : ℂˣ) : ℂ)]
  have hR : 0 ≤ R := le_max_right _ _
  set C : ℝ≥0∞ := ∏ _i : ι, ENNReal.ofReal R ^ 2
  have hKm : MeasurableSet (toUnits ⁻¹' K : Set (ι → ℂ)) := measurable_toUnits hK.isClosed.measurableSet
  rw [unitsHaar, map_apply measurable_toUnits hK.isClosed.measurableSet, wVol,
    withDensity_apply _ hKm, ← lintegral_indicator hKm]
  have hle : ∀ᵐ b ∂(volume : Measure (ι → ℂ)),
      (toUnits ⁻¹' K).indicator invSqWt b ≤ (Metric.closedBall 0 R).indicator (fun _ => C) b := by
    filter_upwards [ae_ne_zero] with b hb
    by_cases hbK : toUnits b ∈ K
    · have hval : ∀ i, ((toUnits b i : ℂˣ) : ℂ) = b i := fun i => by simp [toUnits, hb i]
      have hval' : ∀ i, (((toUnits b i)⁻¹ : ℂˣ) : ℂ) = (b i)⁻¹ := fun i => by simp [toUnits, hb i]
      have hball : b ∈ Metric.closedBall (0 : ι → ℂ) R := by
        rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR]
        intro i
        rw [← hval i]
        exact (hbd _ hbK i).1
      rw [indicator_of_mem (show b ∈ toUnits ⁻¹' K from hbK), indicator_of_mem hball, invSqWt]
      refine Finset.prod_le_prod' fun i _ => ?_
      gcongr
      rw [← enorm_inv (hb i), ← hval' i, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hbd _ hbK i).2
    · rw [indicator_of_notMem (show b ∉ toUnits ⁻¹' K from hbK)]
      exact bot_le
  refine (lintegral_mono_ae hle).trans_lt ?_
  rw [lintegral_indicator_const measurableSet_closedBall]
  exact ENNReal.mul_lt_top (ENNReal.prod_ne_top fun i _ => ENNReal.pow_ne_top ENNReal.ofReal_ne_top).lt_top
    measure_closedBall_lt_top

theorem unitsHaar_ne_zero : unitsHaar ι ≠ 0 := by
  intro h
  have h1 : unitsHaar ι univ = 0 := by rw [h]; rfl
  rw [unitsHaar, map_apply measurable_toUnits MeasurableSet.univ, preimage_univ, wVol,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_eq_zero_iff measurable_invSqWt] at h1
  have hpos : ∀ b : ι → ℂ, invSqWt b ≠ 0 := fun b =>
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (ENNReal.inv_ne_zero.2 enorm_ne_top)
  have hF : ∀ᵐ b ∂(volume : Measure (ι → ℂ)), False := h1.mono fun b hb => hpos b hb
  exact NeZero.ne (volume : Measure (ι → ℂ)) (ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 hF))

def decay (z N : ℕ) (a : ι → ℂˣ) : ℝ := (∏ i, ‖(a i : ℂ)‖ ^ 2) ^ z / (1 + ∑ i, ‖(a i : ℂ)‖) ^ N

theorem continuous_decay (z N : ℕ) : Continuous (decay (ι := ι) z N) := by
  have hc : ∀ i, Continuous fun a : ι → ℂˣ => ‖(a i : ℂ)‖ := fun i =>
    (Units.continuous_val.comp (continuous_apply i)).norm
  refine ((continuous_finset_prod _ fun i _ => (hc i).pow 2).pow z).div
    ((continuous_const.add (continuous_finsetSum _ fun i _ => hc i)).pow N) fun a => ?_
  positivity

theorem decay_bound (k : ℕ) (x : ι → ℝ) (hx : ∀ i, 0 < x i) :
    (∏ i, (x i ^ 2)⁻¹) * ((∏ i, x i ^ 2) ^ (k + 1) / (1 + ∑ i, x i) ^ ((2 * k + 3) * Fintype.card ι)) ≤
      ∏ i, (1 + x i) ^ (-(3 : ℝ)) := by
  set S := 1 + ∑ i, x i with hSdef
  have hS : ∀ i, 1 + x i ≤ S := fun i => by
    have := Finset.single_le_sum (f := x) (fun j _ => (hx j).le) (Finset.mem_univ i)
    linarith
  have hpos : ∀ i, 0 < 1 + x i := fun i => by linarith [hx i]
  have hS0 : 0 < S := by
    have : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => (hx i).le
    linarith
  rw [← Finset.prod_pow, pow_mul, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_div_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun i _ => by have := hx i; positivity) fun i _ => ?_
  have hxi := hx i
  have hxS : x i ≤ S := by linarith [hS i]
  have e1 : (x i ^ 2)⁻¹ * ((x i ^ 2) ^ (k + 1) / S ^ (2 * k + 3)) = (x i ^ 2) ^ k / S ^ (2 * k + 3) := by
    have hx2 : x i ^ 2 ≠ 0 := by positivity
    rw [pow_succ' (x i ^ 2) k, ← mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hx2, one_mul]
  have e2 : (1 + x i) ^ (-(3 : ℝ)) = ((1 + x i) ^ 3)⁻¹ := by
    rw [Real.rpow_neg (hpos i).le]; norm_cast
  rw [e1, e2]
  calc (x i ^ 2) ^ k / S ^ (2 * k + 3) ≤ (S ^ 2) ^ k / S ^ (2 * k + 3) := by gcongr
    _ = (S ^ 3)⁻¹ := by rw [← pow_mul, pow_add]; field_simp
    _ ≤ ((1 + x i) ^ 3)⁻¹ := by have := hpos i; gcongr; exact hS i

theorem integrable_decay (k : ℕ) :
    Integrable (decay (ι := ι) (k + 1) ((2 * k + 3) * Fintype.card ι)) (unitsHaar ι) := by
  set N := (2 * k + 3) * Fintype.card ι
  have hc := continuous_decay (ι := ι) (k + 1) N
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  have hh : Integrable (fun b : ι → ℂ => ∏ i, (1 + ‖b i‖) ^ (-(3 : ℝ))) (volume : Measure (ι → ℂ)) := by
    have := Integrable.fintype_prod (μ := fun _ : ι => (volume : Measure ℂ))
      (f := fun _ (x : ℂ) => (1 + ‖x‖) ^ (-(3 : ℝ))) fun _ =>
        integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)
    exact this
  unfold HasFiniteIntegral
  rw [unitsHaar, lintegral_map hc.measurable.enorm measurable_toUnits, wVol,
    lintegral_withDensity_eq_lintegral_mul _ measurable_invSqWt
      (g := fun b => ‖decay (k + 1) N (toUnits b)‖ₑ) (hc.measurable.enorm.comp measurable_toUnits)]
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) hh.2
  filter_upwards [ae_ne_zero] with b hb
  have hval : ∀ i, ((toUnits b i : ℂˣ) : ℂ) = b i := fun i => by simp [toUnits, hb i]
  have hx : ∀ i, 0 < ‖b i‖ := fun i => norm_pos_iff.2 (hb i)
  have hd : decay (k + 1) N (toUnits b) = (∏ i, ‖b i‖ ^ 2) ^ (k + 1) / (1 + ∑ i, ‖b i‖) ^ N := by
    simp only [decay, hval]
  have hw : invSqWt b = ENNReal.ofReal (∏ i, (‖b i‖ ^ 2)⁻¹) := by
    rw [invSqWt, ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_inv_of_pos (by have := hx i; positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
      ENNReal.inv_pow]
  have h1 : 0 ≤ decay (k + 1) N (toUnits b) := by rw [hd]; positivity
  have h2 : 0 ≤ ∏ i, (1 + ‖b i‖) ^ (-(3 : ℝ)) := Finset.prod_nonneg fun i _ => by positivity
  simp only [Pi.mul_apply, Function.comp]
  rw [hw, Real.enorm_eq_ofReal h1, Real.enorm_eq_ofReal h2, ← ENNReal.ofReal_mul (by positivity), hd]
  exact ENNReal.ofReal_le_ofReal (decay_bound k (fun i => ‖b i‖) hx)

section Ideles

open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem absE_of_mem_arch {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {l : (AE F E)ˣ} (hl : l ∈ idelesAt E (evI F)) :
    (absE F E l : ℝ) = ∏ w, ‖piInf (τ w) l.1‖ ^ 2 := by
  have hfin : ∀ v, GlobalTheory.Doubling.unitFin F E v l = 1 := fun v => by
    have := (at_evI_iff.1 hl) v
    rw [map_sub, map_one, sub_eq_zero] at this
    exact Units.ext this
  rw [GlobalTheory.Doubling.absE_apply, finprod_eq_one_of_forall_eq_one (fun v => by rw [hfin v, map_one]), mul_one]
  push_cast
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [GlobalTheory.Doubling.absEw_eq_sq hcm (τ w)]
  push_cast
  rfl

theorem exists_archEquiv {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ e : idelesAt E (evI F) ≃ₜ* (InfinitePlace F → ℂˣ), ∀ l w, ((e l w : ℂˣ) : ℂ) = piInf (τ w) l.1.1 := by
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
  let φ : idelesAt E (evI F) →* (InfinitePlace F → ℂˣ) :=
    MonoidHom.pi fun w => (Units.map (piInf (τ w)).toMonoidHom).comp (idelesAt E (evI F)).subtype
  have hφ : ∀ l w, ((φ l w : ℂˣ) : ℂ) = piInf (τ w) l.1.1 := fun _ _ => rfl
  have hφc : Continuous φ := continuous_pi fun w =>
    (Continuous.units_map _ (GlobalTheory.Grow.continuous_infEmb_compInf F w (τ w))).comp continuous_subtype_val
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have h1 : l.1.1 - 1 = 0 := GlobalTheory.ArchInj.eq_zero_of_at_of_piInf F E σ hcm τ _ l.2 fun w => by
      rw [map_sub, map_one, sub_eq_zero, ← hφ, hl]
      rfl
    exact Subtype.ext (Units.ext (sub_eq_zero.1 h1))
  have hsurj : Function.Surjective φ := by
    intro a
    obtain ⟨t, ht, htw⟩ := exists_unit_at_evI_piInf_eq σ τ (fun w => (a w : ℂ)) hcm fun w => (a w).ne_zero
    exact ⟨⟨t, ht⟩, funext fun w => Units.ext (htw w)⟩
  have ho : IsOpenMap φ := φ.isOpenMap_of_sigmaCompact hsurj hφc
  let hh := (Equiv.ofBijective φ ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hφc ho
  exact ⟨{ MulEquiv.ofBijective φ ⟨hinj, hsurj⟩ with continuous_toFun := hφc, continuous_invFun := hh.symm.continuous }, hφ⟩

end Ideles

theorem integrable_absE_pow_div : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ (μ : Measure (idelesAt E (evI F))), μ.IsHaarMeasure → ∀ z : ℕ, 1 ≤ z →
    ∃ N : ℕ, Integrable (fun l : idelesAt E (evI F) => (GlobalTheory.Doubling.absE F E l.1 : ℝ) ^ z /
      (1 + ∑ w, ‖piInf (B.emb w) (l.1 : AE F E)‖) ^ N) μ := by
  intro F E _ _ _ _ _ σ B hB μ hμ z hz
  obtain ⟨_, _, _, _, _⟩ := idelesAt_facts E (evI F)
  have hcm : IsCMExt F E σ := hB.cm
  obtain ⟨k, rfl⟩ : ∃ k, z = k + 1 := ⟨z - 1, by omega⟩
  obtain ⟨e, he⟩ := exists_archEquiv hcm B.emb
  haveI := e.isHaarMeasure_map μ
  have hsm := isMulLeftInvariant_eq_smul (unitsHaar (InfinitePlace F)) (μ.map e)
  set c := haarScalarFactor (unitsHaar (InfinitePlace F)) (μ.map e)
  have hc0 : c ≠ 0 := by
    intro h
    apply unitsHaar_ne_zero (ι := InfinitePlace F)
    rw [hsm, h, zero_smul]
  have hν : μ.map e = (c⁻¹ : NNReal) • unitsHaar (InfinitePlace F) := by
    rw [hsm, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  refine ⟨(2 * k + 3) * Fintype.card (InfinitePlace F), ?_⟩
  have hI := integrable_decay (ι := InfinitePlace F) k
  have hI' : Integrable (decay (k + 1) ((2 * k + 3) * Fintype.card (InfinitePlace F))) (μ.map e) := by
    rw [hν]; exact hI.smul_measure_nnreal
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  rw [hme.integrable_map_iff] at hI'
  convert hI' using 1
  funext l
  simp only [Function.comp, decay, he, absE_of_mem_arch hcm B.emb l.2]

end GlobalTheory.ArchIdeleDecay
