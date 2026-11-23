import Mathlib
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsBase
import GroundTheory.AutomorphicForms.CuspidalDiscreteness
import GroundTheory.AutomorphicForms.NormDetDiagUnitsPosRealToUnits

open MeasureTheory Set Filter Topology Function
open scoped ENNReal NNReal

namespace GroundTheory.Automorphic

noncomputable section

namespace CuspidalSpectrum

open AutomorphicForm Reduction GroundTheory.Global

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

variable (K n) in

def infPart : AdelicGLn.AdelicGL K n →* archGroup K n :=
  (archEquiv K n).toMulEquiv.toMonoidHom.comp
    ((MonoidHom.fst _ _).comp (AdelicGLn.prodEquiv K n).toMulEquiv.toMonoidHom)

variable (K n) in

def finPart : AdelicGLn.AdelicGL K n →* AdelicGLn.FiniteAdelicGL K n :=
  (MonoidHom.snd _ _).comp (AdelicGLn.prodEquiv K n).toMulEquiv.toMonoidHom

theorem infPart_apply (g : AdelicGLn.AdelicGL K n) :
    infPart K n g = archEquiv K n (AdelicGLn.prodEquiv K n g).1 := rfl

theorem finPart_apply (g : AdelicGLn.AdelicGL K n) :
    finPart K n g = (AdelicGLn.prodEquiv K n g).2 := rfl

theorem continuous_infPart : Continuous (infPart K n) :=
  (archEquiv K n).continuous.comp (continuous_fst.comp (AdelicGLn.prodEquiv K n).continuous)

theorem continuous_finPart : Continuous (finPart K n) :=
  continuous_snd.comp (AdelicGLn.prodEquiv K n).continuous

theorem infEmb_infPart_mul_finEmb_finPart (g : AdelicGLn.AdelicGL K n) :
    infEmb K n (infPart K n g) * finEmb K n (finPart K n g) = g :=
  infEmb_mul_finEmb g

@[simp] theorem infPart_infEmb (a : archGroup K n) : infPart K n (infEmb K n a) = a := by
  rw [infPart_apply, prodEquiv_infEmb, ContinuousMulEquiv.apply_symm_apply]

@[simp] theorem finPart_infEmb (a : archGroup K n) : finPart K n (infEmb K n a) = 1 := by
  rw [finPart_apply, prodEquiv_infEmb]

@[simp] theorem infPart_finEmb (h : AdelicGLn.FiniteAdelicGL K n) : infPart K n (finEmb K n h) = 1 := by
  rw [infPart_apply, prodEquiv_finEmb, map_one]

@[simp] theorem finPart_finEmb (h : AdelicGLn.FiniteAdelicGL K n) : finPart K n (finEmb K n h) = h := by
  rw [finPart_apply, prodEquiv_finEmb]

theorem ext_parts {g g' : AdelicGLn.AdelicGL K n} (h1 : infPart K n g = infPart K n g')
    (h2 : finPart K n g = finPart K n g') : g = g' := by
  rw [← infEmb_infPart_mul_finEmb_finPart g, ← infEmb_infPart_mul_finEmb_finPart g', h1, h2]

@[simp] theorem finPart_centralSection (s : {r : ℝ // 0 < r}) : finPart K n (centralSection K n s) = 1 := by
  rw [finPart_apply]
  exact prodEquiv_diagUnits_posIdele_snd (K := K) (n := n)
    (fun _ => ((rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ s : {r : ℝ // 0 < r}) : ℝ)) (fun _ => (rpowHom _ s).2)

variable (K n) in

def zInf : {r : ℝ // 0 < r} →* archGroup K n := (infPart K n).comp (centralSection K n)

theorem continuous_zInf : Continuous (zInf K n) :=
  continuous_infPart.comp continuous_centralSection

theorem infEmb_zInf (s : {r : ℝ // 0 < r}) : infEmb K n (zInf K n s) = centralSection K n s := by
  conv_rhs => rw [← infEmb_infPart_mul_finEmb_finPart (centralSection K n s)]
  rw [finPart_centralSection, map_one, mul_one]
  rfl

theorem zInf_mul_comm (s : {r : ℝ // 0 < r}) (a : archGroup K n) : zInf K n s * a = a * zInf K n s := by
  apply infEmb_injective
  rw [map_mul, map_mul, infEmb_zInf, centralSection_mul_comm]

variable (K n) in

def detA : archGroup K n →* {r : ℝ // 0 < r} := (detModule K n).comp (infEmb K n)

theorem continuous_detA : Continuous (detA K n) :=
  continuous_detModule.comp continuous_infEmb

theorem detA_zInf (hn : 0 < n) (s : {r : ℝ // 0 < r}) : detA K n (zInf K n s) = s := by
  rw [detA, MonoidHom.comp_apply, infEmb_zInf, detModule_centralSection hn]

theorem detModule_finEmb {h : AdelicGLn.FiniteAdelicGL K n} (hh : h ∈ AdelicGLn.integralFiniteGL K n) :
    detModule K n (finEmb K n h) = 1 :=
  (mem_normOneGL_iff_detModule).1 (finOne K n ⟨h, hh⟩).2

theorem mul_centralSection_detModule_inv_mem (g : AdelicGLn.AdelicGL K n) :
    g * (centralSection K n (detModule K n g))⁻¹ ∈ normOneGL K n := by
  rw [mem_normOneGL_iff_detModule, map_mul, map_inv]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : Subsingleton (AdelicGLn.AdelicGL K 0) :=
      ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
    rw [Subsingleton.elim g 1, Subsingleton.elim (centralSection K 0 _) 1]
    simp
  · rw [detModule_centralSection hn, mul_inv_cancel]

def retractOne (g : AdelicGLn.AdelicGL K n) : normOneGL K n :=
  ⟨g * (centralSection K n (detModule K n g))⁻¹, mul_centralSection_detModule_inv_mem g⟩

theorem coe_retractOne (g : AdelicGLn.AdelicGL K n) :
    (retractOne g : AdelicGLn.AdelicGL K n) = g * (centralSection K n (detModule K n g))⁻¹ := rfl

theorem continuous_retractOne : Continuous (retractOne (K := K) (n := n)) :=
  continuous_induced_rng.2 (continuous_id.mul
    ((continuous_centralSection.comp continuous_detModule).inv))

theorem retractOne_mul_finEmb (g : AdelicGLn.AdelicGL K n) {u : AdelicGLn.FiniteAdelicGL K n}
    (hu : u ∈ AdelicGLn.integralFiniteGL K n) :
    retractOne (g * finEmb K n u) = retractOne g * finOne K n ⟨u, hu⟩ := by
  have h1 : detModule K n (finEmb K n u) = 1 :=
    (mem_normOneGL_iff_detModule).1 (finOne K n ⟨u, hu⟩).2
  ext1
  rw [coe_retractOne, Subgroup.coe_mul, coe_retractOne, coe_finOne, map_mul, h1, mul_one, mul_assoc,
    ← centralSection_inv_mul_comm, ← mul_assoc]

def finOpenSubgroup (U : Subgroup (AdelicGLn.integralFiniteGL K n))
    (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n))) :
    OpenSubgroup (AdelicGLn.FiniteAdelicGL K n) where
  toSubgroup := U.map (AdelicGLn.integralFiniteGL K n).subtype
  isOpen' := by
    change IsOpen ((U.map (AdelicGLn.integralFiniteGL K n).subtype : Subgroup _) :
      Set (AdelicGLn.FiniteAdelicGL K n))
    rw [Subgroup.coe_map, Subgroup.coe_subtype]
    exact (AdelicGLn.isOpen_integralFiniteGL K n).isOpenMap_subtype_val _ hU

theorem retract_infEmb (a : archGroup K n) : retractOne (infEmb K n a) = archP K n a := by
  ext1
  rfl

theorem finPart_retract (g : AdelicGLn.AdelicGL K n) : finPart K n (retractOne g : AdelicGLn.AdelicGL K n) =
    finPart K n g := by
  rw [coe_retractOne, map_mul, map_inv, finPart_centralSection, inv_one, mul_one]

theorem infPart_archP (a : archGroup K n) :
    infPart K n (archP K n a : AdelicGLn.AdelicGL K n) = a * (zInf K n (detA K n a))⁻¹ := by
  rw [← retract_infEmb, coe_retractOne, map_mul, map_inv, infPart_infEmb]
  rfl

theorem finPart_archP (a : archGroup K n) : finPart K n (archP K n a : AdelicGLn.AdelicGL K n) = 1 := by
  rw [← retract_infEmb, finPart_retract, finPart_infEmb]

theorem archimedeanProjection_mul_positiveScalar (hn : 0 < n) (a : archGroup K n) (s : {r : ℝ // 0 < r}) :
    archP K n (a * zInf K n s) = archP K n a := by
  have h1 : archP K n (zInf K n s) = 1 := by
    rw [← retract_infEmb, infEmb_zInf]
    ext1
    rw [coe_retractOne, detModule_centralSection hn, mul_inv_cancel]
    rfl
  rw [map_mul, h1, mul_one]

theorem archimedeanProjection_mul_finiteEmbedding_comm (a : archGroup K n) (u : AdelicGLn.integralFiniteGL K n) :
    archP K n a * finOne K n u = finOne K n u * archP K n a := by
  ext1
  exact archProj_mul_finEmb_comm (K := K) (n := n) (a : ArchUnits K n) (u : AdelicGLn.FiniteAdelicGL K n)

theorem integrable_of_bound_of_compact {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {m : Measure X} [IsFiniteMeasureOnCompacts m] {f : X → ℂ}
    (hf : AEStronglyMeasurable f m) {C : Set X} (hC : IsCompact C) (M : ℝ) (hM : ∀ x ∈ C, ‖f x‖ ≤ M)
    (h0 : ∀ x ∉ C, f x = 0) : Integrable f m := by
  have hon : IntegrableOn f C m :=
    Measure.integrableOn_of_bounded hC.measure_lt_top.ne hf
      (ae_restrict_of_forall_mem hC.isClosed.measurableSet hM)
  exact hon.integrable_of_forall_notMem_eq_zero h0

theorem preimage_expPos_posRealUnitInterval : expPos ⁻¹' posRealUnitInterval = Icc (0 : ℝ) 1 := by
  ext x
  simp only [posRealUnitInterval, mem_preimage, mem_Icc, coe_expPos]
  rw [Real.one_le_exp_iff, Real.exp_le_exp]

theorem isCompact_posRealUnitInterval : IsCompact posRealUnitInterval := by
  have h : posRealUnitInterval = expPosHomeomorph '' Icc (0 : ℝ) 1 := by
    rw [← preimage_expPos_posRealUnitInterval]
    exact (expPosHomeomorph.image_preimage _).symm
  rw [h]
  exact isCompact_Icc.image expPosHomeomorph.continuous

theorem integral_indicator_inv_mul (r : {r : ℝ // 0 < r}) :
    ∫ s, posRealUnitInterval.indicator (fun _ => (1 : ℂ)) (s⁻¹ * r) ∂posRealMeasure = 1 := by
  have hm : MeasurableSet ((fun s : {r : ℝ // 0 < r} => s⁻¹ * r) ⁻¹' posRealUnitInterval) :=
    (measurable_inv.mul_const r) measurableSet_posRealUnitInterval
  have e1 : (fun s : {r : ℝ // 0 < r} => posRealUnitInterval.indicator (fun _ => (1 : ℂ)) (s⁻¹ * r)) =
      ((fun s : {r : ℝ // 0 < r} => s⁻¹ * r) ⁻¹' posRealUnitInterval).indicator (fun _ => (1 : ℂ)) := by
    funext s
    rfl
  rw [e1, integral_indicator_const _ hm, measureReal_def]
  have hpre : expPos ⁻¹' ((fun s : {r : ℝ // 0 < r} => s⁻¹ * r) ⁻¹' posRealUnitInterval) =
      Icc (Real.log r - 1) (Real.log r) := by
    ext x
    simp only [posRealUnitInterval, mem_preimage, mem_Icc]
    have hval : (((expPos x)⁻¹ * r : {r : ℝ // 0 < r}) : ℝ) = (Real.exp x)⁻¹ * r := rfl
    rw [hval]
    have hex := Real.exp_pos x
    have hr := r.2
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · rw [sub_le_iff_le_add, Real.log_le_iff_le_exp hr, Real.exp_add]
        rw [inv_mul_le_iff₀ hex] at h2
        linarith
      · rw [Real.le_log_iff_exp_le hr]
        rw [le_inv_mul_iff₀ hex] at h1
        linarith
    · rintro ⟨h1, h2⟩
      constructor
      · rw [le_inv_mul_iff₀ hex, mul_one]
        exact (Real.le_log_iff_exp_le hr).1 h2
      · rw [inv_mul_le_iff₀ hex]
        rw [sub_le_iff_le_add, Real.log_le_iff_le_exp hr, Real.exp_add] at h1
        linarith
  rw [posRealMeasure_eq_map_expPos, Measure.map_apply measurable_expPos hm, hpre, Real.volume_Icc]
  norm_num

def kbar (κ : archGroup K n → ℂ) (a : archGroup K n) : ℂ :=
  ∫ s, κ (a * zInf K n s) ∂posRealMeasure

theorem kbar_mul_zInf (κ : archGroup K n → ℂ) (a : archGroup K n) (t : {r : ℝ // 0 < r}) :
    kbar κ (a * zInf K n t) = kbar κ a := by
  unfold kbar
  simp_rw [mul_assoc, ← map_mul]
  exact integral_mul_left_eq_self (fun s => κ (a * zInf K n s)) t

theorem mem_of_kernel_ne_zero (hn : 0 < n) {κ : archGroup K n → ℂ} {a : archGroup K n}
    {s : {r : ℝ // 0 < r}} (h : κ (a * zInf K n s) ≠ 0) :
    s * detA K n a ∈ detA K n '' tsupport κ :=
  ⟨a * zInf K n s, subset_tsupport _ h, by rw [map_mul, detA_zInf hn, mul_comm]⟩

theorem continuous_kbar (hn : 0 < n) {κ : archGroup K n → ℂ} (hκ : Continuous κ)
    (hκc : HasCompactSupport κ) : Continuous (kbar κ) := by
  rw [continuous_iff_continuousAt]
  intro a₀
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds a₀
  set D := detA K n '' tsupport κ with hDdef
  have hD : IsCompact D := hκc.isCompact.image continuous_detA
  set R := detA K n '' N with hRdef
  have hR : IsCompact R := hNc.image continuous_detA
  set T := (fun p : {r : ℝ // 0 < r} × {r : ℝ // 0 < r} => p.1 * p.2⁻¹) '' (D ×ˢ R) with hTdef
  have hT : IsCompact T := (hD.prod hR).image (continuous_fst.mul continuous_snd.inv)
  have hcont : Continuous (fun a => ∫ s in T, κ (a * zInf K n s) ∂posRealMeasure) :=
    continuous_parametric_integral_of_continuous
      (by exact hκ.comp (continuous_fst.mul (continuous_zInf.comp continuous_snd))) hT
  refine hcont.continuousAt.congr ?_
  filter_upwards [hN] with a ha
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun s hs => ?_
  by_contra hne
  apply hs
  refine ⟨(s * detA K n a, detA K n a), ⟨mem_of_kernel_ne_zero hn hne, a, ha, rfl⟩, ?_⟩
  simp only [mul_inv_cancel_right]

theorem integral_indicator_kbar (hn : 0 < n) {κ : archGroup K n → ℂ} (hκ : Continuous κ)
    (hκc : HasCompactSupport κ) {Ψ : archGroup K n → ℂ} (hΨ : Continuous Ψ)
    (hΨz : ∀ a s, Ψ (a * zInf K n s) = Ψ a) (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] :
    ∫ a, posRealUnitInterval.indicator (fun _ => (1 : ℂ)) (detA K n a) * (kbar κ a * Ψ a) ∂ν =
      ∫ a, κ a * Ψ a ∂ν := by
  set I := posRealUnitInterval
  set ρ : Measure {r : ℝ // 0 < r} := posRealMeasure
  set D := detA K n '' tsupport κ with hDdef
  have hD : IsCompact D := hκc.isCompact.image continuous_detA
  have hI : IsCompact I := isCompact_posRealUnitInterval
  set T := (fun p : {r : ℝ // 0 < r} × {r : ℝ // 0 < r} => p.1 * p.2⁻¹) '' (D ×ˢ I) with hTdef
  have hT : IsCompact T := (hD.prod hI).image (continuous_fst.mul continuous_snd.inv)
  obtain ⟨Mκ, hMκ⟩ := hκ.bounded_above_of_compact_support hκc
  have hmind : Measurable fun a : archGroup K n => I.indicator (fun _ => (1 : ℂ)) (detA K n a) :=
    (measurable_const.indicator measurableSet_posRealUnitInterval).comp continuous_detA.measurable
  have hind1 : ∀ r, ‖I.indicator (fun _ => (1 : ℂ)) r‖ ≤ 1 := by
    intro r
    by_cases hr : r ∈ I <;> simp [indicator, hr]

  set G : archGroup K n × {r : ℝ // 0 < r} → ℂ :=
    fun p => I.indicator (fun _ => (1 : ℂ)) (detA K n p.1) * κ (p.1 * zInf K n p.2) * Ψ p.1 with hGdef
  set A1 := (fun q : archGroup K n × {r : ℝ // 0 < r} => q.1 * (zInf K n q.2)⁻¹) '' (tsupport κ ×ˢ T)
  have hA1 : IsCompact A1 := (hκc.isCompact.prod hT).image
    (continuous_fst.mul (continuous_zInf.comp continuous_snd).inv)
  obtain ⟨MΨ, hMΨ⟩ := hA1.exists_bound_of_continuousOn hΨ.continuousOn
  have hGint : Integrable G (ν.prod ρ) := by
    refine integrable_of_bound_of_compact ?_ (hA1.prod hT) (1 * Mκ * MΨ) ?_ ?_
    · exact ((hmind.comp measurable_fst).mul
        (hκ.comp (continuous_fst.mul (continuous_zInf.comp continuous_snd))).measurable |>.mul
        (hΨ.measurable.comp measurable_fst)).aestronglyMeasurable
    · rintro ⟨a, s⟩ ⟨ha, -⟩
      simp only [hGdef, norm_mul]
      exact mul_le_mul (mul_le_mul (hind1 _) (hMκ _) (norm_nonneg _) zero_le_one) (hMΨ a ha)
        (norm_nonneg _) (mul_nonneg zero_le_one ((norm_nonneg _).trans (hMκ 1)))
    · rintro ⟨a, s⟩ hp
      by_contra hne
      apply hp
      have h1 : detA K n a ∈ I := by
        by_contra hI'
        apply hne
        simp [hGdef, indicator, hI']
      have h2 : κ (a * zInf K n s) ≠ 0 := by
        intro h0
        apply hne
        simp [hGdef, h0]
      have hsT : s ∈ T := ⟨(s * detA K n a, detA K n a), ⟨mem_of_kernel_ne_zero hn h2, h1⟩,
        by simp only [mul_inv_cancel_right]⟩
      refine ⟨⟨(a * zInf K n s, s), ⟨subset_tsupport _ h2, hsT⟩, ?_⟩, hsT⟩
      simp only [mul_inv_cancel_right]

  set H : archGroup K n × {r : ℝ // 0 < r} → ℂ :=
    fun p => I.indicator (fun _ => (1 : ℂ)) (p.2⁻¹ * detA K n p.1) * (κ p.1 * Ψ p.1) with hHdef
  obtain ⟨MΨ', hMΨ'⟩ := hκc.isCompact.exists_bound_of_continuousOn hΨ.continuousOn
  have hHint : Integrable H (ν.prod ρ) := by
    refine integrable_of_bound_of_compact ?_ (hκc.isCompact.prod hT) (1 * (Mκ * MΨ')) ?_ ?_
    · exact (((measurable_const.indicator measurableSet_posRealUnitInterval).comp
        (measurable_snd.inv.mul (continuous_detA.measurable.comp measurable_fst))).mul
        ((hκ.measurable.comp measurable_fst).mul (hΨ.measurable.comp measurable_fst))).aestronglyMeasurable
    · rintro ⟨a, s⟩ ⟨ha, -⟩
      simp only [hHdef, norm_mul]
      exact mul_le_mul (hind1 _) (mul_le_mul (hMκ _) (hMΨ' a ha) (norm_nonneg _)
        ((norm_nonneg _).trans (hMκ 1))) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
    · rintro ⟨a, s⟩ hp
      by_contra hne
      apply hp
      have h1 : s⁻¹ * detA K n a ∈ I := by
        by_contra hI'
        apply hne
        simp [hHdef, indicator, hI']
      have h2 : κ a ≠ 0 := by
        intro h0
        apply hne
        simp [hHdef, h0]
      refine ⟨subset_tsupport _ h2, (detA K n a, s⁻¹ * detA K n a), ⟨⟨a, subset_tsupport _ h2, rfl⟩, h1⟩, ?_⟩
      simp only [mul_inv_rev, inv_inv, mul_inv_cancel_left]

  have e1 : ∀ a, I.indicator (fun _ => (1 : ℂ)) (detA K n a) * (kbar κ a * Ψ a) =
      ∫ s, G (a, s) ∂ρ := by
    intro a
    simp only [hGdef, kbar]
    rw [← integral_mul_const, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only
    ring
  have e2 : ∀ s : {r : ℝ // 0 < r}, ∫ a, G (a, s) ∂ν = ∫ a, H (a, s) ∂ν := by
    intro s
    rw [← integral_mul_left_eq_self (fun a => G (a, s)) (zInf K n s)⁻¹]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    have hc : (zInf K n s)⁻¹ * a = a * (zInf K n s)⁻¹ := by
      rw [← map_inv, zInf_mul_comm]
    simp only [hGdef, hHdef, hc, inv_mul_cancel_right]
    rw [← map_inv, hΨz, map_mul, detA_zInf hn, mul_comm (detA K n a)]
    ring
  have e3 : ∀ a, ∫ s, H (a, s) ∂ρ = κ a * Ψ a := by
    intro a
    simp only [hHdef]
    rw [integral_mul_const, integral_indicator_inv_mul, one_mul]
  calc ∫ a, I.indicator (fun _ => (1 : ℂ)) (detA K n a) * (kbar κ a * Ψ a) ∂ν
      = ∫ a, ∫ s, G (a, s) ∂ρ ∂ν := integral_congr_ae (Eventually.of_forall e1)
    _ = ∫ s, ∫ a, G (a, s) ∂ν ∂ρ := integral_integral_swap (by exact hGint)
    _ = ∫ s, ∫ a, H (a, s) ∂ν ∂ρ := integral_congr_ae (Eventually.of_forall e2)
    _ = ∫ a, ∫ s, H (a, s) ∂ρ ∂ν := (integral_integral_swap (by exact hHint)).symm
    _ = ∫ a, κ a * Ψ a ∂ν := integral_congr_ae (Eventually.of_forall e3)

section F0

variable (U : Subgroup (AdelicGLn.integralFiniteGL K n))
  (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))

def finUSet : Set (normOneGL K n) :=
  {x | finPart K n x ∈ (finOpenSubgroup U hU : Set (AdelicGLn.FiniteAdelicGL K n))}

theorem isClopen_finUSet : IsClopen (finUSet U hU) :=
  (finOpenSubgroup U hU).isClopen.preimage (continuous_finPart.comp continuous_subtype_val)

theorem coe_openSubgroupOf :
    (finOpenSubgroup U hU : Set (AdelicGLn.FiniteAdelicGL K n)) =
      Subtype.val '' (U : Set (AdelicGLn.integralFiniteGL K n)) := by
  change ((U.map (AdelicGLn.integralFiniteGL K n).subtype : Subgroup _) :
    Set (AdelicGLn.FiniteAdelicGL K n)) = _
  rw [Subgroup.coe_map, Subgroup.coe_subtype]

theorem isCompact_openSubgroupOf :
    IsCompact (finOpenSubgroup U hU : Set (AdelicGLn.FiniteAdelicGL K n)) := by
  have : CompactSpace (AdelicGLn.integralFiniteGL K n) :=
    isCompact_iff_compactSpace.1 (AdelicGLn.isCompact_integralFiniteGL K n)
  rw [coe_openSubgroupOf]
  exact (U.isClosed_of_isOpen hU).isCompact.image continuous_subtype_val

theorem openSubgroupOf_subset :
    (finOpenSubgroup U hU : Set (AdelicGLn.FiniteAdelicGL K n)) ⊆ AdelicGLn.integralFiniteGL K n := by
  rw [coe_openSubgroupOf]
  rintro _ ⟨u, -, rfl⟩
  exact u.2

theorem coe_mem_openSubgroupOf {u : AdelicGLn.integralFiniteGL K n} (hu : u ∈ U) :
    (u : AdelicGLn.FiniteAdelicGL K n) ∈ (finOpenSubgroup U hU : Set (AdelicGLn.FiniteAdelicGL K n)) := by
  rw [coe_openSubgroupOf]
  exact ⟨u, hu, rfl⟩

def F0fun (κ : archGroup K n → ℂ) (x : normOneGL K n) : ℂ :=
  (finUSet U hU).indicator (fun x : normOneGL K n => kbar κ (infPart K n x)) x

theorem continuous_F0fun (hn : 0 < n) {κ : archGroup K n → ℂ} (hκ : Continuous κ)
    (hκc : HasCompactSupport κ) : Continuous (F0fun U hU κ) :=
  (isClopen_finUSet U hU).continuous_indicator
    ((continuous_kbar hn hκ hκc).comp (continuous_infPart.comp continuous_subtype_val))

theorem detA_infPart {x : normOneGL K n} (hx : finPart K n x ∈ AdelicGLn.integralFiniteGL K n) :
    detA K n (infPart K n x) = 1 := by
  have h1 := (mem_normOneGL_iff_detModule).1 x.2
  rw [← infEmb_infPart_mul_finEmb_finPart (x : AdelicGLn.AdelicGL K n), map_mul,
    detModule_finEmb hx, mul_one] at h1
  exact h1

theorem hasCompactSupport_F0fun (hn : 0 < n) {κ : archGroup K n → ℂ} (hκc : HasCompactSupport κ) :
    HasCompactSupport (F0fun U hU κ) := by
  set Cinf := (fun y => y * (zInf K n (detA K n y))⁻¹) '' tsupport κ with hCinf
  have hCinfc : IsCompact Cinf := hκc.isCompact.image
    (continuous_id.mul ((continuous_zInf.comp continuous_detA).inv))
  set K₀ := (fun p : archGroup K n × AdelicGLn.FiniteAdelicGL K n => infEmb K n p.1 * finEmb K n p.2) ''
    (Cinf ×ˢ (finOpenSubgroup U hU : Set (AdelicGLn.FiniteAdelicGL K n))) with hK₀
  have hK₀c : IsCompact K₀ := (hCinfc.prod (isCompact_openSubgroupOf U hU)).image
    ((continuous_infEmb.comp continuous_fst).mul (continuous_finEmb.comp continuous_snd))
  have hKc : IsCompact ((Subtype.val : normOneGL K n → AdelicGLn.AdelicGL K n) ⁻¹' K₀) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage (by rw [Subtype.range_coe]; exact isClosed_normOneGL)
      hK₀c
  refine HasCompactSupport.intro hKc fun x hx => ?_
  by_contra hne
  apply hx
  have hxU : x ∈ finUSet U hU := by
    by_contra h0
    exact hne (by simp [F0fun, indicator, h0])
  have hk : kbar κ (infPart K n x) ≠ 0 := by
    intro h0
    exact hne (by simp [F0fun, indicator, hxU, h0])
  obtain ⟨s, hs⟩ : ∃ s, κ (infPart K n x * zInf K n s) ≠ 0 := by
    by_contra h0
    simp only [not_exists, ne_eq, not_not] at h0
    exact hk (by simp [kbar, h0])
  have hdet := detA_infPart (openSubgroupOf_subset U hU hxU)
  refine ⟨(infPart K n x, finPart K n x), ⟨⟨infPart K n x * zInf K n s, subset_tsupport _ hs, ?_⟩, hxU⟩,
    infEmb_infPart_mul_finEmb_finPart _⟩
  simp only [map_mul, hdet, one_mul, detA_zInf hn, mul_inv_cancel_right]

theorem F0fun_finOne_mul (κ : archGroup K n → ℂ) {u : AdelicGLn.integralFiniteGL K n} (hu : u ∈ U)
    (x : normOneGL K n) : F0fun U hU κ (finOne K n u * x) = F0fun U hU κ x := by
  have h1 : infPart K n ((finOne K n u * x : normOneGL K n) : AdelicGLn.AdelicGL K n) =
      infPart K n x := by
    rw [Subgroup.coe_mul, coe_finOne, map_mul, infPart_finEmb, one_mul]
  have h2 : finPart K n ((finOne K n u * x : normOneGL K n) : AdelicGLn.AdelicGL K n) =
      (u : AdelicGLn.FiniteAdelicGL K n) * finPart K n x := by
    rw [Subgroup.coe_mul, coe_finOne, map_mul, finPart_finEmb]
  have hmem : finOne K n u * x ∈ finUSet U hU ↔ x ∈ finUSet U hU := by
    simp only [finUSet, mem_ofPred_eq, h2]
    exact (finOpenSubgroup U hU).mul_mem_cancel_left (coe_mem_openSubgroupOf U hU hu)
  unfold F0fun
  by_cases hx : x ∈ finUSet U hU
  · rw [indicator_of_mem hx, indicator_of_mem (hmem.2 hx), h1]
  · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx (hmem.1 h))]

theorem F0fun_archP (κ : archGroup K n → ℂ) (a : archGroup K n) :
    F0fun U hU κ (archP K n a) = kbar κ a := by
  have hmem : archP K n a ∈ finUSet U hU := by
    simp only [finUSet, mem_ofPred_eq, finPart_archP]
    exact (finOpenSubgroup U hU).one_mem
  unfold F0fun
  rw [indicator_of_mem hmem, infPart_archP, ← map_inv, kbar_mul_zInf]

end F0

variable (K n) in

def infFinEquiv : archGroup K n × AdelicGLn.FiniteAdelicGL K n ≃ₜ* AdelicGLn.AdelicGL K n where
  toFun p := infEmb K n p.1 * finEmb K n p.2
  invFun g := (infPart K n g, finPart K n g)
  left_inv p := by
    refine Prod.ext ?_ ?_
    · simp only [map_mul, infPart_infEmb, infPart_finEmb, mul_one]
    · simp only [map_mul, finPart_infEmb, finPart_finEmb, one_mul]
  right_inv g := infEmb_infPart_mul_finEmb_finPart g
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_assoc]
    rw [← mul_assoc (infEmb K n q.1) (finEmb K n p.2), infEmb_mul_finEmb_comm, mul_assoc]
  continuous_toFun := (continuous_infEmb.comp continuous_fst).mul (continuous_finEmb.comp continuous_snd)
  continuous_invFun := continuous_infPart.prodMk continuous_finPart

theorem infFinEquiv_apply (p : archGroup K n × AdelicGLn.FiniteAdelicGL K n) :
    infFinEquiv K n p = infEmb K n p.1 * finEmb K n p.2 := rfl

theorem image_mul_centralSection_eq (hn : 0 < n) (E : Set (normOneGL K n)) :
    (fun p : normOneGL K n × {r : ℝ // 0 < r} => (p.1 : AdelicGLn.AdelicGL K n) * centralSection K n p.2) ''
        (E ×ˢ posRealUnitInterval) =
      retractOne ⁻¹' E ∩ detModule K n ⁻¹' posRealUnitInterval := by
  ext g
  constructor
  · rintro ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩
    have hd : detModule K n ((x : AdelicGLn.AdelicGL K n) * centralSection K n s) = s := by
      rw [map_mul, (mem_normOneGL_iff_detModule).1 x.2, detModule_centralSection hn, one_mul]
    have hr : retractOne ((x : AdelicGLn.AdelicGL K n) * centralSection K n s) = x := by
      ext1
      rw [coe_retractOne, hd, mul_inv_cancel_right]
    refine ⟨?_, ?_⟩
    · show retractOne _ ∈ E
      rw [hr]
      exact hx
    · show detModule K n _ ∈ posRealUnitInterval
      rw [hd]
      exact hs
  · rintro ⟨hE, hS⟩
    refine ⟨(retractOne g, detModule K n g), ⟨hE, hS⟩, ?_⟩
    show (retractOne g : AdelicGLn.AdelicGL K n) * centralSection K n (detModule K n g) = g
    rw [coe_retractOne, inv_mul_cancel_right]

theorem exists_eq_smul_map_retract (hn : 0 < n) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (μA : Measure (AdelicGLn.AdelicGL K n)) [μA.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      μ = c • Measure.map retractOne (μA.restrict (detModule K n ⁻¹' posRealUnitInterval)) := by
  obtain ⟨c, hc, hμ⟩ := exists_measure_eq_mul_measure_image hn μ μA
  have heq : μ = c • Measure.map retractOne (μA.restrict (detModule K n ⁻¹' posRealUnitInterval)) := by
    ext E hE
    rw [hμ E hE, image_mul_centralSection_eq hn, Measure.smul_apply,
      Measure.map_apply continuous_retractOne.measurable hE,
      Measure.restrict_apply (continuous_retractOne.measurable hE), smul_eq_mul]
  refine ⟨c, ?_, hc, heq⟩
  rintro rfl
  apply isOpen_univ.measure_ne_zero μ univ_nonempty
  rw [heq, zero_smul, Measure.coe_zero, Pi.zero_apply]

theorem exists_cc_integral_mul_eq_of_pos (hn : 0 < n) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
    (U : Subgroup (AdelicGLn.integralFiniteGL K n)) (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
    (κ : archGroup K n → ℂ) (hκ : Continuous κ) (hκc : HasCompactSupport κ) :
    ∃ (F₀ : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (c : ℝ), 0 < c ∧
      (∀ u ∈ U, ∀ x, F₀ (finOne K n u * x) = F₀ x) ∧
      ∀ Θ : normOneGL K n → ℂ, Continuous Θ → (∀ u ∈ U, ∀ x, Θ (x * finOne K n u) = Θ x) →
        ∫ x, F₀ x * Θ x ∂μ = c * ∫ a, κ a * Θ (archP K n a) ∂ν := by
  set μf : Measure (AdelicGLn.FiniteAdelicGL K n) := Measure.haar with hμf
  set m : Measure (archGroup K n × AdelicGLn.FiniteAdelicGL K n) := ν.prod μf with hmdef
  have hm : m.IsHaarMeasure := by rw [hmdef]; infer_instance
  set μA : Measure (AdelicGLn.AdelicGL K n) := Measure.map (infFinEquiv K n) m with hμAdef
  have hμA : μA.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map m (infFinEquiv K n)
  obtain ⟨c₁, hc₁0, hc₁, hμ⟩ := exists_eq_smul_map_retract hn μ μA
  set U' : Set (AdelicGLn.FiniteAdelicGL K n) :=
    (finOpenSubgroup U hU : Set (AdelicGLn.FiniteAdelicGL K n)) with hU'def
  have hU'o : IsOpen U' := (finOpenSubgroup U hU).isOpen
  have hU'm : MeasurableSet U' := hU'o.measurableSet
  have hU'0 : μf U' ≠ 0 := hU'o.measure_ne_zero μf ⟨1, (finOpenSubgroup U hU).one_mem⟩
  have hU'top : μf U' ≠ ⊤ := (isCompact_openSubgroupOf U hU).measure_lt_top.ne
  set F₀ : CompactlySupportedContinuousMap (normOneGL K n) ℂ :=
    ⟨⟨F0fun U hU κ, continuous_F0fun U hU hn hκ hκc⟩, hasCompactSupport_F0fun U hU hn hκc⟩ with hF₀
  have hF₀apply : ∀ x, F₀ x = F0fun U hU κ x := fun x => rfl
  refine ⟨F₀, c₁.toReal * (μf U').toReal,
    mul_pos (ENNReal.toReal_pos hc₁0 hc₁) (ENNReal.toReal_pos hU'0 hU'top),
    fun u hu x => F0fun_finOne_mul U hU κ hu x, fun Θ hΘ hΘU => ?_⟩
  set I := posRealUnitInterval
  set S := detModule K n ⁻¹' I with hSdef
  have hS : MeasurableSet S := continuous_detModule.measurable measurableSet_posRealUnitInterval
  set Ξ : normOneGL K n → ℂ := fun x => F₀ x * Θ x with hΞdef
  have hΞ : Continuous Ξ := F₀.continuous.mul hΘ
  have hΞc : HasCompactSupport Ξ := F₀.hasCompactSupport.mul_right
  set Fp : archGroup K n × AdelicGLn.FiniteAdelicGL K n → ℂ :=
    fun p => S.indicator (fun g => Ξ (retractOne g)) (infFinEquiv K n p) with hFpdef
  have hFm : Measurable (S.indicator (fun g => Ξ (retractOne g))) :=
    (hΞ.comp continuous_retractOne).measurable.indicator hS

  have hecont : Continuous (infFinEquiv K n) := (infFinEquiv K n).continuous
  have step1 : ∫ x, Ξ x ∂μ = c₁.toReal • ∫ p, Fp p ∂m := by
    rw [hμ, integral_smul_measure, integral_map continuous_retractOne.aemeasurable hΞ.aestronglyMeasurable,
      ← integral_indicator hS, hμAdef, integral_map hecont.aemeasurable hFm.aestronglyMeasurable]

  have hFpint : Integrable Fp m := by
    obtain ⟨M, hM⟩ := hΞ.bounded_above_of_compact_support hΞc
    have hC : IsCompact ((infFinEquiv K n) ⁻¹' (retractOne ⁻¹' tsupport Ξ ∩ S)) := by
      refine (infFinEquiv K n).toHomeomorph.isCompact_preimage.2 ?_
      rw [← image_mul_centralSection_eq hn]
      exact (hΞc.isCompact.prod isCompact_posRealUnitInterval).image
        ((continuous_subtype_val.comp continuous_fst).mul (continuous_centralSection.comp continuous_snd))
    refine integrable_of_bound_of_compact (hFm.comp (infFinEquiv K n).continuous.measurable).aestronglyMeasurable
      hC M (fun p _ => (norm_indicator_le_norm_self _ _).trans (hM _)) fun p hp => ?_
    simp only [hFpdef]
    by_contra hne
    apply hp
    have hpS : infFinEquiv K n p ∈ S := by
      by_contra h0
      exact hne (indicator_of_notMem h0 _)
    rw [indicator_of_mem hpS] at hne
    exact ⟨subset_tsupport _ hne, hpS⟩
  have step2 : ∫ p, Fp p ∂m = ∫ a, ∫ h, Fp (a, h) ∂μf ∂ν := integral_prod Fp hFpint

  have step3 : ∀ a : archGroup K n, ∫ h, Fp (a, h) ∂μf =
      (μf U').toReal • (I.indicator (fun _ => (1 : ℂ)) (detA K n a) * (kbar κ a * Θ (archP K n a))) := by
    intro a
    have hpt : ∀ h, Fp (a, h) =
        U'.indicator (fun _ => I.indicator (fun _ => (1 : ℂ)) (detA K n a) * (kbar κ a * Θ (archP K n a))) h := by
      intro h
      by_cases hh : h ∈ U'
      · rw [indicator_of_mem hh]
        have hh' : h ∈ Subtype.val '' (U : Set (AdelicGLn.integralFiniteGL K n)) := by
          rw [← coe_openSubgroupOf U hU]
          exact hh
        obtain ⟨u, hu, rfl⟩ := hh'
        have hr : retractOne (infFinEquiv K n (a, (u : AdelicGLn.FiniteAdelicGL K n))) =
            archP K n a * finOne K n u := by
          rw [infFinEquiv_apply, retractOne_mul_finEmb _ u.2, retract_infEmb]
        have hd : detModule K n (infFinEquiv K n (a, (u : AdelicGLn.FiniteAdelicGL K n))) = detA K n a := by
          rw [infFinEquiv_apply, map_mul, detModule_finEmb u.2, mul_one]
          rfl
        have hΞv : Ξ (archP K n a * finOne K n u) = kbar κ a * Θ (archP K n a) := by
          simp only [hΞdef, hF₀apply]
          rw [archimedeanProjection_mul_finiteEmbedding_comm, F0fun_finOne_mul U hU κ hu, F0fun_archP, ← archimedeanProjection_mul_finiteEmbedding_comm,
            hΘU u hu]
        have hmemS : infFinEquiv K n (a, (u : AdelicGLn.FiniteAdelicGL K n)) ∈ S ↔ detA K n a ∈ I := by
          rw [hSdef, mem_preimage, hd]
        show S.indicator (fun g => Ξ (retractOne g)) (infFinEquiv K n (a, (u : AdelicGLn.FiniteAdelicGL K n))) = _
        by_cases hI : detA K n a ∈ I
        · rw [indicator_of_mem (hmemS.2 hI), indicator_of_mem hI, hr, hΞv, one_mul]
        · rw [indicator_of_notMem (fun h => hI (hmemS.1 h)), indicator_of_notMem hI, zero_mul]
      · rw [indicator_of_notMem hh]
        simp only [hFpdef]
        by_cases hS' : infFinEquiv K n (a, h) ∈ S
        · rw [indicator_of_mem hS']
          have h0 : F₀ (retractOne (infFinEquiv K n (a, h))) = 0 := by
            rw [hF₀apply]
            unfold F0fun
            refine indicator_of_notMem ?_ _
            simp only [finUSet, mem_ofPred_eq, finPart_retract, infFinEquiv_apply, map_mul, finPart_infEmb,
              finPart_finEmb, one_mul]
            exact hh
          simp only [hΞdef, h0, zero_mul]
        · rw [indicator_of_notMem hS']
    simp_rw [hpt]
    rw [integral_indicator_const _ hU'm, measureReal_def]

  have step4 : ∫ a, I.indicator (fun _ => (1 : ℂ)) (detA K n a) * (kbar κ a * Θ (archP K n a)) ∂ν =
      ∫ a, κ a * Θ (archP K n a) ∂ν :=
    integral_indicator_kbar hn hκ hκc (hΘ.comp continuous_archP)
      (fun a s => by simp only [Function.comp_apply, archimedeanProjection_mul_positiveScalar hn]) ν
  calc ∫ x, F₀ x * Θ x ∂μ = ∫ x, Ξ x ∂μ := rfl
    _ = c₁.toReal • ∫ a, (μf U').toReal •
          (I.indicator (fun _ => (1 : ℂ)) (detA K n a) * (kbar κ a * Θ (archP K n a))) ∂ν := by
        rw [step1, step2]
        congr 1
        exact integral_congr_ae (Eventually.of_forall step3)
    _ = ((c₁.toReal * (μf U').toReal : ℝ) : ℂ) * ∫ a, κ a * Θ (archP K n a) ∂ν := by
        rw [integral_smul, step4, smul_smul, Complex.real_smul]

theorem exists_cc_integral_mul_eq_zero (μ : Measure (normOneGL K 0)) [μ.IsHaarMeasure]
    (ν : Measure (archGroup K 0)) [ν.IsHaarMeasure]
    (U : Subgroup (AdelicGLn.integralFiniteGL K 0)) (κ : archGroup K 0 → ℂ) :
    ∃ (F₀ : CompactlySupportedContinuousMap (normOneGL K 0) ℂ) (c : ℝ), 0 < c ∧
      (∀ u ∈ U, ∀ x, F₀ (finOne K 0 u * x) = F₀ x) ∧
      ∀ Θ : normOneGL K 0 → ℂ, Continuous Θ → (∀ u ∈ U, ∀ x, Θ (x * finOne K 0 u) = Θ x) →
        ∫ x, F₀ x * Θ x ∂μ = c * ∫ a, κ a * Θ (archP K 0 a) ∂ν := by
  have h1 : Subsingleton (AdelicGLn.AdelicGL K 0) := ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
  have h2 : Subsingleton (normOneGL K 0) := ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
  have h3 : Subsingleton (ArchMatrix K 0) :=
    inferInstanceAs (Subsingleton (Matrix (Fin 0) (Fin 0) (NumberField.mixedEmbedding.mixedSpace K)))
  have h4 : Subsingleton (archGroup K 0) :=
    ⟨fun x y => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
  let _ : Unique (normOneGL K 0) := uniqueOfSubsingleton 1
  let _ : Unique (archGroup K 0) := uniqueOfSubsingleton 1
  have : CompactSpace (normOneGL K 0) := Finite.compactSpace
  have hμ0 : μ univ ≠ 0 := isOpen_univ.measure_ne_zero μ univ_nonempty
  have hμt : μ univ ≠ ⊤ := isCompact_univ.measure_lt_top.ne
  have hμr : μ.real univ ≠ 0 := (ENNReal.toReal_pos hμ0 hμt).ne'
  set C : ℂ := ((ν.real univ / μ.real univ : ℝ) : ℂ) * κ default with hC
  refine ⟨⟨⟨fun _ => C, continuous_const⟩, ?_⟩, 1, one_pos, fun u _ x => rfl, fun Θ _ _ => ?_⟩
  · show IsCompact (tsupport _)
    exact isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)
  · rw [integral_unique, integral_unique]
    have ha : archP K 0 (default : archGroup K 0) = default := Subsingleton.elim _ _
    simp only [CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk, ha, Complex.real_smul,
      hC, Complex.ofReal_div, Complex.ofReal_one, one_mul]
    have hμc : (μ.real univ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hμr
    field_simp

theorem exists_cc_integral_mul_eq (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
    (U : Subgroup (AdelicGLn.integralFiniteGL K n)) (hU : IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)))
    (κ : archGroup K n → ℂ) (hκ : Continuous κ) (hκc : HasCompactSupport κ) :
    ∃ (F₀ : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (c : ℝ), 0 < c ∧
      (∀ u ∈ U, ∀ x, F₀ (finOne K n u * x) = F₀ x) ∧
      ∀ Θ : normOneGL K n → ℂ, Continuous Θ → (∀ u ∈ U, ∀ x, Θ (x * finOne K n u) = Θ x) →
        ∫ x, F₀ x * Θ x ∂μ = c * ∫ a, κ a * Θ (archP K n a) ∂ν := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact exists_cc_integral_mul_eq_zero μ ν U κ
  · exact exists_cc_integral_mul_eq_of_pos hn μ ν U hU κ hκ hκc

end CuspidalSpectrum

end

end GroundTheory.Automorphic
