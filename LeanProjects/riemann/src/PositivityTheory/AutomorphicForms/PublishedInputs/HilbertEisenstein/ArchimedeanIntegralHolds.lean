import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ArchInt
import GroundTheory.GlobalFields.TateThesis.EulerFactorsArch
import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Set Filter
open GroundTheory.Global GroundTheory.Global.IdeleGroup InfinitePlace InfinitePlace.Completion Formalism.L2.Host UpperTheory.V.Sd

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.LocalArchimedeanIntegral

theorem gauss_split {y M x : ℝ} (hx : x ≠ 0) :
    (x * y) ^ 2 + (M / x) ^ 2 = (x * y - M / x) ^ 2 + 2 * M * y := by
  field_simp
  ring

def phiP (y M : ℝ) (x : ℝ) : ℝ := x * y - M / x

theorem hasDerivAt_phiP (y M : ℝ) {x : ℝ} (hx : x ≠ 0) : HasDerivAt (phiP y M) (y + M / x ^ 2) x := by
  have h1 : HasDerivAt (fun x : ℝ => x * y) y x := by simpa using (hasDerivAt_id x).mul_const y
  have h2 : HasDerivAt (fun x : ℝ => M * x⁻¹) (M * -(x ^ 2)⁻¹) x := (hasDerivAt_inv hx).const_mul M
  have e1 : phiP y M = fun t => t * y - M * t⁻¹ := by
    funext t; simp only [phiP, div_eq_mul_inv]
  rw [e1]
  exact (h1.sub h2).congr_deriv (by rw [div_eq_mul_inv]; ring)

theorem phiP_strictMonoOn {y M : ℝ} (hy : 0 < y) (hM : 0 < M) : StrictMonoOn (phiP y M) (Ioi 0) := by
  intro a ha b hb hab
  simp only [mem_Ioi] at ha hb
  simp only [phiP]
  have h1 : a * y < b * y := mul_lt_mul_of_pos_right hab hy
  have h2 : M / b < M / a := div_lt_div_of_pos_left hM ha hab
  linarith

theorem phiP_image {y M : ℝ} (hy : 0 < y) (hM : 0 < M) : phiP y M '' Ioi 0 = univ := by
  refine eq_univ_of_forall fun u => ?_
  set s := Real.sqrt (u ^ 2 + 4 * M * y)
  have hs0 : 0 ≤ u ^ 2 + 4 * M * y := by positivity
  have hs2 : s ^ 2 = u ^ 2 + 4 * M * y := Real.sq_sqrt hs0
  have hsu : |u| < s := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
  have hpos : 0 < (u + s) / (2 * y) := by
    apply div_pos _ (by positivity)
    have := neg_abs_le u
    linarith
  refine ⟨(u + s) / (2 * y), hpos, ?_⟩
  simp only [phiP]
  have hne : (u + s) / (2 * y) ≠ 0 := hpos.ne'
  field_simp
  have hus : u + s ≠ 0 := by
    intro h
    have := neg_abs_le u
    linarith
  field_simp
  nlinarith [hs2]

theorem integral_plus {y M : ℝ} (hy : 0 < y) (hM : 0 < M) :
    ∫ x in Ioi (0 : ℝ), (y + M / x ^ 2) * Real.exp (-Real.pi * ((x * y) ^ 2 + (M / x) ^ 2)) =
      Real.exp (-2 * Real.pi * M * y) := by
  have h1 : ∀ x ∈ Ioi (0 : ℝ), (y + M / x ^ 2) * Real.exp (-Real.pi * ((x * y) ^ 2 + (M / x) ^ 2)) =
      Real.exp (-2 * Real.pi * M * y) * (|y + M / x ^ 2| • Real.exp (-Real.pi * (phiP y M x) ^ 2)) := by
    intro x hx
    have hx0 : x ≠ 0 := (mem_Ioi.1 hx).ne'
    rw [gauss_split hx0, abs_of_pos (by positivity), smul_eq_mul, phiP]
    rw [show -Real.pi * ((x * y - M / x) ^ 2 + 2 * M * y) = -2 * Real.pi * M * y + -Real.pi * (x * y - M / x) ^ 2 by ring,
      Real.exp_add]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_const_mul]
  have h2 := integral_image_eq_integral_abs_deriv_smul (f := phiP y M) (f' := fun x => y + M / x ^ 2)
    (s := Ioi 0) measurableSet_Ioi (fun x hx => (hasDerivAt_phiP y M (mem_Ioi.1 hx).ne').hasDerivWithinAt)
    (phiP_strictMonoOn hy hM).injOn (fun u => Real.exp (-Real.pi * u ^ 2))
  rw [← h2, phiP_image hy hM, Measure.restrict_univ, integral_gaussian, div_self Real.pi_ne_zero, Real.sqrt_one,
    mul_one]

theorem integrableOn_plus {y M : ℝ} (hy : 0 < y) (hM : 0 < M) :
    IntegrableOn (fun x : ℝ => (y + M / x ^ 2) * Real.exp (-Real.pi * ((x * y) ^ 2 + (M / x) ^ 2))) (Ioi 0) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_plus hy hM]
  exact (Real.exp_pos _).ne'

def psiP (y M : ℝ) (x : ℝ) : ℝ := M / y / x

theorem integral_minus {y M : ℝ} (hy : 0 < y) (hM : 0 < M) :
    ∫ x in Ioi (0 : ℝ), (y - M / x ^ 2) * Real.exp (-Real.pi * ((x * y) ^ 2 + (M / x) ^ 2)) = 0 := by
  set G : ℝ → ℝ := fun x => Real.exp (-Real.pi * ((x * y) ^ 2 + (M / x) ^ 2)) with hG
  have hP := integrableOn_plus hy hM
  have hGi : IntegrableOn G (Ioi 0) := by
    refine (hP.div_const y).mono' ?_ ?_
    · exact (by fun_prop : Measurable G).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
      have hx0 : 0 < x := hx
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [le_div_iff₀ hy]
      have : 0 ≤ M / x ^ 2 := by positivity
      nlinarith [Real.exp_pos (-Real.pi * ((x * y) ^ 2 + (M / x) ^ 2))]
  have hG2i : IntegrableOn (fun x => M / x ^ 2 * G x) (Ioi 0) := by
    refine hP.mono' ?_ ?_
    · exact (by fun_prop : Measurable fun x => M / x ^ 2 * G x).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
      have hx0 : 0 < x := hx
      have h0 : 0 ≤ M / x ^ 2 * G x := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      have := Real.exp_pos (-Real.pi * ((x * y) ^ 2 + (M / x) ^ 2))
      simp only [hG]
      nlinarith

  have hsub : ∫ x in Ioi (0 : ℝ), G x = ∫ x in Ioi (0 : ℝ), M / y / x ^ 2 * G x := by
    have hc : 0 < M / y := div_pos hM hy
    have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt (psiP y M) (-(M / y / x ^ 2)) (Ioi 0) x := by
      intro x hx
      have hx0 : x ≠ 0 := (mem_Ioi.1 hx).ne'
      have h2 : HasDerivAt (fun t : ℝ => M / y * t⁻¹) (M / y * -(x ^ 2)⁻¹) x := (hasDerivAt_inv hx0).const_mul (M / y)
      have e1 : psiP y M = fun t => M / y * t⁻¹ := by
        funext t; simp only [psiP, div_eq_mul_inv]
      rw [e1]
      exact (h2.congr_deriv (by rw [div_eq_mul_inv (M / y)]; ring)).hasDerivWithinAt
    have hinj : InjOn (psiP y M) (Ioi 0) := by
      intro a ha b hb hab
      have h1 : M / y / a = M / y / b := hab
      have ha0 : a ≠ 0 := (mem_Ioi.1 ha).ne'
      have hb0 : b ≠ 0 := (mem_Ioi.1 hb).ne'
      rw [div_eq_div_iff ha0 hb0] at h1
      exact (mul_left_cancel₀ hc.ne' h1).symm
    have him : psiP y M '' Ioi 0 = Ioi 0 := by
      ext u
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact div_pos hc hx
      · intro hu
        refine ⟨M / y / u, div_pos hc hu, ?_⟩
        simp only [psiP]
        field_simp
    have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj G
    rw [him] at h
    rw [h]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := hx
    rw [abs_neg, abs_of_pos (by positivity), smul_eq_mul]
    congr 1
    simp only [hG, psiP]
    congr 2
    field_simp
    ring
  have hsplit : (fun x : ℝ => (y - M / x ^ 2) * G x) = fun x => y * G x - M / x ^ 2 * G x := by
    funext x; ring
  rw [hsplit, integral_sub (hGi.const_mul y) hG2i, integral_const_mul, hsub]
  have : ∫ x in Ioi (0 : ℝ), M / y / x ^ 2 * G x = y⁻¹ * ∫ x in Ioi (0 : ℝ), M / x ^ 2 * G x := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    field_simp
  rw [this, ← mul_assoc, mul_inv_cancel₀ hy.ne', one_mul, sub_self]

def kR (y ξ : ℝ) (x : ℝ) : ℝ := (y + ξ / x ^ 2) * Real.exp (-Real.pi * ((x * y) ^ 2 + (ξ / x) ^ 2))

theorem kR_abs (y ξ x : ℝ) : kR y ξ |x| = kR y ξ x := by
  simp only [kR, sq_abs, div_pow, mul_pow]

theorem integrableOn_abs_Iic {f : ℝ → ℝ} (hf : IntegrableOn (fun x => f |x|) (Ioi 0)) :
    IntegrableOn (fun x => f |x|) (Iic 0) := by
  rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
  let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
  rw [m.integrableOn_map_iff]
  simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact hf

theorem integrable_of_abs {f : ℝ → ℝ} (hf : IntegrableOn (fun x => f |x|) (Ioi 0)) :
    Integrable (fun x => f |x|) := by
  have h := (integrableOn_abs_Iic hf).union hf
  rwa [Iic_union_Ioi, integrableOn_univ] at h

theorem integrable_kR {y ξ : ℝ} (hy : 0 < y) (hξ : ξ ≠ 0) : Integrable (kR y ξ) := by
  have hM : 0 < |ξ| := abs_pos.2 hξ
  have hdom : IntegrableOn (fun x => kR y |ξ| |x|) (Ioi 0) := by
    refine (integrableOn_plus hy hM).congr_fun (fun x hx => ?_) measurableSet_Ioi
    have hx0 : 0 < x := hx
    simp only [kR, abs_of_pos hx0]
  have hi := integrable_of_abs hdom
  refine hi.mono' (by unfold kR; fun_prop : Measurable (kR y ξ)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [kR_abs]
  simp only [kR, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : (ξ / x) ^ 2 = (|ξ| / x) ^ 2 := by rw [div_pow, div_pow, sq_abs]
  rw [h1]
  gcongr
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_pos hy, abs_div, abs_of_nonneg (sq_nonneg x)]

theorem integral_kR {y ξ : ℝ} (hy : 0 < y) (hξ : ξ ≠ 0) :
    ∫ x, kR y ξ x = if 0 < ξ then 2 * Real.exp (-2 * Real.pi * ξ * y) else 0 := by
  have h : ∫ x, kR y ξ x = 2 * ∫ x in Ioi (0 : ℝ), kR y ξ x := by
    rw [← integral_comp_abs]
    simp only [kR_abs]
  rw [h]
  split_ifs with hpos
  · rw [show (∫ x in Ioi (0 : ℝ), kR y ξ x) = Real.exp (-2 * Real.pi * ξ * y) from integral_plus hy hpos]
  · have hneg : 0 < -ξ := by
      rcases lt_or_gt_of_ne hξ with h' | h'
      · linarith
      · exact absurd h' hpos
    have := integral_minus hy hneg
    have e : ∀ x, kR y ξ x = (y - -ξ / x ^ 2) * Real.exp (-Real.pi * ((x * y) ^ 2 + (-ξ / x) ^ 2)) := by
      intro x
      simp only [kR, neg_div, sub_neg_eq_add, neg_sq]
    simp only [e]
    rw [this, mul_zero]

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem locInf_eq (ω : HChar F) (v : InfinitePlace F) (z : (v.Completion)ˣ) :
    ω.1 (infiniteEmbedding v z) = ω.locInf v z := rfl

theorem omega_ofInfinite (ω : HChar F) (a : (InfiniteAdeleRing F)ˣ) :
    ((ω.1 (ofInfinite a) : ℂˣ) : ℂ) = ∏ v, ((ω.locInf v (infiniteComponent v a) : ℂˣ) : ℂ) := by
  rw [ofInfinite_eq_prod, map_prod, Units.coe_prod]
  rfl

theorem locInf_pow_eq_one {ω : HChar F} (hfin : IsOfFinOrder ω) :
    ∃ N : ℕ, 0 < N ∧ ∀ v (z : (v.Completion)ˣ), ω.locInf v z ^ N = 1 := by
  obtain ⟨N, hN, hpow⟩ := (isOfFinOrder_iff_pow_eq_one).1 hfin
  refine ⟨N, hN, fun v z => ?_⟩
  have h1 : (ω ^ N).1 = 1 := by rw [hpow]; rfl
  rw [HChar.locInf, MonoidHom.comp_apply, ← MonoidHom.pow_apply, ← Subgroup.coe_pow, h1, MonoidHom.one_apply]

def rv (v : InfinitePlace F) (z : v.Completion) : ℝ := ringEquivRealOfIsReal (IsTotallyReal.isReal v) z

theorem locInf_sign {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp ω c) (v : InfinitePlace F)
    (z : (v.Completion)ˣ) : ((ω.locInf v z : ℂˣ) : ℂ) = if 0 < rv v (z : v.Completion) then 1 else -1 := by
  obtain ⟨N, hN, hpow⟩ := locInf_pow_eq_one H.fin
  set e := ringEquivRealOfIsReal (IsTotallyReal.isReal v)
  have hpos : ∀ z' : (v.Completion)ˣ, 0 < e z' → ω.locInf v z' = 1 := by
    intro z' hz'
    set r := e z'
    have hb : (r ^ ((N : ℝ)⁻¹)) ≠ 0 := (Real.rpow_pos_of_pos hz' _).ne'
    set b : (v.Completion)ˣ := Units.mk0 (e.symm (r ^ ((N : ℝ)⁻¹))) (by
      rw [Ne, map_eq_zero_iff _ e.symm.injective]; exact hb)
    have hbN : b ^ N = z' := by
      apply Units.ext
      apply e.injective
      rw [Units.val_pow_eq_pow_val, map_pow]
      change (e (e.symm (r ^ ((N : ℝ)⁻¹)))) ^ N = r
      rw [RingEquiv.apply_symm_apply, ← Real.rpow_natCast, ← Real.rpow_mul hz'.le,
        inv_mul_cancel₀ (by exact_mod_cast hN.ne'), Real.rpow_one]
    rw [← hbN, map_pow, hpow]
  have hodd := H.odd v
  split_ifs with h
  · rw [hpos z h, Units.val_one]
  · have h' : e z ≠ 0 := by
      intro h0
      exact z.ne_zero (e.injective (by rw [h0, map_zero]))
    have hneg : e z < 0 := lt_of_le_of_ne (not_lt.1 h) h'
    have hz : z = -1 * (-z) := by rw [neg_mul, one_mul, neg_neg]
    have hz' : 0 < e ((-z : (v.Completion)ˣ) : v.Completion) := by
      rw [Units.val_neg, map_neg]; linarith
    rw [hz, map_mul, hodd, hpos _ hz', mul_one, Units.val_neg, Units.val_one]

omit [NumberField F] in
theorem integrable_units_iff {v : InfinitePlace F} (G : v.Completion → ℂ) :
    Integrable (fun a : (v.Completion)ˣ => G a) (infinitePlaceUnitsMeasure v) ↔
      Integrable (fun x : ℝ => G ((isometryEquivRealOfIsReal (IsTotallyReal.isReal v)).symm x) / ((|x| : ℝ) : ℂ)) := by
  have hv := IsTotallyReal.isReal v
  have he := measurableEmbedding_units_val (F := v.Completion)
  set ν := (infinitePlaceMeasure v).withDensity fun x => ENNReal.ofReal (‖x‖ ^ v.mult)⁻¹ with hν
  have hr : Set.range (Units.val : (v.Completion)ˣ → v.Completion) = {0}ᶜ := by
    ext x
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ⟨fun ⟨u, hu⟩ ↦ hu ▸ u.ne_zero, fun hx ↦ ⟨Units.mk0 x hx, rfl⟩⟩
  have hac : ν ≪ infinitePlaceMeasure v := withDensity_absolutelyContinuous _ _
  have h0 := he.integrable_map_iff (g := G) (μ := Measure.comap Units.val ν)
  rw [he.map_comap, hr, Measure.restrict_eq_self_of_ae_mem (s := ({0} : Set v.Completion)ᶜ)
    (compl_mem_ae_iff.2 (hac (infinitePlaceMeasure_zero v)))] at h0
  have h1 : Integrable (fun a : (v.Completion)ˣ => G a) (infinitePlaceUnitsMeasure v) ↔ Integrable G ν := by
    show Integrable (G ∘ Units.val) (Measure.comap Units.val ν) ↔ _
    exact h0.symm
  have hme : MeasurableEmbedding (isometryEquivRealOfIsReal hv).symm :=
    (isometryEquivRealOfIsReal hv).symm.toHomeomorph.measurableEmbedding
  rw [h1, hν, integrable_withDensity_iff_integrable_smul' (measurable_density_unitsMeasure v.mult)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), infinitePlaceMeasure_of_isReal hv,
    hme.integrable_map_iff]
  refine integrable_congr (Eventually.of_forall fun x => ?_)
  have hn : ‖(isometryEquivRealOfIsReal hv).symm x‖ = |x| := by
    rw [← Real.norm_eq_abs, ← (isometryEquivRealOfIsReal hv).symm.isometry.norm_map_of_map_zero]
    change (ringEquivRealOfIsReal hv).symm 0 = 0
    exact map_zero _
  simp only [Function.comp_apply, hv.mult_eq_one, pow_one, hn,
    ENNReal.toReal_ofReal (inv_nonneg.2 (abs_nonneg x)), Complex.real_smul]
  push_cast
  rw [div_eq_inv_mul]

def gv (ω : HChar F) (y : (UpperTheory.V.TR.Rinf F)ˣ) (ξ : F) (v : InfinitePlace F) (u : (v.Completion)ˣ) : ℂ :=
  ((((rv v u * y.val v + (rv v u)⁻¹ * reAt v ξ : ℝ)) : ℂ) *
    Complex.exp (-(Real.pi : ℂ) * (((rv v u * y.val v) ^ 2 + ((rv v u)⁻¹ * reAt v ξ) ^ 2 : ℝ) : ℂ))) *
      ((ω.locInf v u : ℂˣ) : ℂ)⁻¹

theorem reAt_ne_zero (v : InfinitePlace F) {ξ : F} (hξ : ξ ≠ 0) : reAt v ξ ≠ 0 := by
  have hv := IsTotallyReal.isReal v
  have h := NumberField.InfinitePlace.embedding_of_isReal_apply hv ξ
  have h2 : reAt v ξ = NumberField.InfinitePlace.embedding_of_isReal hv ξ := by
    rw [reAt, ← h, Complex.ofReal_re]
  rw [h2]
  exact (map_ne_zero _).2 hξ

theorem local_int {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (H : Hyp ω c) (y : (UpperTheory.V.TR.Rinf F)ˣ)
    (hy : ∀ v, 0 < y.val v) (ξ : Fˣ) (v : InfinitePlace F) :
    Integrable (gv ω y (ξ : F) v) (infinitePlaceUnitsMeasure v) ∧
      ∫ u, gv ω y (ξ : F) v u ∂infinitePlaceUnitsMeasure v =
        if 0 < reAt v (ξ : F) then 2 * Complex.exp (-(2 * Real.pi : ℂ) * ((reAt v (ξ : F) : ℂ) * (y.val v : ℂ))) else 0 := by
  have hv := IsTotallyReal.isReal v
  have hξ0 : reAt v (ξ : F) ≠ 0 := reAt_ne_zero v ξ.ne_zero
  set yv := y.val v with hyv
  set m := reAt v (ξ : F) with hm
  set G : v.Completion → ℂ := fun z => (((rv v z * yv + (rv v z)⁻¹ * m : ℝ) : ℂ) *
      ((Real.exp (-Real.pi * ((rv v z * yv) ^ 2 + ((rv v z)⁻¹ * m) ^ 2)) : ℝ) : ℂ)) *
      (if 0 < rv v z then (1 : ℂ) else -1)⁻¹ with hGdef
  have hgv : gv ω y (ξ : F) v = fun u : (v.Completion)ˣ => G (u : v.Completion) := by
    funext u
    simp only [gv, hGdef, locInf_sign H v u, Complex.ofReal_exp]
    congr 3
    push_cast
    ring
  have hae : (fun x : ℝ => G ((isometryEquivRealOfIsReal hv).symm x) / ((|x| : ℝ) : ℂ)) =ᵐ[volume]
      fun x => ((kR yv m x : ℝ) : ℂ) := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with x hx
    have hx0 : x ≠ 0 := hx
    have hr : rv v ((isometryEquivRealOfIsReal hv).symm x) = x := (ringEquivRealOfIsReal hv).apply_symm_apply x
    simp only [hGdef, hr, kR, inv_mul_eq_div]
    have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
    rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · rw [if_neg (not_lt.2 hneg.le), abs_of_neg hneg]
      push_cast
      field_simp
    · rw [if_pos hpos, abs_of_pos hpos]
      push_cast
      field_simp
  refine ⟨?_, ?_⟩
  · rw [hgv, integrable_units_iff G]
    exact (integrable_kR (hy v) hξ0).ofReal.congr hae.symm
  · rw [hgv, integral_infinitePlaceUnitsMeasure_of_isReal hv G, integral_congr_ae hae, integral_complex_ofReal,
      integral_kR (hy v) hξ0]
    split_ifs
    · push_cast
      congr 2
      ring
    · simp

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.LocalArchimedeanIntegral

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open LocalArchimedeanIntegral L4

theorem archimedean_integral_holds : ArchInt := by
  intro F _ _ _ ω c H y hy ξ
  have he : MeasurableEmbedding (infiniteUnitsEquiv F).symm :=
    (infiniteUnitsEquiv F).symm.toHomeomorph.measurableEmbedding
  have hpt : ∀ z : (Π v : InfinitePlace F, (v.Completion)ˣ),
      archK y (ξ : F) ((infiniteUnitsEquiv F).symm z) * (ωI ω ((infiniteUnitsEquiv F).symm z))⁻¹ =
        ∏ v, gv ω y (ξ : F) v (z v) := by
    intro z
    rw [archK, ωI, omega_ofInfinite, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    rfl
  have hloc := fun v => local_int H y hy ξ v
  constructor
  · rw [infiniteIdeleMeasure, he.integrable_map_iff]
    refine (Integrable.fintype_prod_dep (fun v => (hloc v).1)).congr ?_
    exact Eventually.of_forall fun z => (hpt z).symm
  · rw [infiniteIdeleMeasure, he.integral_map]
    simp only [Function.comp_apply, hpt]
    rw [integral_fintype_prod_eq_prod]
    simp only [fun v => (hloc v).2]
    rw [Finset.prod_ite_zero]
    simp only [Finset.mem_univ, true_implies]
    split_ifs
    · rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Complex.exp_sum, Finset.mul_sum]
    · rfl

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
