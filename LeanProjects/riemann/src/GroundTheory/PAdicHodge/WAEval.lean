import Mathlib
import GroundTheory.PAdicHodge.WACommon
import GroundTheory.PAdicHodge.ExtRobbaPointDiv
import GroundTheory.PAdicHodge.ExtRobbaRoot
import GroundTheory.PAdicHodge.BStPeriod
import GroundTheory.PAdicHodge.ACrisBdR
import GroundTheory.PAdicHodge.BdRGalois
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace WAEval

open _root_.WittVector WittTilt PhiGamma TeichLift UniformSpace IsPerfectoidField Laurent

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔍" => RingHom.ker (fontaineThetaInvertP (normInteger ℂ_[p]) p)
local notation "θ" => fontaineTheta (normInteger ℂ_[p]) p

theorem norm_natCast_p : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends,
    ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends, Padic.norm_p]

theorem inv_p_pos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 hp.out.pos)

theorem inv_p_lt_one : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 hp.out.one_lt)

variable (p) in

def varpi : Cb p := algebraMap (Ob p) (Cb p) (pFlat p)

theorem norm_varpi : ‖varpi p‖ = (p : ℝ)⁻¹ := by
  rw [varpi, norm_algebraMap_preTilt, preTilt_norm_def, untilt_pFlat]
  push_cast
  exact norm_natCast_p

theorem varpi_ne_zero : varpi p ≠ 0 := by
  intro h
  have := norm_varpi (p := p)
  rw [h, norm_zero] at this
  exact inv_p_pos.ne this

theorem norm_varpi_lt_one : ‖varpi p‖ < 1 := by
  rw [norm_varpi]; exact inv_p_lt_one

variable (p) in

def xi : (𝓣).int := (𝓣).ptElt (norm_varpi_lt_one (p := p)).le

theorem isPrimOne_xi : (𝓣).IsPrimOne (xi p) := (𝓣).isPrimOne_ptElt varpi_ne_zero norm_varpi_lt_one

theorem ptRad_xi : (𝓣).ptRad (xi p) = (p : ℝ)⁻¹ := by
  rw [ptRad, coeff_zero, xi, coe_ptElt, map_sub, red_π, red_teich, zero_sub, norm_neg, norm_varpi]

variable (p) in

def xiA : AInf ℂ_[p] p := (p : AInf ℂ_[p] p) - teichmuller p (pFlat p)

theorem ker_theta_eq_span_xiA : RingHom.ker θ = Ideal.span {xiA p} :=
  IsPerfectoidField.ker_fontaineTheta_eq_span_p_sub_teichmuller untilt_pFlat

theorem incl_xiA : incl ℂ_[p] p (xiA p) = ((xi p : (𝓣).int) : WC p) := by
  rw [xiA, map_sub, map_natCast, incl_teichmuller, xi, coe_ptElt, teich_eq, teichLift_π]
  rfl

theorem ker_eq_span_xiA : 𝔍 = Ideal.span {algebraMap (AInf ℂ_[p] p) 𝔸 (xiA p)} :=
  ker_fontaineThetaInvertP ker_theta_eq_span_xiA

theorem ker_pow_eq_span (m : ℕ) : 𝔍 ^ m = Ideal.span {algebraMap (AInf ℂ_[p] p) 𝔸 (xiA p) ^ m} := by
  rw [ker_eq_span_xiA, Ideal.span_singleton_pow]

theorem convAll_pow {b : (𝓣).B} (hb : (𝓣).ConvAll b) (k : ℕ) : (𝓣).ConvAll (b ^ k) := by
  induction k with
  | zero => rw [pow_zero]; simpa using (TeichLift.convAll_π_pow (T := 𝓣) 0)
  | succ k ih => rw [pow_succ]; exact ih.mul hb

theorem toB_eq_mul (a : 𝔸) : ∃ (N : ℕ) (y : AInf ℂ_[p] p), toB ℂ_[p] p a =
    algebraMap (WC p) (𝓣).B (incl ℂ_[p] p y) * IsLocalization.Away.invSelf (𝓣).π ^ N := by
  obtain ⟨N, y, hy⟩ := IsLocalization.Away.surj (p : AInf ℂ_[p] p) a
  refine ⟨N, y, ?_⟩
  have h := congrArg (toB ℂ_[p] p) hy
  rw [map_mul, map_pow, toB_algebraMap, toB_algebraMap] at h
  have e : algebraMap (WC p) (𝓣).B (incl ℂ_[p] p (p : AInf ℂ_[p] p)) =
      algebraMap (WC p) (𝓣).B (𝓣).π := by
    rw [map_natCast (incl ℂ_[p] p)]; rfl
  rw [← h, mul_assoc, ← mul_pow, e, IsLocalization.Away.mul_invSelf, one_pow, mul_one]

theorem convAll_toB (a : 𝔸) : (𝓣).ConvAll (toB ℂ_[p] p a) := by
  obtain ⟨N, y, hy⟩ := toB_eq_mul a
  rw [hy]
  exact (convAll_algebraMap_of_mem_int (incl_mem_int y)).mul (convAll_pow convAll_invSelf N)

variable (p) in

def awayToEcon (ρ : Set.Ioo (0 : ℝ) 1) : 𝔸 →+* (𝓣).Econ ρ :=
  (toB ℂ_[p] p).codRestrict ((𝓣).Econ ρ) fun a => convAll_toB a ρ ρ.2.1 ρ.2.2

variable (p) in

def awayToExt (ρ : Set.Ioo (0 : ℝ) 1) : 𝔸 →+* (𝓣).RobbaExt ρ :=
  Completion.coeRingHom.comp (awayToEcon p ρ)

theorem awayToExt_apply (ρ : Set.Ioo (0 : ℝ) 1) (a : 𝔸) :
    awayToExt p ρ a = ((⟨toB ℂ_[p] p a, convAll_toB a ρ ρ.2.1 ρ.2.2⟩ : (𝓣).Econ ρ) :
      (𝓣).RobbaExt ρ) := rfl

theorem awayToExt_eq_ofAll (ρ : Set.Ioo (0 : ℝ) 1) (a : 𝔸) :
    awayToExt p ρ a = (𝓣).ofAll (toB ℂ_[p] p a) (convAll_toB a) ρ := rfl

theorem awayToExt_injective (ρ : Set.Ioo (0 : ℝ) 1) : Function.Injective (awayToExt p ρ) :=
  fun _ _ h => toB_injective (congrArg Subtype.val ((𝓣).coe_injective_Econ h))

theorem res_awayToExt {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} (h : (ρ1 : ℝ) ≤ ρ0) (a : 𝔸) :
    (𝓣).res h (awayToExt p ρ0 a) = awayToExt p ρ1 a := by
  rw [awayToExt_apply, res_coe]
  rfl

theorem awayToExt_xiA (ρ : Set.Ioo (0 : ℝ) 1) :
    awayToExt p ρ (algebraMap (AInf ℂ_[p] p) 𝔸 (xiA p)) = (𝓣).ξExt (xi p) ρ := by
  rw [awayToExt_apply, ξExt]
  congr 2
  rw [toB_algebraMap, incl_xiA]

theorem res_ξExt {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} (h : (ρ1 : ℝ) ≤ ρ0) :
    (𝓣).res h ((𝓣).ξExt (xi p) ρ0) = (𝓣).ξExt (xi p) ρ1 := by
  rw [← awayToExt_xiA, ← awayToExt_xiA, res_awayToExt]

theorem ξExt_ne_zero (ρ : Set.Ioo (0 : ℝ) 1) : (𝓣).ξExt (xi p) ρ ≠ 0 := by
  intro h
  have h1 := (𝓣).ptRad_le_extNorm_ξExt (ξ := xi p) (topRad ρ)
  rw [h, extNorm_zero, ptRad_xi] at h1
  exact absurd h1 (not_le.2 inv_p_pos)

theorem toUntiltField_injective : Function.Injective ((𝓣).toUntiltField (isPrimOne_xi (p := p))) :=
  fun _ _ h => (𝓣).algebraMap_untiltFrac_injective isPrimOne_xi
    ((WithAbs.equiv ((𝓣).untiltAbs isPrimOne_xi)).symm.injective h)

variable (p) in

def thetaXi : 𝔸 →+* (𝓣).UntiltField (isPrimOne_xi (p := p)) :=
  ((𝓣).ptEvalEcon isPrimOne_xi).comp (awayToEcon p ((𝓣).ptRadIoo isPrimOne_xi))

theorem thetaXi_apply (a : 𝔸) : thetaXi p a = (𝓣).ptEvalB isPrimOne_xi (toB ℂ_[p] p a) := rfl

theorem ptEval_awayToExt {ρ : Set.Ioo (0 : ℝ) 1} (hr : (𝓣).ptRad (xi p) ≤ ρ) (a : 𝔸) :
    (𝓣).ptEval isPrimOne_xi hr (awayToExt p ρ a) = thetaXi p a := by
  rw [awayToExt_apply, ptEval_coe]
  rfl

theorem thetaXi_algebraMap (y : AInf ℂ_[p] p) :
    thetaXi p (algebraMap _ 𝔸 y) = (𝓣).toUntiltField isPrimOne_xi
      ((𝓣).toUntilt (xi p) ⟨incl ℂ_[p] p y, incl_mem_int y⟩) := by
  rw [thetaXi_apply, toB_algebraMap, ptEvalB_algebraMap, ptE_int]

theorem thetaXi_algebraMap_p :
    thetaXi p (algebraMap _ 𝔸 (p : AInf ℂ_[p] p)) = (𝓣).ptPi isPrimOne_xi := by
  rw [thetaXi_algebraMap, ptPi]
  congr 2
  exact Subtype.ext (map_natCast (incl ℂ_[p] p) p)

theorem thetaXi_algebraMap_eq_zero_iff (y : AInf ℂ_[p] p) :
    thetaXi p (algebraMap _ 𝔸 y) = 0 ↔ y ∈ Ideal.span {xiA p} := by
  rw [thetaXi_algebraMap, map_eq_zero_iff _ toUntiltField_injective, toUntilt_eq_zero_iff,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨B, ⟨c, rfl⟩, hB⟩
    refine ⟨c, incl_injective ?_⟩
    rw [map_mul, incl_xiA, mul_comm]
    exact hB.symm
  · rintro ⟨c, rfl⟩
    refine ⟨incl ℂ_[p] p c, ⟨c, rfl⟩, ?_⟩
    show incl ℂ_[p] p (c * xiA p) = _
    rw [map_mul, incl_xiA, mul_comm]

theorem natCast_p_normInteger_ne_zero : ((p : normInteger ℂ_[p]) : normInteger ℂ_[p]) ≠ 0 := by
  intro h
  have h' := congrArg (fun x : normInteger ℂ_[p] => ‖(x : ℂ_[p])‖) h
  simp only [ZeroMemClass.coe_zero, norm_zero] at h'
  push_cast at h'
  rw [norm_natCast_p] at h'
  exact inv_p_pos.ne' h'

theorem fontaineThetaInvertP_algebraMap_eq_zero_iff (y : AInf ℂ_[p] p) :
    fontaineThetaInvertP (normInteger ℂ_[p]) p (algebraMap _ 𝔸 y) = 0 ↔ θ y = 0 := by
  rw [fontaineThetaInvertP_algebraMap]
  exact map_eq_zero_iff _ (IsLocalization.injective (M := Submonoid.powers (p : normInteger ℂ_[p]))
      (Localization.Away (p : normInteger ℂ_[p]))
      (powers_le_nonZeroDivisors_of_noZeroDivisors natCast_p_normInteger_ne_zero))

theorem thetaXi_eq_zero_iff (a : 𝔸) : thetaXi p a = 0 ↔ a ∈ 𝔍 := by
  obtain ⟨N, y, hy⟩ := IsLocalization.Away.surj (p : AInf ℂ_[p] p) a
  rw [RingHom.mem_ker]
  have hP : thetaXi p (algebraMap _ 𝔸 (p : AInf ℂ_[p] p)) ≠ 0 := by
    rw [thetaXi_algebraMap_p]; exact (𝓣).ptPi_ne_zero isPrimOne_xi
  have h1 : thetaXi p a = 0 ↔ thetaXi p (algebraMap _ 𝔸 y) = 0 := by
    rw [← hy, map_mul, map_pow, mul_eq_zero, or_iff_left (pow_ne_zero N hP)]
  have hU : IsUnit (fontaineThetaInvertP (normInteger ℂ_[p]) p (algebraMap _ 𝔸 (p : AInf ℂ_[p] p))) := by
    rw [fontaineThetaInvertP_algebraMap, map_natCast, ← map_natCast (algebraMap (normInteger ℂ_[p]) _)]
    exact IsLocalization.Away.algebraMap_isUnit _
  have h2 : fontaineThetaInvertP (normInteger ℂ_[p]) p a = 0 ↔
      fontaineThetaInvertP (normInteger ℂ_[p]) p (algebraMap _ 𝔸 y) = 0 := by
    rw [← hy, map_mul, map_pow, (hU.pow N).mul_left_eq_zero]
  rw [h1, h2, thetaXi_algebraMap_eq_zero_iff, fontaineThetaInvertP_algebraMap_eq_zero_iff,
    ← RingHom.mem_ker, ker_theta_eq_span_xiA]

theorem ker_thetaXi : RingHom.ker (thetaXi p) = 𝔍 :=
  Ideal.ext fun a => (RingHom.mem_ker).trans (thetaXi_eq_zero_iff a)

theorem thetaXi_surjective : Function.Surjective (thetaXi p) := by
  intro w
  set π' := (𝓣).ptPi (isPrimOne_xi (p := p)) with hπ'
  have hπn : ‖π'‖ = (p : ℝ)⁻¹ := by rw [hπ', norm_ptPi]; exact ptRad_xi
  have hπ0 : π' ≠ 0 := (𝓣).ptPi_ne_zero isPrimOne_xi
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (‖w‖ + 1)⁻¹ by positivity)
    (inv_p_lt_one (p := p))
  have hle : ‖w * π' ^ k‖ ≤ 1 := by
    rw [norm_mul, norm_pow, hπn]
    have h1 : ‖w‖ * (p : ℝ)⁻¹ ^ k ≤ ‖w‖ * (‖w‖ + 1)⁻¹ :=
      mul_le_mul_of_nonneg_left hk.le (norm_nonneg w)
    have h2 : ‖w‖ * (‖w‖ + 1)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by positivity)]; linarith
    linarith
  obtain ⟨q, hq⟩ := (𝓣).exists_toUntiltField_eq isPrimOne_xi hle
  obtain ⟨Y, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨y, hy⟩ := Y.2
  have hY : Y = ⟨incl ℂ_[p] p y, incl_mem_int y⟩ := Subtype.ext hy.symm
  refine ⟨algebraMap _ 𝔸 y * IsLocalization.Away.invSelf (p : AInf ℂ_[p] p) ^ k, ?_⟩
  have h1 : thetaXi p (algebraMap _ 𝔸 y) = w * π' ^ k := by
    rw [thetaXi_algebraMap, ← hY]; exact hq
  have h2 : thetaXi p (IsLocalization.Away.invSelf (p : AInf ℂ_[p] p)) = π'⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [hπ', ← thetaXi_algebraMap_p, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  rw [map_mul, map_pow, h1, h2, mul_assoc, ← mul_pow, mul_inv_cancel₀ hπ0, one_pow, mul_one]

variable {ρ : Set.Ioo (0 : ℝ) 1}

theorem ptRad_xi_le (hρ : (p : ℝ)⁻¹ < ρ) : (𝓣).ptRad (xi p) ≤ ρ := by
  rw [ptRad_xi]; exact hρ.le

theorem ptRad_xi_lt (hρ : (p : ℝ)⁻¹ < ρ) : (𝓣).ptRad (xi p) < ρ := by
  rw [ptRad_xi]; exact hρ

theorem exists_sub_awayToExt_mem_span (hρ : (p : ℝ)⁻¹ < ρ) (x : (𝓣).RobbaExt ρ) :
    ∃ a : 𝔸, x - awayToExt p ρ a ∈ Ideal.span {(𝓣).ξExt (xi p) ρ} := by
  obtain ⟨a, ha⟩ := thetaXi_surjective ((𝓣).ptEval isPrimOne_xi (ptRad_xi_le hρ) x)
  refine ⟨a, Ideal.mem_span_singleton'.2 ?_⟩
  obtain ⟨y, hy⟩ := ((𝓣).ptEval_eq_zero_iff isPrimOne_xi (ptRad_xi_le hρ)
    (x - awayToExt p ρ a)).1 (by rw [map_sub, ptEval_awayToExt, ha, sub_self])
  exact ⟨y, by rw [hy, mul_comm]⟩

theorem awayToExt_mem_span_iff (hρ : (p : ℝ)⁻¹ < ρ) (a : 𝔸) :
    awayToExt p ρ a ∈ Ideal.span {(𝓣).ξExt (xi p) ρ} ↔ a ∈ 𝔍 := by
  rw [← thetaXi_eq_zero_iff, ← ptEval_awayToExt (ptRad_xi_le hρ),
    (𝓣).ptEval_eq_zero_iff isPrimOne_xi (ptRad_xi_le hρ), Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, by rw [← hy, mul_comm]⟩
  · rintro ⟨y, hy⟩; exact ⟨y, by rw [hy, mul_comm]⟩

theorem awayToExt_mem_pow_iff (hρ : (p : ℝ)⁻¹ < ρ) (m : ℕ) (a : 𝔸) :
    awayToExt p ρ a ∈ Ideal.span {(𝓣).ξExt (xi p) ρ} ^ m ↔ a ∈ 𝔍 ^ m := by
  set ξ := (𝓣).ξExt (xi p) ρ with hξdef
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    rw [Ideal.span_singleton_pow, ker_pow_eq_span, Ideal.mem_span_singleton',
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, hy⟩
      have hm : awayToExt p ρ a ∈ Ideal.span {ξ} ^ m := by
        rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
        exact ⟨y * ξ, by rw [← hy, pow_succ]; ring⟩
      have hm' := (ih a).1 hm
      rw [ker_pow_eq_span, Ideal.mem_span_singleton'] at hm'
      obtain ⟨c, rfl⟩ := hm'
      have h2 : awayToExt p ρ c = y * ξ := by
        rw [map_mul, map_pow, awayToExt_xiA, pow_succ] at hy
        apply mul_right_cancel₀ (pow_ne_zero m (ξExt_ne_zero ρ))
        rw [← hy]; ring
      have h3 : c ∈ 𝔍 := (awayToExt_mem_span_iff hρ c).1 (Ideal.mem_span_singleton'.2 ⟨y, h2.symm⟩)
      rw [ker_eq_span_xiA, Ideal.mem_span_singleton'] at h3
      obtain ⟨d, rfl⟩ := h3
      exact ⟨d, by ring⟩
    · rintro ⟨c, rfl⟩
      exact ⟨awayToExt p ρ c, by rw [map_mul, map_pow, awayToExt_xiA]⟩

theorem exists_sub_awayToExt_mem_pow (hρ : (p : ℝ)⁻¹ < ρ) (m : ℕ) (x : (𝓣).RobbaExt ρ) :
    ∃ a : 𝔸, x - awayToExt p ρ a ∈ Ideal.span {(𝓣).ξExt (xi p) ρ} ^ m := by
  set ξ := (𝓣).ξExt (xi p) ρ with hξdef
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
    obtain ⟨a, ha⟩ := ih
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨y, hy⟩ := ha
    obtain ⟨b, hb⟩ := exists_sub_awayToExt_mem_span hρ y
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hb
    refine ⟨a + b * algebraMap _ 𝔸 (xiA p) ^ m, ?_⟩
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    refine ⟨z, ?_⟩
    rw [map_add, map_mul, map_pow, awayToExt_xiA, pow_succ]
    linear_combination ξ ^ m * hz + hy

theorem exists_awayToExt_sub_mem_pow (hρ : (p : ℝ)⁻¹ < ρ) (m : ℕ) (x : (𝓣).RobbaExt ρ) :
    ∃ a : 𝔸, awayToExt p ρ a - x ∈ Ideal.span {(𝓣).ξExt (xi p) ρ} ^ m := by
  obtain ⟨a, ha⟩ := exists_sub_awayToExt_mem_pow hρ m x
  refine ⟨a, ?_⟩
  set ξ := (𝓣).ξExt (xi p) ρ with hξdef
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha ⊢
  obtain ⟨y, hy⟩ := ha
  exact ⟨-y, by linear_combination -hy⟩

theorem ker_pow_le_comap (ρ : Set.Ioo (0 : ℝ) 1) (m : ℕ) :
    𝔍 ^ m ≤ (Ideal.span {(𝓣).ξExt (xi p) ρ} ^ m).comap (awayToExt p ρ) := by
  rw [ker_pow_eq_span, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap,
    map_pow, awayToExt_xiA, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton_self _

variable (p) in

def jetMap (ρ : Set.Ioo (0 : ℝ) 1) (m : ℕ) :
    𝔸 ⧸ 𝔍 ^ m →+* (𝓣).RobbaExt ρ ⧸ Ideal.span {(𝓣).ξExt (xi p) ρ} ^ m :=
  Ideal.quotientMap _ (awayToExt p ρ) (ker_pow_le_comap ρ m)

theorem jetMap_mk (ρ : Set.Ioo (0 : ℝ) 1) (m : ℕ) (a : 𝔸) :
    jetMap p ρ m (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (awayToExt p ρ a) :=
  Ideal.quotientMap_mk

theorem jetMap_mk_eq_mk_iff (ρ : Set.Ioo (0 : ℝ) 1) (m : ℕ) (a : 𝔸) (x : (𝓣).RobbaExt ρ) :
    jetMap p ρ m (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ x ↔
      awayToExt p ρ a - x ∈ Ideal.span {(𝓣).ξExt (xi p) ρ} ^ m := by
  rw [jetMap_mk]
  exact Ideal.Quotient.eq

theorem jetMap_bijective (hρ : (p : ℝ)⁻¹ < ρ) (m : ℕ) : Function.Bijective (jetMap p ρ m) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [jetMap_mk, Ideal.Quotient.eq_zero_iff_mem, awayToExt_mem_pow_iff hρ] at hq
    exact Ideal.Quotient.eq_zero_iff_mem.2 hq
  · intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, ha⟩ := exists_awayToExt_sub_mem_pow hρ m x
    exact ⟨Ideal.Quotient.mk (𝔍 ^ m) a, (jetMap_mk_eq_mk_iff ρ m a x).2 ha⟩

variable (p) in

def jetEquiv (hρ : (p : ℝ)⁻¹ < ρ) (m : ℕ) :
    (𝔸 ⧸ 𝔍 ^ m) ≃+* ((𝓣).RobbaExt ρ ⧸ Ideal.span {(𝓣).ξExt (xi p) ρ} ^ m) :=
  RingEquiv.ofBijective (jetMap p ρ m) (jetMap_bijective hρ m)

variable (p) in

def iotaQ (hρ : (p : ℝ)⁻¹ < ρ) (m : ℕ) : (𝓣).RobbaExt ρ →+* 𝔸 ⧸ 𝔍 ^ m :=
  (jetEquiv p hρ m).symm.toRingHom.comp (Ideal.Quotient.mk _)

theorem iotaQ_eq_mk_iff (hρ : (p : ℝ)⁻¹ < ρ) {m : ℕ} {x : (𝓣).RobbaExt ρ} {a : 𝔸} :
    iotaQ p hρ m x = Ideal.Quotient.mk _ a ↔
      x - awayToExt p ρ a ∈ Ideal.span {(𝓣).ξExt (xi p) ρ} ^ m := by
  have e : (jetEquiv p hρ m) (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (awayToExt p ρ a) :=
    jetMap_mk ρ m a
  show (jetEquiv p hρ m).symm (Ideal.Quotient.mk _ x) = _ ↔ _
  rw [RingEquiv.symm_apply_eq, e]
  exact Ideal.Quotient.eq

theorem iotaQ_compat (hρ : (p : ℝ)⁻¹ < ρ) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow 𝔍 hle).comp (iotaQ p hρ n) = iotaQ p hρ m := by
  ext x
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (iotaQ p hρ n x)
  rw [RingHom.comp_apply, ← ha]
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  rw [eq_comm, iotaQ_eq_mk_iff]
  exact Ideal.pow_le_pow_right hle ((iotaQ_eq_mk_iff hρ).1 ha.symm)

variable (p) in

def iota (hρ : (p : ℝ)⁻¹ < ρ) : (𝓣).RobbaExt ρ →+* 𝔹 :=
  _root_.AdicCompletion.liftRingHom 𝔍 (iotaQ p hρ) fun hle => iotaQ_compat hρ hle

theorem evalB_iota (hρ : (p : ℝ)⁻¹ < ρ) (m : ℕ) (x : (𝓣).RobbaExt ρ) :
    evalB ℂ_[p] p m (iota p hρ x) = iotaQ p hρ m x :=
  _root_.AdicCompletion.evalₐ_liftRingHom _ _ _ m x

theorem evalB_iota_eq_mk_iff (hρ : (p : ℝ)⁻¹ < ρ) {m : ℕ} {x : (𝓣).RobbaExt ρ} {a : 𝔸} :
    evalB ℂ_[p] p m (iota p hρ x) = Ideal.Quotient.mk _ a ↔
      x - awayToExt p ρ a ∈ Ideal.span {(𝓣).ξExt (xi p) ρ} ^ m := by
  rw [evalB_iota, iotaQ_eq_mk_iff]

theorem iota_awayToExt (hρ : (p : ℝ)⁻¹ < ρ) (a : 𝔸) :
    iota p hρ (awayToExt p ρ a) = toBDeRhamPlus (normInteger ℂ_[p]) p a := by
  refine evalB_ext fun m => ?_
  rw [evalB_toBDeRhamPlus, evalB_iota_eq_mk_iff, sub_self]
  exact zero_mem _

theorem iota_res {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} (hρ1 : (p : ℝ)⁻¹ < ρ1) (h : (ρ1 : ℝ) ≤ ρ0)
    (x : (𝓣).RobbaExt ρ0) :
    iota p hρ1 ((𝓣).res h x) = iota p (hρ1.trans_le h) x := by
  refine evalB_ext fun m => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalB ℂ_[p] p m (iota p (hρ1.trans_le h) x))
  rw [← ha, evalB_iota_eq_mk_iff]
  have h2 := (evalB_iota_eq_mk_iff (hρ1.trans_le h)).1 ha.symm
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h2 ⊢
  obtain ⟨y, hy⟩ := h2
  refine ⟨(𝓣).res h y, ?_⟩
  rw [← res_awayToExt h, ← map_sub, ← hy, map_mul, map_pow, res_ξExt]

theorem mult_ξExt_pow_mul (hρ : (p : ℝ)⁻¹ < ρ) (m : ℕ) {y : (𝓣).RobbaExt ρ} (hy : y ≠ 0) :
    (𝓣).mult ((𝓣).ξExt (xi p) ρ ^ m * y) ((𝓣).ptRad (xi p)) =
      m + (𝓣).mult y ((𝓣).ptRad (xi p)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h0 : (𝓣).ξExt (xi p) ρ ^ m * y ≠ 0 := mul_ne_zero (pow_ne_zero _ (ξExt_ne_zero ρ)) hy
    rw [pow_succ', mul_assoc, (𝓣).mult_mul (ξExt_ne_zero ρ) h0
      ⟨(𝓣).ptRad_pos' isPrimOne_xi, ptRad_xi_lt hρ⟩, ih,
      (𝓣).mult_ξExt isPrimOne_xi (ptRad_xi_lt hρ)]
    push_cast
    ring

theorem eq_zero_of_forall_mem_pow (hρ : (p : ℝ)⁻¹ < ρ) {x : (𝓣).RobbaExt ρ}
    (h : ∀ m : ℕ, x ∈ Ideal.span {(𝓣).ξExt (xi p) ρ} ^ m) : x = 0 := by
  by_contra hx
  set k := (𝓣).mult x ((𝓣).ptRad (xi p)) with hk
  have hm := h (k.toNat + 1)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hm
  obtain ⟨y, hy⟩ := hm
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hy
    exact hx hy.symm
  have h1 := mult_ξExt_pow_mul hρ (k.toNat + 1) hy0
  rw [mul_comm, hy, ← hk] at h1
  have hk0 : 0 ≤ k := (𝓣).mult_nonneg x _
  have hy1 := (𝓣).mult_nonneg y ((𝓣).ptRad (xi p))
  push_cast at h1
  omega

theorem iota_injective (hρ : (p : ℝ)⁻¹ < ρ) : Function.Injective (iota p hρ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine eq_zero_of_forall_mem_pow hρ fun m => ?_
  have h := (evalB_iota_eq_mk_iff hρ (m := m) (x := x) (a := 0)).1 (by rw [hx, map_zero, map_zero])
  rwa [map_zero, sub_zero] at h

section Galois

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem toB_galAway (σ : Gal(PadicAlgCl p/K)) (a : 𝔸) :
    toB ℂ_[p] p (galAway σ a) = (galIso σ).toB (toB ℂ_[p] p a) := by
  have : (toB ℂ_[p] p).comp (galAway σ) =
      ((galIso σ).toB : (𝓣).B →+* (𝓣).B).comp (toB ℂ_[p] p) :=
    IsLocalization.ringHom_ext (Submonoid.powers (p : AInf ℂ_[p] p)) (RingHom.ext fun y => by
      simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
      rw [galAway_algebraMap, toB_algebraMap, toB_algebraMap, TeichLift.TeichIso.toB_algebraMap,
        galIso_incl])
  exact RingHom.congr_fun this a

theorem extMap_awayToExt (σ : Gal(PadicAlgCl p/K)) (a : 𝔸) :
    (galIso σ).extMap ρ (awayToExt p ρ a) = awayToExt p ρ (galAway σ a) := by
  rw [awayToExt_apply, TeichLift.TeichIso.extMap_coe, awayToExt_apply]
  congr 1
  exact Subtype.ext (toB_galAway σ a).symm

theorem extMap_ξExt_mem (σ : Gal(PadicAlgCl p/K)) :
    (galIso σ).extMap ρ ((𝓣).ξExt (xi p) ρ) ∈ Ideal.span {(𝓣).ξExt (xi p) ρ} := by
  have h : σ • xiA p ∈ RingHom.ker θ := gal_smul_mem_ker_fontaineTheta σ
    (by rw [ker_theta_eq_span_xiA]; exact Ideal.mem_span_singleton_self _)
  rw [ker_theta_eq_span_xiA, Ideal.mem_span_singleton'] at h
  obtain ⟨c, hc⟩ := h
  rw [← awayToExt_xiA, extMap_awayToExt, galAway_algebraMap, ← hc, map_mul, map_mul, awayToExt_xiA]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem extMap_mem_pow (σ : Gal(PadicAlgCl p/K)) {m : ℕ} {x : (𝓣).RobbaExt ρ}
    (hx : x ∈ Ideal.span {(𝓣).ξExt (xi p) ρ} ^ m) :
    (galIso σ).extMap ρ x ∈ Ideal.span {(𝓣).ξExt (xi p) ρ} ^ m := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [map_mul, map_pow]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (extMap_ξExt_mem σ) m)

theorem iota_extMap (hρ : (p : ℝ)⁻¹ < ρ) (σ : Gal(PadicAlgCl p/K)) (x : (𝓣).RobbaExt ρ) :
    iota p hρ ((galIso σ).extMap ρ x) = σ • iota p hρ x := by
  refine evalB_ext fun m => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalB ℂ_[p] p m (iota p hρ x))
  rw [gal_smul_bdR_def, evalB_galBdRHom, ← ha, galQuot_mk, evalB_iota_eq_mk_iff,
    ← extMap_awayToExt, ← map_sub]
  exact extMap_mem_pow σ ((evalB_iota_eq_mk_iff hρ).1 ha.symm)

end Galois

variable (p) in

def thetaAway : 𝔸 →+* ℂ_[p] :=
  (awayEquiv (K := ℂ_[p]) p).toRingEquiv.toRingHom.comp (fontaineThetaInvertP (normInteger ℂ_[p]) p)

theorem thetaAway_algebraMap (y : AInf ℂ_[p] p) :
    thetaAway p (algebraMap _ 𝔸 y) = ((θ y : normInteger ℂ_[p]) : ℂ_[p]) := by
  simp only [thetaAway, RingHom.comp_apply, fontaineThetaInvertP_algebraMap]
  exact (awayEquiv (K := ℂ_[p]) p).commutes (θ y)

theorem thetaBDeRhamPlusField_toBDeRhamPlus (a : 𝔸) :
    thetaBDeRhamPlusField p (toBDeRhamPlus (normInteger ℂ_[p]) p a) = thetaAway p a := by
  simp only [thetaBDeRhamPlusField, thetaAway, RingHom.comp_apply, thetaBDeRhamPlus_toBDeRhamPlus]

theorem ker_thetaAway : RingHom.ker (thetaAway p) = 𝔍 := by
  ext a
  simp only [RingHom.mem_ker, thetaAway, RingHom.comp_apply]
  exact map_eq_zero_iff _ (awayEquiv (K := ℂ_[p]) p).injective

theorem thetaAway_surjective : Function.Surjective (thetaAway p) :=
  (awayEquiv (K := ℂ_[p]) p).surjective.comp
    (surjective_fontaineThetaInvertP (normInteger ℂ_[p]) p
      (IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[p]) p))

variable (p) in

def cXi : (𝓣).UntiltField (isPrimOne_xi (p := p)) ≃+* ℂ_[p] :=
  ((RingHom.quotientKerEquivOfSurjective (thetaXi_surjective (p := p))).symm.trans
    (Ideal.quotEquivOfEq (ker_thetaXi.trans ker_thetaAway.symm))).trans
    (RingHom.quotientKerEquivOfSurjective (thetaAway_surjective (p := p)))

theorem cXi_thetaXi (a : 𝔸) : cXi p (thetaXi p a) = thetaAway p a := by
  have h1 : (RingHom.quotientKerEquivOfSurjective (thetaXi_surjective (p := p))).symm (thetaXi p a) =
      Ideal.Quotient.mk _ a := by
    rw [RingEquiv.symm_apply_eq]; rfl
  simp only [cXi, RingEquiv.trans_apply, h1]
  rfl

theorem cXi_toUntiltField (y : AInf ℂ_[p] p) :
    cXi p ((𝓣).toUntiltField isPrimOne_xi ((𝓣).toUntilt (xi p) ⟨incl ℂ_[p] p y, incl_mem_int y⟩)) =
      ((θ y : normInteger ℂ_[p]) : ℂ_[p]) := by
  rw [← thetaXi_algebraMap, cXi_thetaXi, thetaAway_algebraMap]

theorem cXi_ptPi : cXi p ((𝓣).ptPi isPrimOne_xi) = (p : ℂ_[p]) := by
  rw [← thetaXi_algebraMap_p, cXi_thetaXi, map_natCast, map_natCast]

theorem norm_cXi_toUntilt_le_one (Y : (𝓣).int) :
    ‖cXi p ((𝓣).toUntiltField isPrimOne_xi ((𝓣).toUntilt (xi p) Y))‖ ≤ 1 := by
  obtain ⟨y, hy⟩ := Y.2
  have hY : Y = ⟨incl ℂ_[p] p y, incl_mem_int y⟩ := Subtype.ext hy.symm
  rw [hY, cXi_toUntiltField]
  exact mem_normInteger.1 (θ y).2

theorem norm_cXi_toUntilt_of_isUnit {u : (𝓣).Untilt (xi p)} (hu : IsUnit u) :
    ‖cXi p ((𝓣).toUntiltField isPrimOne_xi u)‖ = 1 := by
  obtain ⟨v, huv⟩ := hu.exists_right_inv
  obtain ⟨U, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨V, rfl⟩ := Ideal.Quotient.mk_surjective v
  have h := congrArg (fun w => ‖cXi p ((𝓣).toUntiltField isPrimOne_xi w)‖) huv
  simp only [map_mul, map_one, norm_mul, norm_one] at h
  have h1 := norm_cXi_toUntilt_le_one (p := p) U
  have h2 := norm_cXi_toUntilt_le_one (p := p) V
  nlinarith [norm_nonneg (cXi p ((𝓣).toUntiltField isPrimOne_xi (Ideal.Quotient.mk _ U))),
    norm_nonneg (cXi p ((𝓣).toUntiltField isPrimOne_xi (Ideal.Quotient.mk _ V)))]

theorem norm_cXi_toUntilt_teich {z : Cb p} (hz : ‖z‖ ≤ 1) :
    ‖cXi p ((𝓣).toUntiltField isPrimOne_xi ((𝓣).toUntilt (xi p) ((𝓣).teichInt hz)))‖ = ‖z‖ := by
  obtain ⟨z', rfl⟩ := norm_le_one_iff_exists_algebraMap.1 hz
  have e : (𝓣).teichInt hz = ⟨incl ℂ_[p] p (teichmuller p z'), incl_mem_int _⟩ :=
    Subtype.ext (by
      show (𝓣).teich (algebraMap (Ob p) (Cb p) z') = incl ℂ_[p] p (teichmuller p z')
      rw [incl_teichmuller]; exact teich_eq _)
  rw [e, cXi_toUntiltField, fontaineTheta_teichmuller, norm_algebraMap_preTilt, preTilt_norm_def]

theorem norm_cXi_toUntilt (Y : (𝓣).int) :
    ‖cXi p ((𝓣).toUntiltField isPrimOne_xi ((𝓣).toUntilt (xi p) Y))‖ =
      (𝓣).untiltNorm isPrimOne_xi ((𝓣).toUntilt (xi p) Y) := by
  by_cases hq : (𝓣).toUntilt (xi p) Y = 0
  · rw [hq, map_zero, map_zero, norm_zero, ((𝓣).untiltNorm_eq_zero_iff isPrimOne_xi).2 rfl]
  obtain ⟨z, hz0, hz, u, hu, hqu⟩ := (𝓣).exists_teich_mul_unit isPrimOne_xi hq
  rw [(𝓣).untiltNorm_eq isPrimOne_xi hz0 hz hu hqu, hqu, map_mul, map_mul, norm_mul,
    norm_cXi_toUntilt_teich, norm_cXi_toUntilt_of_isUnit hu, mul_one]

theorem norm_cXi (w : (𝓣).UntiltField (isPrimOne_xi (p := p))) : ‖cXi p w‖ = ‖w‖ := by
  obtain ⟨a, rfl⟩ := thetaXi_surjective w
  obtain ⟨N, y, hy⟩ := IsLocalization.Away.surj (p : AInf ℂ_[p] p) a
  have h1 := congrArg (fun b => ‖cXi p (thetaXi p b)‖) hy
  have h2 := congrArg (fun b => ‖thetaXi p b‖) hy
  simp only [map_mul, map_pow, norm_mul, norm_pow, thetaXi_algebraMap_p, cXi_ptPi] at h1 h2
  rw [thetaXi_algebraMap, norm_cXi_toUntilt] at h1
  rw [thetaXi_algebraMap, norm_toUntiltField] at h2
  have hπ : ‖(𝓣).ptPi (isPrimOne_xi (p := p))‖ = ‖(p : ℂ_[p])‖ := by
    rw [norm_ptPi, norm_natCast_p]; exact ptRad_xi
  rw [hπ] at h2
  have hp0 : ‖(p : ℂ_[p])‖ ^ N ≠ 0 := pow_ne_zero _ (by rw [norm_natCast_p]; exact inv_p_pos.ne')
  exact mul_right_cancel₀ hp0 (h1.trans h2.symm)

theorem theta_iota (hρ : (p : ℝ)⁻¹ < ρ) (x : (𝓣).RobbaExt ρ) :
    thetaBDeRhamPlusField p (iota p hρ x) = cXi p ((𝓣).ptEval isPrimOne_xi (ptRad_xi_le hρ) x) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalB ℂ_[p] p 1 (iota p hρ x))
  have h1 := (evalB_iota_eq_mk_iff hρ).1 ha.symm
  rw [pow_one, Ideal.mem_span_singleton'] at h1
  obtain ⟨y, hy⟩ := h1
  have h2 : (𝓣).ptEval isPrimOne_xi (ptRad_xi_le hρ) x = thetaXi p a := by
    rw [← ptEval_awayToExt (ptRad_xi_le hρ), ← sub_eq_zero, ← map_sub, ← hy, map_mul,
      (𝓣).ptEval_ξExt isPrimOne_xi, mul_zero]
  have h3 : thetaBDeRhamPlus (normInteger ℂ_[p]) p
      (iota p hρ x - toBDeRhamPlus (normInteger ℂ_[p]) p a) = 0 :=
    thetaBDeRhamPlus_eq_zero_of_evalB_one_eq_zero (by rw [map_sub, ← ha, evalB_toBDeRhamPlus, sub_self])
  have h4 : thetaBDeRhamPlusField p (iota p hρ x - toBDeRhamPlus (normInteger ℂ_[p]) p a) = 0 := by
    simp only [thetaBDeRhamPlusField, RingHom.comp_apply, h3, map_zero]
  rw [map_sub, sub_eq_zero, thetaBDeRhamPlusField_toBDeRhamPlus] at h4
  rw [h4, h2, cXi_thetaXi]

variable (p) in

def inversePRadius (hρ : (p : ℝ)⁻¹ < ρ) : Set.Ioc (0 : ℝ) ρ := ⟨(p : ℝ)⁻¹, inv_p_pos, hρ.le⟩

theorem inverse_p_radius_eq_ptRadIoc (hρ : (p : ℝ)⁻¹ < ρ) :
    inversePRadius p hρ = (𝓣).ptRadIoc isPrimOne_xi (ptRad_xi_le hρ) :=
  Subtype.ext ptRad_xi.symm

theorem awayToExt_natCast (ρ : Set.Ioo (0 : ℝ) 1) :
    awayToExt p ρ (algebraMap (AInf ℂ_[p] p) 𝔸 (p : AInf ℂ_[p] p)) = (p : (𝓣).RobbaExt ρ) := by
  rw [map_natCast, map_natCast]

theorem extNorm_awayToExt_algebraMap_le (hρ : (p : ℝ)⁻¹ < ρ) (y : AInf ℂ_[p] p) :
    (𝓣).extNorm ρ (inversePRadius p hρ) (awayToExt p ρ (algebraMap _ 𝔸 y)) ≤ 1 := by
  rw [awayToExt_apply, extNorm_coe]
  show gaussNorm ((𝓣).coeffB (toB ℂ_[p] p (algebraMap _ 𝔸 y))) (p : ℝ)⁻¹ ≤ 1
  rw [toB_algebraMap, coeffB_algebraMap]
  exact (𝓣).gaussNorm_le_one_of_mem_int (incl_mem_int y) inv_p_pos inv_p_lt_one.le

theorem extNorm_natCast_p (hρ : (p : ℝ)⁻¹ < ρ) :
    (𝓣).extNorm ρ (inversePRadius p hρ) (p : (𝓣).RobbaExt ρ) = (p : ℝ)⁻¹ := by
  rw [← awayToExt_natCast, awayToExt_apply, extNorm_coe]
  show gaussNorm ((𝓣).coeffB (toB ℂ_[p] p (algebraMap _ 𝔸 (p : AInf ℂ_[p] p)))) (p : ℝ)⁻¹ = _
  rw [toB_algebraMap, coeffB_algebraMap, map_natCast (incl ℂ_[p] p)]
  exact (𝓣).gaussNorm_π inv_p_pos

theorem exists_lift_step (hρ : (p : ℝ)⁻¹ < ρ) {w : (𝓣).RobbaExt ρ}
    (hw : (𝓣).extNorm ρ (inversePRadius p hρ) w ≤ 1) :
    ∃ (l : AInf ℂ_[p] p) (w' : (𝓣).RobbaExt ρ),
      w = awayToExt p ρ (algebraMap _ 𝔸 l) + (𝓣).ξExt (xi p) ρ * w' ∧
      (𝓣).extNorm ρ (inversePRadius p hρ) ((p : (𝓣).RobbaExt ρ) * w') ≤ 1 := by
  have hv : ‖(𝓣).ptEval isPrimOne_xi (ptRad_xi_le hρ) w‖ ≤ 1 := by
    refine ((𝓣).norm_ptEval_le isPrimOne_xi (ptRad_xi_le hρ) w).trans ?_
    rw [← inverse_p_radius_eq_ptRadIoc]; exact hw
  obtain ⟨q, hq⟩ := (𝓣).exists_toUntiltField_eq isPrimOne_xi hv
  obtain ⟨Y, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨l, hl⟩ := Y.2
  have hY : Y = ⟨incl ℂ_[p] p l, incl_mem_int l⟩ := Subtype.ext hl.symm
  have h0 : (𝓣).ptEval isPrimOne_xi (ptRad_xi_le hρ) (w - awayToExt p ρ (algebraMap _ 𝔸 l)) = 0 := by
    rw [map_sub, ptEval_awayToExt, thetaXi_algebraMap, ← hY]
    exact sub_eq_zero.2 hq.symm
  obtain ⟨w', hw'⟩ := ((𝓣).ptEval_eq_zero_iff isPrimOne_xi (ptRad_xi_le hρ) _).1 h0
  refine ⟨l, w', by rw [← hw', add_sub_cancel], ?_⟩
  have hN : (𝓣).extNorm ρ (inversePRadius p hρ) ((𝓣).ξExt (xi p) ρ * w') ≤ 1 := by
    rw [← hw', sub_eq_add_neg]
    refine ((𝓣).extNorm_add_le _ _ _).trans (max_le hw ?_)
    rw [(𝓣).extNorm_neg]
    exact extNorm_awayToExt_algebraMap_le hρ l
  rw [(𝓣).extNorm_mul, (𝓣).extNorm_ξExt isPrimOne_xi] at hN
  rw [(𝓣).extNorm_mul, extNorm_natCast_p]
  have e : max ((𝓣).ptRad (xi p)) ((inversePRadius p hρ : Set.Ioc (0 : ℝ) ρ) : ℝ) = (p : ℝ)⁻¹ := by
    rw [ptRad_xi]; exact max_self _
  rwa [e] at hN

theorem exists_pow_mul_sub_mem (hρ : (p : ℝ)⁻¹ < ρ) (m : ℕ) :
    ∀ w : (𝓣).RobbaExt ρ, (𝓣).extNorm ρ (inversePRadius p hρ) w ≤ 1 →
      ∃ y : AInf ℂ_[p] p, (p : (𝓣).RobbaExt ρ) ^ m * w - awayToExt p ρ (algebraMap _ 𝔸 y) ∈
        Ideal.span {(𝓣).ξExt (xi p) ρ} ^ (m + 1) := by
  set ξ := (𝓣).ξExt (xi p) ρ with hξdef
  induction m with
  | zero =>
    intro w hw
    obtain ⟨l, w', rfl, -⟩ := exists_lift_step hρ hw
    refine ⟨l, ?_⟩
    rw [pow_zero, one_mul, add_sub_cancel_left, zero_add, pow_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  | succ m ih =>
    intro w hw
    obtain ⟨l, w', rfl, hw'⟩ := exists_lift_step hρ hw
    obtain ⟨y', hy'⟩ := ih _ hw'
    refine ⟨(p : AInf ℂ_[p] p) ^ (m + 1) * l + xiA p * y', ?_⟩
    have e : (p : (𝓣).RobbaExt ρ) ^ (m + 1) * (awayToExt p ρ (algebraMap _ 𝔸 l) +
        ξ * w') - awayToExt p ρ (algebraMap _ 𝔸
          ((p : AInf ℂ_[p] p) ^ (m + 1) * l + xiA p * y')) =
        ξ * ((p : (𝓣).RobbaExt ρ) ^ m * ((p : (𝓣).RobbaExt ρ) * w') -
          awayToExt p ρ (algebraMap _ 𝔸 y')) := by
      simp only [map_add, map_mul, map_pow, map_natCast]
      rw [awayToExt_xiA ρ]
      ring
    rw [e, pow_succ' _ (m + 1)]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hy'

theorem exists_evalB_pow_mul_iota_eq (hρ : (p : ℝ)⁻¹ < ρ) {w : (𝓣).RobbaExt ρ}
    (hw : (𝓣).extNorm ρ (inversePRadius p hρ) w ≤ 1) (m : ℕ) :
    ∃ y : AInf ℂ_[p] p, evalB ℂ_[p] p (m + 1) ((p : 𝔹) ^ m * iota p hρ w) =
      Ideal.Quotient.mk _ (algebraMap _ 𝔸 y) := by
  obtain ⟨y, hy⟩ := exists_pow_mul_sub_mem hρ m w hw
  refine ⟨y, ?_⟩
  have e : (p : 𝔹) ^ m * iota p hρ w = iota p hρ ((p : (𝓣).RobbaExt ρ) ^ m * w) := by
    rw [map_mul, map_pow, map_natCast]
  rw [e, evalB_iota_eq_mk_iff]
  exact hy

theorem pow_mul_evalB_iota_mem_latticeQ (hρ : (p : ℝ)⁻¹ < ρ) {w : (𝓣).RobbaExt ρ}
    (hw : (𝓣).extNorm ρ (inversePRadius p hρ) w ≤ 1) (m : ℕ) :
    (p : 𝔸 ⧸ 𝔍 ^ (m + 1)) ^ m * evalB ℂ_[p] p (m + 1) (iota p hρ w) ∈
      ACris.latticeQ ℂ_[p] p (m + 1) := by
  obtain ⟨y, hy⟩ := exists_evalB_pow_mul_iota_eq hρ hw m
  rw [map_mul, map_pow, map_natCast] at hy
  rw [hy]
  exact ⟨y, rfl⟩

variable (p) in

def pUnit : 𝔸ˣ := (IsLocalization.Away.algebraMap_isUnit (p : AInf ℂ_[p] p)).unit

theorem coe_pUnit : ((pUnit p : 𝔸ˣ) : 𝔸) = algebraMap _ 𝔸 (p : AInf ℂ_[p] p) := rfl

theorem evalB_iota_awayToExt (hρ : (p : ℝ)⁻¹ < ρ) (m : ℕ) (a : 𝔸) :
    evalB ℂ_[p] p m (iota p hρ (awayToExt p ρ a)) = Ideal.Quotient.mk _ a := by
  rw [evalB_iota_eq_mk_iff, sub_self]
  exact zero_mem _

theorem extNorm_awayToExt_pUnit_zpow (hρ : (p : ℝ)⁻¹ < ρ) (k : ℤ) :
    (𝓣).extNorm ρ (inversePRadius p hρ) (awayToExt p ρ ((pUnit p ^ k : 𝔸ˣ) : 𝔸)) = (p : ℝ) ^ (-k) := by
  have hpos : (0 : ℝ) < p := Nat.cast_pos.2 hp.out.pos
  have hnat : ∀ n : ℕ, (𝓣).extNorm ρ (inversePRadius p hρ) (awayToExt p ρ ((pUnit p ^ n : 𝔸ˣ) : 𝔸)) =
      ((p : ℝ)⁻¹) ^ n := by
    intro n
    induction n with
    | zero => rw [pow_zero, Units.val_one, map_one, (𝓣).extNorm_one, pow_zero]
    | succ n ih =>
      rw [pow_succ, Units.val_mul, map_mul, (𝓣).extNorm_mul, ih, coe_pUnit, awayToExt_natCast,
        extNorm_natCast_p, pow_succ]
  have hinv : ∀ u : 𝔸ˣ, (𝓣).extNorm ρ (inversePRadius p hρ) (awayToExt p ρ ((u⁻¹ : 𝔸ˣ) : 𝔸)) *
      (𝓣).extNorm ρ (inversePRadius p hρ) (awayToExt p ρ (u : 𝔸)) = 1 := by
    intro u
    rw [← (𝓣).extNorm_mul, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one,
      (𝓣).extNorm_one]
  rcases k with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast, hnat, zpow_neg, zpow_natCast, inv_pow]
  · rw [zpow_negSucc, Int.neg_negSucc, zpow_natCast]
    have h := hinv (pUnit p ^ (n + 1))
    rw [hnat, inv_pow, mul_inv_eq_one₀ (pow_ne_zero _ hpos.ne')] at h
    exact h

set_option maxHeartbeats 2000000 in

theorem exists_evalB_iota_eq_zpow (hρ : (p : ℝ)⁻¹ < ρ) {w : (𝓣).RobbaExt ρ} {c : ℤ}
    (hw : (𝓣).extNorm ρ (inversePRadius p hρ) w ≤ (p : ℝ) ^ (-c)) (m : ℕ) :
    ∃ y : AInf ℂ_[p] p, evalB ℂ_[p] p (m + 1) (iota p hρ w) =
      Ideal.Quotient.mk _ (((pUnit p ^ (c - m) : 𝔸ˣ) : 𝔸) * algebraMap _ 𝔸 y) := by
  have hpos : (0 : ℝ) < p := Nat.cast_pos.2 hp.out.pos
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, w₀ = awayToExt p ρ ((pUnit p ^ (-c) : 𝔸ˣ) : 𝔸) * w := ⟨_, rfl⟩
  have hw₀n : (𝓣).extNorm ρ (inversePRadius p hρ) w₀ ≤ 1 := by
    rw [hw₀, (𝓣).extNorm_mul, extNorm_awayToExt_pUnit_zpow, neg_neg]
    calc (p : ℝ) ^ c * (𝓣).extNorm ρ (inversePRadius p hρ) w ≤ (p : ℝ) ^ c * (p : ℝ) ^ (-c) :=
          mul_le_mul_of_nonneg_left hw (zpow_nonneg hpos.le c)
      _ = 1 := by rw [← zpow_add₀ hpos.ne', add_neg_cancel, zpow_zero]
  obtain ⟨y, hy⟩ := exists_evalB_pow_mul_iota_eq hρ hw₀n m
  refine ⟨y, ?_⟩
  have hw' : w = awayToExt p ρ ((pUnit p ^ c : 𝔸ˣ) : 𝔸) * w₀ := by
    rw [hw₀, ← mul_assoc, ← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero,
      Units.val_one, map_one, one_mul]
  have hpm : (p : 𝔹) ^ m = toBDeRhamPlus (normInteger ℂ_[p]) p ((pUnit p ^ (m : ℤ) : 𝔸ˣ) : 𝔸) := by
    rw [zpow_natCast, Units.val_pow_eq_pow_val, coe_pUnit]
    simp only [map_pow, map_natCast]
  rw [hpm, map_mul, evalB_toBDeRhamPlus (m + 1) ((pUnit p ^ (m : ℤ) : 𝔸ˣ) : 𝔸)] at hy
  have e : ((pUnit p ^ (c - m) : 𝔸ˣ) : 𝔸) =
      ((pUnit p ^ c : 𝔸ˣ) : 𝔸) * ((pUnit p ^ (-(m : ℤ)) : 𝔸ˣ) : 𝔸) := by
    rw [← Units.val_mul, ← zpow_add, sub_eq_add_neg]
  have hE : evalB ℂ_[p] p (m + 1) (iota p hρ w) =
      Ideal.Quotient.mk (𝔍 ^ (m + 1)) ((pUnit p ^ c : 𝔸ˣ) : 𝔸) *
        evalB ℂ_[p] p (m + 1) (iota p hρ w₀) := by
    rw [hw', map_mul, map_mul, evalB_iota_awayToExt]
  have hu : Ideal.Quotient.mk (𝔍 ^ (m + 1)) ((pUnit p ^ (-(m : ℤ)) : 𝔸ˣ) : 𝔸) *
      Ideal.Quotient.mk (𝔍 ^ (m + 1)) ((pUnit p ^ (m : ℤ) : 𝔸ˣ) : 𝔸) = 1 := by
    rw [← map_mul, zpow_neg, Units.inv_mul, map_one]
  rw [e, map_mul, map_mul, ← hy, hE, ← mul_assoc,
    mul_assoc (Ideal.Quotient.mk (𝔍 ^ (m + 1)) ((pUnit p ^ c : 𝔸ˣ) : 𝔸)), hu, mul_one]

def InDom (x : (𝓣).RobbaTilde) : Prop :=
  ∃ ρ : Set.Ioo (0 : ℝ) 1, (p : ℝ)⁻¹ < ρ ∧ ∃ y : (𝓣).RobbaExt ρ, (𝓣).ofRad ρ y = x

theorem exists_common {x y : (𝓣).RobbaTilde} (hx : InDom x) (hy : InDom y) :
    ∃ (ρ : Set.Ioo (0 : ℝ) 1) (_ : (p : ℝ)⁻¹ < ρ) (x' y' : (𝓣).RobbaExt ρ),
      (𝓣).ofRad ρ x' = x ∧ (𝓣).ofRad ρ y' = y := by
  obtain ⟨ρ1, h1, x1, rfl⟩ := hx
  obtain ⟨ρ2, h2, y2, rfl⟩ := hy
  let ρ3 : Set.Ioo (0 : ℝ) 1 := ⟨min ρ1 ρ2, lt_min ρ1.2.1 ρ2.2.1, min_lt_of_left_lt ρ1.2.2⟩
  exact ⟨ρ3, lt_min h1 h2, (𝓣).res (ρ1 := ρ3) (min_le_left _ _) x1,
    (𝓣).res (ρ1 := ρ3) (min_le_right _ _) y2, (𝓣).ofRad_res _ _, (𝓣).ofRad_res _ _⟩

variable (p) in

def rhoMid : Set.Ioo (0 : ℝ) 1 :=
  ⟨(1 + (p : ℝ)⁻¹) / 2, by have := inv_p_pos (p := p); positivity,
    by have := inv_p_lt_one (p := p); linarith⟩

theorem inv_p_lt_rhoMid : (p : ℝ)⁻¹ < rhoMid p := by
  show (p : ℝ)⁻¹ < (1 + (p : ℝ)⁻¹) / 2
  have := inv_p_lt_one (p := p); linarith

variable (p) in

def tildeDom : Subring (𝓣).RobbaTilde where
  carrier := {x | InDom x}
  mul_mem' {x y} hx hy := by
    obtain ⟨ρ, hρ, x', y', rfl, rfl⟩ := exists_common hx hy
    exact ⟨ρ, hρ, x' * y', map_mul _ _ _⟩
  one_mem' := ⟨rhoMid p, inv_p_lt_rhoMid, 1, map_one _⟩
  add_mem' {x y} hx hy := by
    obtain ⟨ρ, hρ, x', y', rfl, rfl⟩ := exists_common hx hy
    exact ⟨ρ, hρ, x' + y', map_add _ _ _⟩
  zero_mem' := ⟨rhoMid p, inv_p_lt_rhoMid, 0, map_zero _⟩
  neg_mem' {x} hx := by
    obtain ⟨ρ, hρ, x', rfl⟩ := hx
    exact ⟨ρ, hρ, -x', map_neg _ _⟩

theorem ofRad_mem_tildeDom (hρ : (p : ℝ)⁻¹ < ρ) (y : (𝓣).RobbaExt ρ) :
    (𝓣).ofRad ρ y ∈ tildeDom p := ⟨ρ, hρ, y, rfl⟩

theorem iota_eq_of_ofRad_eq {ρ1 ρ2 : Set.Ioo (0 : ℝ) 1} (h1 : (p : ℝ)⁻¹ < ρ1) (h2 : (p : ℝ)⁻¹ < ρ2)
    {y1 : (𝓣).RobbaExt ρ1} {y2 : (𝓣).RobbaExt ρ2} (h : (𝓣).ofRad ρ1 y1 = (𝓣).ofRad ρ2 y2) :
    iota p h1 y1 = iota p h2 y2 := by
  let ρ3 : Set.Ioo (0 : ℝ) 1 := ⟨min ρ1 ρ2, lt_min ρ1.2.1 ρ2.2.1, min_lt_of_left_lt ρ1.2.2⟩
  have h3 : (p : ℝ)⁻¹ < ρ3 := lt_min h1 h2
  have e : (𝓣).res (ρ1 := ρ3) (min_le_left _ _) y1 = (𝓣).res (ρ1 := ρ3) (min_le_right _ _) y2 :=
    (𝓣).ofRad_injective ρ3 (by rw [(𝓣).ofRad_res, (𝓣).ofRad_res, h])
  rw [← iota_res h3 (min_le_left _ _), e, iota_res h3 (min_le_right _ _)]

open Classical in
variable (p) in

def iotaTildeFun (x : (𝓣).RobbaTilde) : 𝔹 :=
  if h : InDom x then iota p h.choose_spec.1 h.choose_spec.2.choose else 0

theorem iotaTildeFun_ofRad (hρ : (p : ℝ)⁻¹ < ρ) (y : (𝓣).RobbaExt ρ) :
    iotaTildeFun p ((𝓣).ofRad ρ y) = iota p hρ y := by
  have h : InDom ((𝓣).ofRad ρ y) := ⟨ρ, hρ, y, rfl⟩
  rw [iotaTildeFun, dif_pos h]
  exact iota_eq_of_ofRad_eq _ _ h.choose_spec.2.choose_spec

theorem iotaTildeFun_one : iotaTildeFun p 1 = 1 := by
  have e : (1 : (𝓣).RobbaTilde) = (𝓣).ofRad (rhoMid p) 1 := (map_one _).symm
  rw [e, iotaTildeFun_ofRad inv_p_lt_rhoMid, map_one]

theorem iotaTildeFun_zero : iotaTildeFun p 0 = 0 := by
  have e : (0 : (𝓣).RobbaTilde) = (𝓣).ofRad (rhoMid p) 0 := (map_zero _).symm
  rw [e, iotaTildeFun_ofRad inv_p_lt_rhoMid, map_zero]

theorem iotaTildeFun_mul {x y : (𝓣).RobbaTilde} (hx : x ∈ tildeDom p) (hy : y ∈ tildeDom p) :
    iotaTildeFun p (x * y) = iotaTildeFun p x * iotaTildeFun p y := by
  obtain ⟨ρ, hρ, x', y', rfl, rfl⟩ := exists_common hx hy
  rw [← map_mul, iotaTildeFun_ofRad hρ, iotaTildeFun_ofRad hρ, iotaTildeFun_ofRad hρ, map_mul]

theorem iotaTildeFun_add {x y : (𝓣).RobbaTilde} (hx : x ∈ tildeDom p) (hy : y ∈ tildeDom p) :
    iotaTildeFun p (x + y) = iotaTildeFun p x + iotaTildeFun p y := by
  obtain ⟨ρ, hρ, x', y', rfl, rfl⟩ := exists_common hx hy
  rw [← map_add, iotaTildeFun_ofRad hρ, iotaTildeFun_ofRad hρ, iotaTildeFun_ofRad hρ, map_add]

variable (p) in

def iotaTilde : tildeDom p →+* 𝔹 where
  toFun x := iotaTildeFun p x
  map_one' := iotaTildeFun_one
  map_mul' x y := iotaTildeFun_mul x.2 y.2
  map_zero' := iotaTildeFun_zero
  map_add' x y := iotaTildeFun_add x.2 y.2

theorem iotaTilde_apply (x : tildeDom p) : iotaTilde p x = iotaTildeFun p x := rfl

theorem iotaTilde_ofRad (hρ : (p : ℝ)⁻¹ < ρ) (y : (𝓣).RobbaExt ρ) :
    iotaTilde p ⟨(𝓣).ofRad ρ y, ofRad_mem_tildeDom hρ y⟩ = iota p hρ y :=
  iotaTildeFun_ofRad hρ y

theorem iotaTilde_injective : Function.Injective (iotaTilde p) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨x, ρ, hρ, y, rfl⟩ hx
  rw [iotaTilde_ofRad hρ] at hx
  have hy : y = 0 := iota_injective hρ (hx.trans (map_zero _).symm)
  apply Subtype.ext
  show (𝓣).ofRad ρ y = 0
  rw [hy, map_zero]

theorem rootRadius_coe (τ : Set.Ioo (0 : ℝ) 1) :
    ((frob ℂ_[p] p).rootRadius τ : ℝ) = (τ : ℝ) ^ ((p : ℝ)⁻¹) := by
  show (τ : ℝ) ^ ((((p ^ (frob ℂ_[p] p).a : ℕ)) : ℝ)⁻¹) = _
  rw [frob_a, pow_one]

theorem le_rootRadius (τ : Set.Ioo (0 : ℝ) 1) : (τ : ℝ) ≤ (frob ℂ_[p] p).rootRadius τ := by
  rw [rootRadius_coe]
  exact Real.self_le_rpow_of_le_one τ.2.1.le τ.2.2.le inv_p_lt_one.le

theorem tildeFrobSymm_mem_tildeDom {x : (𝓣).RobbaTilde} (hx : x ∈ tildeDom p) :
    (frob ℂ_[p] p).tildeFrobSymm x ∈ tildeDom p := by
  obtain ⟨ρ, hρ, y, rfl⟩ := hx
  rw [TeichLift.TeichFrob.tildeFrobSymm_ofRad]
  exact ⟨_, hρ.trans_le (le_rootRadius ρ), _, rfl⟩

theorem iterate_tildeFrobSymm_ofRad (N : ℕ) : ∀ (τ : Set.Ioo (0 : ℝ) 1) (y : (𝓣).RobbaExt τ),
    ∃ (τ' : Set.Ioo (0 : ℝ) 1) (y' : (𝓣).RobbaExt τ'),
      (frob ℂ_[p] p).tildeFrobSymm^[N] ((𝓣).ofRad τ y) = (𝓣).ofRad τ' y' ∧
        (τ' : ℝ) = (τ : ℝ) ^ ((p : ℝ)⁻¹ ^ N) := by
  induction N with
  | zero => intro τ y; exact ⟨τ, y, rfl, by rw [pow_zero, Real.rpow_one]⟩
  | succ N ih =>
    intro τ y
    obtain ⟨τ', y', h1, h2⟩ := ih _ ((frob ℂ_[p] p).extFrobSymm τ y)
    refine ⟨τ', y', ?_, ?_⟩
    · rw [Function.iterate_succ_apply, TeichLift.TeichFrob.tildeFrobSymm_ofRad, h1]
    · rw [h2, rootRadius_coe, ← Real.rpow_mul τ.2.1.le, pow_succ, mul_comm]

theorem exists_rpow_gt (τ : Set.Ioo (0 : ℝ) 1) : ∃ N : ℕ, (p : ℝ)⁻¹ < (τ : ℝ) ^ ((p : ℝ)⁻¹ ^ N) := by
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.2 hp.out.one_lt
  have hL : 0 < -Real.log τ := neg_pos.2 (Real.log_neg τ.2.1 τ.2.2)
  have hlp : 0 < Real.log p := Real.log_pos hp1
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hlp hL) (inv_p_lt_one (p := p))
  refine ⟨N, ?_⟩
  have e : (p : ℝ)⁻¹ = Real.exp (-Real.log p) := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
  rw [lt_div_iff₀ hL] at hN
  rw [Real.rpow_def_of_pos τ.2.1]
  calc (p : ℝ)⁻¹ = Real.exp (-Real.log p) := e
    _ < Real.exp (Real.log τ * (p : ℝ)⁻¹ ^ N) := Real.exp_lt_exp.2 (by nlinarith)

theorem exists_iterate_tildeFrobSymm_mem (x : (𝓣).RobbaTilde) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (frob ℂ_[p] p).tildeFrobSymm^[n] x ∈ tildeDom p := by
  obtain ⟨τ, y, rfl⟩ := (𝓣).exists_ofRad x
  obtain ⟨N, hN⟩ := exists_rpow_gt (p := p) τ
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm, Function.iterate_add_apply]
  obtain ⟨τ', y', h1, h2⟩ := iterate_tildeFrobSymm_ofRad N τ y
  rw [h1]
  have hmem : (𝓣).ofRad τ' y' ∈ tildeDom p := ⟨τ', by rw [h2]; exact hN, y', rfl⟩
  clear h1 h2 hn
  induction k with
  | zero => exact hmem
  | succ k ih => rw [Function.iterate_succ_apply']; exact tildeFrobSymm_mem_tildeDom ih

variable (p) in

def phiNeg (n : ℕ) : (𝓣).RobbaTilde →+* (𝓣).RobbaTilde := (frob ℂ_[p] p).tildeFrobSymm ^ n

theorem phiNeg_apply (n : ℕ) (x : (𝓣).RobbaTilde) :
    phiNeg p n x = (frob ℂ_[p] p).tildeFrobSymm^[n] x := by
  rw [phiNeg, RingHom.coe_pow]

theorem phiNeg_succ (n : ℕ) (x : (𝓣).RobbaTilde) :
    phiNeg p (n + 1) x = (frob ℂ_[p] p).tildeFrobSymm (phiNeg p n x) := by
  rw [phiNeg_apply, phiNeg_apply, Function.iterate_succ_apply']

theorem phiNeg_succ_tildeFrob (n : ℕ) (x : (𝓣).RobbaTilde) :
    phiNeg p (n + 1) ((frob ℂ_[p] p).tildeFrob x) = phiNeg p n x := by
  rw [phiNeg_apply, phiNeg_apply, Function.iterate_succ_apply,
    TeichLift.TeichFrob.tildeFrobSymm_tildeFrob]

theorem exists_phiNeg_mem (x : (𝓣).RobbaTilde) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → phiNeg p n x ∈ tildeDom p := by
  obtain ⟨N, hN⟩ := exists_iterate_tildeFrobSymm_mem (p := p) x
  exact ⟨N, fun n hn => by rw [phiNeg_apply]; exact hN n hn⟩

variable (p) in

def iotaN (n : ℕ) (x : (𝓣).RobbaTilde) : 𝔹 := iotaTildeFun p (phiNeg p n x)

variable (p) in

def thetaN (n : ℕ) (x : (𝓣).RobbaTilde) : ℂ_[p] := thetaBDeRhamPlusField p (iotaN p n x)

theorem iotaN_eq (n : ℕ) {x : (𝓣).RobbaTilde} (hx : phiNeg p n x ∈ tildeDom p) :
    iotaN p n x = iotaTilde p ⟨phiNeg p n x, hx⟩ := rfl

theorem iotaN_of_eq_ofRad {n : ℕ} {x : (𝓣).RobbaTilde} (hρ : (p : ℝ)⁻¹ < ρ) {y : (𝓣).RobbaExt ρ}
    (h : phiNeg p n x = (𝓣).ofRad ρ y) : iotaN p n x = iota p hρ y := by
  rw [iotaN, h, iotaTildeFun_ofRad hρ]

theorem thetaN_of_eq_ofRad {n : ℕ} {x : (𝓣).RobbaTilde} (hρ : (p : ℝ)⁻¹ < ρ) {y : (𝓣).RobbaExt ρ}
    (h : phiNeg p n x = (𝓣).ofRad ρ y) :
    thetaN p n x = cXi p ((𝓣).ptEval isPrimOne_xi (ptRad_xi_le hρ) y) := by
  rw [thetaN, iotaN_of_eq_ofRad hρ h, theta_iota]

theorem iotaN_add {n : ℕ} {x y : (𝓣).RobbaTilde} (hx : phiNeg p n x ∈ tildeDom p)
    (hy : phiNeg p n y ∈ tildeDom p) : iotaN p n (x + y) = iotaN p n x + iotaN p n y := by
  rw [iotaN, iotaN, iotaN, map_add, iotaTildeFun_add hx hy]

theorem iotaN_mul {n : ℕ} {x y : (𝓣).RobbaTilde} (hx : phiNeg p n x ∈ tildeDom p)
    (hy : phiNeg p n y ∈ tildeDom p) : iotaN p n (x * y) = iotaN p n x * iotaN p n y := by
  rw [iotaN, iotaN, iotaN, map_mul, iotaTildeFun_mul hx hy]

theorem thetaN_add {n : ℕ} {x y : (𝓣).RobbaTilde} (hx : phiNeg p n x ∈ tildeDom p)
    (hy : phiNeg p n y ∈ tildeDom p) : thetaN p n (x + y) = thetaN p n x + thetaN p n y := by
  rw [thetaN, iotaN_add hx hy, map_add]; rfl

theorem thetaN_mul {n : ℕ} {x y : (𝓣).RobbaTilde} (hx : phiNeg p n x ∈ tildeDom p)
    (hy : phiNeg p n y ∈ tildeDom p) : thetaN p n (x * y) = thetaN p n x * thetaN p n y := by
  rw [thetaN, iotaN_mul hx hy, map_mul]; rfl

theorem iotaN_add_one_tildeFrob (n : ℕ) (x : (𝓣).RobbaTilde) :
    iotaN p (n + 1) ((frob ℂ_[p] p).tildeFrob x) = iotaN p n x := by
  rw [iotaN, iotaN, phiNeg_succ_tildeFrob]

theorem thetaN_add_one_tildeFrob (n : ℕ) (x : (𝓣).RobbaTilde) :
    thetaN p (n + 1) ((frob ℂ_[p] p).tildeFrob x) = thetaN p n x := by
  rw [thetaN, thetaN, iotaN_add_one_tildeFrob]

section GaloisN

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem galIso_tildeMap_tildeFrobSymm (σ : Gal(PadicAlgCl p/K)) (x : (𝓣).RobbaTilde) :
    (galIso σ).tildeMap ((frob ℂ_[p] p).tildeFrobSymm x) =
      (frob ℂ_[p] p).tildeFrobSymm ((galIso σ).tildeMap x) := by
  have hinj : Function.Injective (frob ℂ_[p] p).tildeFrob :=
    Function.LeftInverse.injective (frob ℂ_[p] p).tildeFrobSymm_tildeFrob
  apply hinj
  rw [← galIso_tildeMap_tildeFrob, TeichLift.TeichFrob.tildeFrob_tildeFrobSymm,
    TeichLift.TeichFrob.tildeFrob_tildeFrobSymm]

theorem galIso_tildeMap_phiNeg (σ : Gal(PadicAlgCl p/K)) (n : ℕ) (x : (𝓣).RobbaTilde) :
    (galIso σ).tildeMap (phiNeg p n x) = phiNeg p n ((galIso σ).tildeMap x) := by
  induction n with
  | zero => rw [phiNeg_apply, phiNeg_apply]; rfl
  | succ k ih => rw [phiNeg_succ, phiNeg_succ, galIso_tildeMap_tildeFrobSymm, ih]

theorem tildeMap_mem_tildeDom (σ : Gal(PadicAlgCl p/K)) {x : (𝓣).RobbaTilde}
    (hx : x ∈ tildeDom p) : (galIso σ).tildeMap x ∈ tildeDom p := by
  obtain ⟨ρ, hρ, y, rfl⟩ := hx
  rw [TeichLift.TeichIso.tildeMap_ofRad]
  exact ⟨ρ, hρ, _, rfl⟩

theorem iotaTildeFun_tildeMap (σ : Gal(PadicAlgCl p/K)) {x : (𝓣).RobbaTilde}
    (hx : x ∈ tildeDom p) : iotaTildeFun p ((galIso σ).tildeMap x) = σ • iotaTildeFun p x := by
  obtain ⟨ρ, hρ, y, rfl⟩ := hx
  rw [TeichLift.TeichIso.tildeMap_ofRad, iotaTildeFun_ofRad hρ, iotaTildeFun_ofRad hρ,
    iota_extMap hρ]

theorem iotaN_tildeMap (σ : Gal(PadicAlgCl p/K)) {n : ℕ} {x : (𝓣).RobbaTilde}
    (hx : phiNeg p n x ∈ tildeDom p) :
    iotaN p n ((galIso σ).tildeMap x) = σ • iotaN p n x := by
  rw [iotaN, ← galIso_tildeMap_phiNeg, iotaTildeFun_tildeMap σ hx]
  rfl

end GaloisN

end WAEval

end GroundTheory.PAdicHodge
