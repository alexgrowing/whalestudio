import Mathlib
import GroundTheory.PAdicHodge.WAEval
import GroundTheory.PAdicHodge.WACommonKappa
import GroundTheory.PAdicHodge.BdRTGalois
import GroundTheory.PAdicHodge.BCrisPlusInvariants
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WAPeriodT

open _root_.WittVector WittTilt PhiGamma TeichLift UniformSpace Laurent WAEval Filter Topology

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝓣" => teichLift ℂ_[p] p
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p
local notation "𝔸" => Localization.Away (p : AInf ℂ_[p] p)
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔪" => IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[p]) p)

theorem extNorm_pow' {ρ : Set.Ioo (0 : ℝ) 1} (σ : Set.Ioc (0 : ℝ) ρ) (x : (𝓣).RobbaExt ρ) (n : ℕ) :
    (𝓣).extNorm ρ σ (x ^ n) = (𝓣).extNorm ρ σ x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, (𝓣).extNorm_one]
  | succ n ih => rw [pow_succ, pow_succ, (𝓣).extNorm_mul, ih]

theorem extNorm_awayToExt_algebraMap_le' (ρ : Set.Ioo (0 : ℝ) 1) (σ : Set.Ioc (0 : ℝ) ρ)
    (y : AInf ℂ_[p] p) : (𝓣).extNorm ρ σ (awayToExt p ρ (algebraMap _ 𝔸 y)) ≤ 1 := by
  rw [awayToExt_apply, extNorm_coe]
  show gaussNorm ((𝓣).coeffB (toB ℂ_[p] p (algebraMap _ 𝔸 y))) σ ≤ 1
  rw [toB_algebraMap, coeffB_algebraMap]
  exact (𝓣).gaussNorm_le_one_of_mem_int (incl_mem_int y) (rad_pos ρ σ) (rad_lt_one ρ σ).le

theorem extNorm_natCast_p' (ρ : Set.Ioo (0 : ℝ) 1) (σ : Set.Ioc (0 : ℝ) ρ) :
    (𝓣).extNorm ρ σ (p : (𝓣).RobbaExt ρ) = σ := by
  rw [← awayToExt_natCast, awayToExt_apply, extNorm_coe]
  show gaussNorm ((𝓣).coeffB (toB ℂ_[p] p (algebraMap _ 𝔸 (p : AInf ℂ_[p] p)))) σ = _
  rw [toB_algebraMap, coeffB_algebraMap, map_natCast (incl ℂ_[p] p)]
  exact (𝓣).gaussNorm_π (rad_pos ρ σ)

theorem extNorm_awayToExt_invSelf (ρ : Set.Ioo (0 : ℝ) 1) (σ : Set.Ioc (0 : ℝ) ρ) :
    (𝓣).extNorm ρ σ (awayToExt p ρ (IsLocalization.Away.invSelf (p : AInf ℂ_[p] p))) = (σ : ℝ)⁻¹ := by
  have h : (𝓣).extNorm ρ σ (p : (𝓣).RobbaExt ρ) *
      (𝓣).extNorm ρ σ (awayToExt p ρ (IsLocalization.Away.invSelf (p : AInf ℂ_[p] p))) = 1 := by
    rw [← (𝓣).extNorm_mul, ← awayToExt_natCast, ← map_mul, IsLocalization.Away.mul_invSelf, map_one,
      (𝓣).extNorm_one]
  rw [extNorm_natCast_p'] at h
  exact eq_inv_of_mul_eq_one_right h

variable (p) in

def unitInv (n : ℕ) : ℤ_[p] := ((n / p ^ n.factorization p : ℕ) : ℤ_[p]).inv

theorem natCast_mul_unitInv {n : ℕ} (hn : n ≠ 0) :
    ((n / p ^ n.factorization p : ℕ) : ℤ_[p]) * unitInv p n = 1 :=
  PadicInt.mul_inv (PadicInt.norm_natCast_eq_one_iff.2 (Nat.coprime_ordCompl hp.out hn))

variable (p) in

def logCoeff (n : ℕ) : 𝔸 :=
  (-1) ^ (n + 1) * algebraMap (AInf ℂ_[p] p) 𝔸 (IsPerfectoidField.padicIntToWitt p (unitInv p n)) *
    IsLocalization.Away.invSelf (p : AInf ℂ_[p] p) ^ n.factorization p

theorem natCast_mul_logCoeff {n : ℕ} (hn : n ≠ 0) : (n : 𝔸) * logCoeff p n = (-1) ^ (n + 1) := by
  set X := algebraMap (AInf ℂ_[p] p) 𝔸
    (IsPerfectoidField.padicIntToWitt p ((n / p ^ n.factorization p : ℕ) : ℤ_[p])) with hX
  set Y := algebraMap (AInf ℂ_[p] p) 𝔸 (IsPerfectoidField.padicIntToWitt p (unitInv p n)) with hY
  set P := algebraMap (AInf ℂ_[p] p) 𝔸 (p : AInf ℂ_[p] p) with hP
  set I := IsLocalization.Away.invSelf (S := 𝔸) (p : AInf ℂ_[p] p) with hI
  have e1 : (n : 𝔸) = P ^ n.factorization p * X := by
    rw [hP, hX, map_natCast, map_natCast, map_natCast, ← Nat.cast_pow, ← Nat.cast_mul,
      Nat.ordProj_mul_ordCompl_eq_self]
  have e2 : X * Y = 1 := by
    rw [hX, hY, ← map_mul, ← map_mul, natCast_mul_unitInv hn, map_one, map_one]
  have e3 : P ^ n.factorization p * I ^ n.factorization p = 1 := by
    rw [← mul_pow, hP, hI, IsLocalization.Away.mul_invSelf (S := 𝔸) (p : AInf ℂ_[p] p), one_pow]
  rw [e1, logCoeff, ← hY, ← hI]
  linear_combination (-1 : 𝔸) ^ (n + 1) * (X * Y) * e3 + (-1 : 𝔸) ^ (n + 1) * e2

theorem map_logCoeff (f : 𝔸 →+* 𝔹) {n : ℕ} (hn : n ≠ 0) :
    f (logCoeff p n) = algebraMap ℚ 𝔹 ((-1) ^ (n + 1) / n) := by
  have h := congrArg f (natCast_mul_logCoeff (p := p) hn)
  rw [map_mul, map_natCast, map_pow, map_neg, map_one] at h
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hu : IsUnit (n : 𝔹) := by
    have := (isUnit_iff_ne_zero.2 hn').map (algebraMap ℚ 𝔹)
    rwa [map_natCast] at this
  apply hu.mul_left_cancel
  rw [h, ← map_natCast (algebraMap ℚ 𝔹), ← map_mul, mul_div_cancel₀ _ hn', map_pow, map_neg, map_one]

theorem extNorm_awayToExt_logCoeff_le (ρ : Set.Ioo (0 : ℝ) 1) (σ : Set.Ioc (0 : ℝ) ρ) (n : ℕ) :
    (𝓣).extNorm ρ σ (awayToExt p ρ (logCoeff p n)) ≤ (σ : ℝ)⁻¹ ^ n.factorization p := by
  rw [logCoeff, map_mul, map_mul, map_pow, map_pow, map_neg, map_one, (𝓣).extNorm_mul,
    (𝓣).extNorm_mul, extNorm_pow', extNorm_pow', (𝓣).extNorm_neg, (𝓣).extNorm_one, one_pow, one_mul,
    extNorm_awayToExt_invSelf]
  exact mul_le_of_le_one_left (by have := rad_pos ρ σ; positivity)
    (extNorm_awayToExt_algebraMap_le' ρ σ _)

theorem tendsto_inv_pow_factorization_mul_pow {σ a : ℝ} (hσ0 : 0 < σ) (ha0 : 0 < a) (ha : a < 1)
    (k : ℕ) : Tendsto (fun N : ℕ => σ⁻¹ ^ (N + k).factorization p * a ^ N) atTop (𝓝 0) := by
  have hp1 : (1 : ℝ) < p := Nat.one_lt_cast.2 hp.out.one_lt
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt σ⁻¹ hp1
  have hg := (tendsto_pow_const_mul_const_pow_of_abs_lt_one K
    (show |a| < 1 by rw [abs_of_pos ha0]; exact ha)).comp (tendsto_add_atTop_nat (k + 1))
  have hg2 := hg.div_const (a ^ (k + 1))
  rw [zero_div] at hg2
  refine squeeze_zero (fun N => by positivity) (fun N => ?_) hg2
  simp only [Function.comp_apply]
  have hak : 0 < a ^ (k + 1) := pow_pos ha0 _
  rw [pow_add, ← mul_assoc, mul_div_assoc, div_self hak.ne', mul_one]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg ha0.le N)
  have hle : ((p ^ (N + k).factorization p : ℕ) : ℝ) ≤ ((N + (k + 1) : ℕ) : ℝ) := by
    refine Nat.cast_le.2 ?_
    by_cases h0 : N + k = 0
    · rw [h0, Nat.factorization_zero, Finsupp.zero_apply, pow_zero]; omega
    · exact (Nat.ordProj_le p h0).trans (by omega)
  calc σ⁻¹ ^ (N + k).factorization p ≤ ((p : ℝ) ^ K) ^ (N + k).factorization p :=
        pow_le_pow_left₀ (by positivity) hK.le _
    _ = ((p ^ (N + k).factorization p : ℕ) : ℝ) ^ K := by push_cast; rw [← pow_mul, ← pow_mul, mul_comm]
    _ ≤ ((N + (k + 1) : ℕ) : ℝ) ^ K := pow_le_pow_left₀ (by positivity) hle K

variable (p) in

def logPSum (z : 𝔸) (k N : ℕ) : 𝔸 := ∑ n ∈ Finset.range N, logCoeff p (n + k) * z ^ n

variable (p) in

def logTail (ρ : Set.Ioo (0 : ℝ) 1) (z : 𝔸) (k : ℕ) : (𝓣).RobbaExt ρ :=
  limUnder atTop fun N => awayToExt p ρ (logPSum p z k N)

section Series

theorem cauchySeq_logPSum {ρ : Set.Ioo (0 : ℝ) 1} {z : 𝔸} {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hz : ∀ σ : Set.Ioc (0 : ℝ) ρ, (𝓣).extNorm ρ σ (awayToExt p ρ z) ≤ a) (k : ℕ) :
    CauchySeq fun N => awayToExt p ρ (logPSum p z k N) := by
  refine (𝓣).cauchySeq_of_increments fun σ => ?_
  have hbd : ∀ N, (𝓣).extNorm ρ σ (awayToExt p ρ (logPSum p z k (N + 1)) -
      awayToExt p ρ (logPSum p z k N)) ≤ (σ : ℝ)⁻¹ ^ (N + k).factorization p * a ^ N := by
    intro N
    rw [← map_sub, logPSum, logPSum, Finset.sum_range_succ, add_sub_cancel_left, map_mul,
      (𝓣).extNorm_mul, map_pow, extNorm_pow']
    exact mul_le_mul (extNorm_awayToExt_logCoeff_le ρ σ (N + k))
      (pow_le_pow_left₀ ((𝓣).extNorm_nonneg σ _) (hz σ) N) (pow_nonneg ((𝓣).extNorm_nonneg σ _) N)
      (by have := rad_pos ρ σ; positivity)
  exact squeeze_zero (fun N => (𝓣).extNorm_nonneg σ _) hbd
    (tendsto_inv_pow_factorization_mul_pow (rad_pos ρ σ) ha0 ha1 k)

theorem tendsto_logTail {ρ : Set.Ioo (0 : ℝ) 1} {z : 𝔸} {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hz : ∀ σ : Set.Ioc (0 : ℝ) ρ, (𝓣).extNorm ρ σ (awayToExt p ρ z) ≤ a) (k : ℕ) :
    Tendsto (fun N => awayToExt p ρ (logPSum p z k N)) atTop (𝓝 (logTail p ρ z k)) :=
  (cauchySeq_logPSum ha0 ha1 hz k).tendsto_limUnder

theorem logPSum_succ (z : 𝔸) (k N : ℕ) :
    logPSum p z k (N + 1) = logCoeff p k + z * logPSum p z (k + 1) N := by
  rw [logPSum, Finset.sum_range_succ', logPSum, Finset.mul_sum, add_comm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [show i + 1 + k = i + (k + 1) by omega, pow_succ]
    ring

theorem logTail_succ {ρ : Set.Ioo (0 : ℝ) 1} {z : 𝔸} {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hz : ∀ σ : Set.Ioc (0 : ℝ) ρ, (𝓣).extNorm ρ σ (awayToExt p ρ z) ≤ a) (k : ℕ) :
    logTail p ρ z k = awayToExt p ρ (logCoeff p k) + awayToExt p ρ z * logTail p ρ z (k + 1) := by
  have h1 := (tendsto_logTail ha0 ha1 hz k).comp (tendsto_add_atTop_nat 1)
  have h2 := (tendsto_const_nhds (x := awayToExt p ρ (logCoeff p k))).add
    ((tendsto_const_nhds (x := awayToExt p ρ z)).mul (tendsto_logTail ha0 ha1 hz (k + 1)))
  refine tendsto_nhds_unique h1 (h2.congr fun N => ?_)
  simp only [Function.comp_apply, logPSum_succ, map_add, map_mul]

theorem res_logTail {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} {z : 𝔸} (h : (ρ1 : ℝ) ≤ ρ0) {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hz : ∀ σ : Set.Ioc (0 : ℝ) ρ0, (𝓣).extNorm ρ0 σ (awayToExt p ρ0 z) ≤ a)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hz' : ∀ σ : Set.Ioc (0 : ℝ) ρ1, (𝓣).extNorm ρ1 σ (awayToExt p ρ1 z) ≤ b) (k : ℕ) :
    (𝓣).res h (logTail p ρ0 z k) = logTail p ρ1 z k := by
  have h1 := (((𝓣).continuous_res h).tendsto _).comp (tendsto_logTail ha0 ha1 hz k)
  refine tendsto_nhds_unique (h1.congr fun N => ?_) (tendsto_logTail hb0 hb1 hz' k)
  simp only [Function.comp_apply, res_awayToExt]

theorem logTail_eq_sum {ρ : Set.Ioo (0 : ℝ) 1} {z : 𝔸} {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hz : ∀ σ : Set.Ioc (0 : ℝ) ρ, (𝓣).extNorm ρ σ (awayToExt p ρ z) ≤ a) (m : ℕ) :
    awayToExt p ρ z * logTail p ρ z 1 =
      awayToExt p ρ (∑ i ∈ Finset.range m, logCoeff p (i + 1) * z ^ (i + 1)) +
        awayToExt p ρ z ^ (m + 1) * logTail p ρ z (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ih, logTail_succ ha0 ha1 hz (m + 1), Finset.sum_range_succ, map_add, map_mul, map_pow]
    ring

end Series

variable (p) in

def muA (ε : 𝒪♭) : 𝔸 := algebraMap (AInf ℂ_[p] p) 𝔸 (AInf.mu ε)

theorem norm_sub_one_lt_one {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) : ‖ε - 1‖ < 1 := by
  have h := AInf.norm_sub_one_pow (K := ℂ_[p]) hε hζ
  have hp1 : p - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hp.out.one_lt
  by_contra hge
  push Not at hge
  have h1 : 1 ≤ ‖ε - 1‖ ^ (p - 1) := one_le_pow₀ hge
  have h2 : ‖(p : ℂ_[p])‖ ^ p < 1 :=
    pow_lt_one₀ (norm_nonneg _) (by rw [norm_natCast_p]; exact inv_p_lt_one) hp.out.ne_zero
  linarith

theorem extNorm_muA_le (ε : 𝒪♭) (ρ : Set.Ioo (0 : ℝ) 1) (σ : Set.Ioc (0 : ℝ) ρ) :
    (𝓣).extNorm ρ σ (awayToExt p ρ (muA p ε)) ≤ max ‖ε - 1‖ σ := by
  rw [muA, awayToExt_apply, extNorm_coe]
  show gaussNorm ((𝓣).coeffB (toB ℂ_[p] p (algebraMap _ 𝔸 (AInf.mu ε)))) σ ≤ _
  rw [toB_algebraMap, coeffB_algebraMap]
  have hσ0 := rad_pos ρ σ
  have hσ1 := rad_lt_one ρ σ
  refine gaussNorm_le fun n => ?_
  rcases lt_or_ge n 0 with hn | hn
  · rw [(𝓣).zcoeff_of_neg _ hn, norm_zero, zero_mul]; positivity
  · lift n to ℕ using hn
    rw [zcoeff_natCast, zpow_natCast]
    rcases n with _ | n
    · have h0 : (AInf.mu ε).coeff 0 = ε - 1 := by
        rw [AInf.mu, ← WittVector.constantCoeff_apply, map_sub, map_one, WittVector.constantCoeff_apply,
          WittVector.teichmuller_coeff_zero]
      rw [pow_zero, mul_one, coeff_zero, teichLift_red, incl_coeff, h0, norm_algebraMap_preTilt]
      exact le_max_left _ _
    · refine le_trans ?_ (le_max_right _ _)
      calc ‖(𝓣).coeff (incl ℂ_[p] p (AInf.mu ε)) (n + 1)‖ * (σ : ℝ) ^ (n + 1) ≤ 1 * (σ : ℝ) ^ 1 :=
            mul_le_mul ((𝓣).mem_int_iff.1 (incl_mem_int _) _)
              (pow_le_pow_of_le_one hσ0.le hσ1.le (by omega)) (by positivity) zero_le_one
        _ = σ := by rw [one_mul, pow_one]

theorem muBound_lt_one {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) (ρ : Set.Ioo (0 : ℝ) 1) :
    max ‖ε - 1‖ (ρ : ℝ) < 1 :=
  max_lt (norm_sub_one_lt_one hε hζ) ρ.2.2

theorem muBound_pos (ε : 𝒪♭) (ρ : Set.Ioo (0 : ℝ) 1) : 0 < max ‖ε - 1‖ (ρ : ℝ) :=
  lt_max_of_lt_right ρ.2.1

theorem extNorm_muA_le_bound (ε : 𝒪♭) (ρ : Set.Ioo (0 : ℝ) 1) (σ : Set.Ioc (0 : ℝ) ρ) :
    (𝓣).extNorm ρ σ (awayToExt p ρ (muA p ε)) ≤ max ‖ε - 1‖ (ρ : ℝ) :=
  (extNorm_muA_le ε ρ σ).trans (max_le_max le_rfl σ.2.2)

variable (p) in

def tTildeExt (ε : 𝒪♭) (ρ : Set.Ioo (0 : ℝ) 1) : (𝓣).RobbaExt ρ :=
  awayToExt p ρ (muA p ε) * logTail p ρ (muA p ε) 1

variable (p) in

def tTilde (ε : 𝒪♭) : (𝓣).RobbaTilde := (𝓣).ofRad (rhoMid p) (tTildeExt p ε (rhoMid p))

theorem logOnePlus_congr {w w' : 𝔹} (h : w = w') (hw : w ∈ 𝔪) (hw' : w' ∈ 𝔪) :
    logOnePlus 𝔪 w hw = logOnePlus 𝔪 w' hw' := by
  subst h; rfl

theorem toBDeRhamPlus_muA (ε : 𝒪♭) : toBDeRhamPlus (normInteger ℂ_[p]) p (muA p ε) = muBdR p ε :=
  rfl

theorem one_add_pow_sub_one_mem {w : 𝔹} (hw : w ∈ 𝔪) (k : ℕ) : (1 + w) ^ k - 1 ∈ 𝔪 := by
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (1 + w) 1 k
  rw [one_pow] at hc
  rw [hc, add_sub_cancel_left]
  exact Ideal.mul_mem_right _ _ hw

theorem toB_phiAway (a : 𝔸) :
    toB ℂ_[p] p (ACris.phiAway ℂ_[p] p a) = (frob ℂ_[p] p).toB (toB ℂ_[p] p a) := by
  have : (toB ℂ_[p] p).comp (ACris.phiAway ℂ_[p] p) =
      ((frob ℂ_[p] p).toB : (𝓣).B →+* (𝓣).B).comp (toB ℂ_[p] p) :=
    IsLocalization.ringHom_ext (Submonoid.powers (p : AInf ℂ_[p] p)) (RingHom.ext fun y => by
      simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
      rw [ACris.phiAway_algebraMap, toB_algebraMap, toB_algebraMap,
        TeichLift.TeichFrob.toB_algebraMap, frob_φ_incl])
  exact RingHom.congr_fun this a

theorem extFrob_awayToExt (ρ : Set.Ioo (0 : ℝ) 1) (a : 𝔸) :
    (frob ℂ_[p] p).extFrob ρ (awayToExt p ρ a) =
      awayToExt p ((frob ℂ_[p] p).powRadius ρ) (ACris.phiAway ℂ_[p] p a) := by
  rw [awayToExt_apply, TeichLift.TeichFrob.extFrob_coe, awayToExt_apply]
  congr 1
  exact Subtype.ext (by rw [TeichLift.TeichFrob.coe_econFrob]; exact (toB_phiAway a).symm)

theorem toBDeRhamPlus_phiAway_muA (ε : 𝒪♭) :
    toBDeRhamPlus (normInteger ℂ_[p]) p (ACris.phiAway ℂ_[p] p (muA p ε)) = (1 + muBdR p ε) ^ p - 1 := by
  rw [muA, ACris.phiAway_algebraMap, AInf.mu, map_sub, map_one, WittVector.frobeniusEquiv_teichmuller,
    map_pow, muBdR_eq]
  show wittToBDeRhamPlus (normInteger ℂ_[p]) p (teichmuller p ε ^ p - 1) = _
  rw [map_sub, map_pow, map_one]
  ring

theorem padicToTilde_eq_ofRad (q : ℚ_[p]) (ρ : Set.Ioo (0 : ℝ) 1) :
    padicToTilde p q = (𝓣).ofRad ρ (awayToExt p ρ (wittFpbarToAway p (padicToWFrac p q))) := by
  rw [padicToTilde, RingHom.comp_apply, wittFpbarToTilde_eq_tildeOf, TeichLift.tildeOf_eq _ _ ρ,
    awayToExt_eq_ofAll]
  congr 1
  exact (𝓣).ofAll_congr _ _ (toB_wittFpbarToAway _).symm ρ

theorem iota_awayToExt_padic {ρ : Set.Ioo (0 : ℝ) 1} (hρ : (p : ℝ)⁻¹ < ρ) (q : ℚ_[p]) :
    iota p hρ (awayToExt p ρ (wittFpbarToAway p (padicToWFrac p q))) = algebraMap ℚ_[p] 𝔹 q := by
  rw [iota_awayToExt, toBDeRhamPlus_wittFpbarToAway, wittFpbarToBCrisPlus_padicToWFrac,
    ACris.iotaPlus_algebraMap_padic]

section TTilde

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)
include hε hζ

theorem tendsto_tTildeExt (ρ : Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun N => awayToExt p ρ (∑ i ∈ Finset.range N, logCoeff p (i + 1) * muA p ε ^ (i + 1)))
      atTop (𝓝 (tTildeExt p ε ρ)) := by
  have h := (tendsto_const_nhds (x := awayToExt p ρ (muA p ε))).mul
    (tendsto_logTail (muBound_pos ε ρ) (muBound_lt_one hε hζ ρ) (extNorm_muA_le_bound ε ρ) 1)
  refine h.congr fun N => ?_
  rw [← map_mul, logPSum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_succ]
  ring

theorem tTildeExt_eq_sum (ρ : Set.Ioo (0 : ℝ) 1) (m : ℕ) :
    tTildeExt p ε ρ = awayToExt p ρ (∑ i ∈ Finset.range m, logCoeff p (i + 1) * muA p ε ^ (i + 1)) +
      awayToExt p ρ (muA p ε) ^ (m + 1) * logTail p ρ (muA p ε) (m + 1) :=
  logTail_eq_sum (muBound_pos ε ρ) (muBound_lt_one hε hζ ρ) (extNorm_muA_le_bound ε ρ) m

theorem res_tTildeExt {ρ0 ρ1 : Set.Ioo (0 : ℝ) 1} (h : (ρ1 : ℝ) ≤ ρ0) :
    (𝓣).res h (tTildeExt p ε ρ0) = tTildeExt p ε ρ1 := by
  rw [tTildeExt, map_mul, res_awayToExt, res_logTail h (muBound_pos ε ρ0) (muBound_lt_one hε hζ ρ0)
    (extNorm_muA_le_bound ε ρ0) (muBound_pos ε ρ1) (muBound_lt_one hε hζ ρ1)
    (extNorm_muA_le_bound ε ρ1)]
  rfl

theorem ofRad_tTildeExt (ρ : Set.Ioo (0 : ℝ) 1) : (𝓣).ofRad ρ (tTildeExt p ε ρ) = tTilde p ε := by
  let ρ3 : Set.Ioo (0 : ℝ) 1 := ⟨min ρ (rhoMid p), lt_min ρ.2.1 (rhoMid p).2.1,
    min_lt_of_left_lt ρ.2.2⟩
  rw [tTilde, ← (𝓣).ofRad_res (ρ1 := ρ3) (min_le_left _ _), ← (𝓣).ofRad_res (ρ1 := ρ3) (min_le_right _ _),
    res_tTildeExt hε hζ, res_tTildeExt hε hζ]

theorem map_tTildeExt (ρ : Set.Ioo (0 : ℝ) 1) (g : (𝓣).RobbaExt ρ →+* 𝔹) (ψ : 𝔸 →+* 𝔸)
    (hg : ∀ a, g (awayToExt p ρ a) = toBDeRhamPlus (normInteger ℂ_[p]) p (ψ a))
    (hw : toBDeRhamPlus (normInteger ℂ_[p]) p (ψ (muA p ε)) ∈ 𝔪) :
    g (tTildeExt p ε ρ) = logOnePlus 𝔪 _ hw := by
  set w := toBDeRhamPlus (normInteger ℂ_[p]) p (ψ (muA p ε)) with hwdef
  rw [← sub_eq_zero]
  refine IsPerfectoidField.eq_zero_of_forall_mem_maximalIdeal_pow fun n => ?_
  refine Ideal.pow_le_pow_right (Nat.le_succ n) ?_
  have hsum : g (awayToExt p ρ (∑ i ∈ Finset.range n, logCoeff p (i + 1) * muA p ε ^ (i + 1))) =
      ∑ i ∈ Finset.Ico 1 (n + 1), algebraMap ℚ 𝔹 ((-1) ^ (i + 1) / i) * w ^ i := by
    rw [hg, map_sum, map_sum, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, map_pow, map_pow, ← RingHom.comp_apply (toBDeRhamPlus (normInteger ℂ_[p]) p) ψ,
      map_logCoeff _ (Nat.succ_ne_zero i), add_comm 1 i]
  have h1 := logOnePlus_sub_sum_mem hw (n + 1)
  have h2 : g (awayToExt p ρ (muA p ε)) ^ (n + 1) * g (logTail p ρ (muA p ε) (n + 1)) ∈ 𝔪 ^ (n + 1) := by
    rw [hg]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hw _)
  have e : g (tTildeExt p ε ρ) - logOnePlus 𝔪 w hw =
      g (awayToExt p ρ (muA p ε)) ^ (n + 1) * g (logTail p ρ (muA p ε) (n + 1)) -
        (logOnePlus 𝔪 w hw - ∑ i ∈ Finset.Ico 1 (n + 1), algebraMap ℚ 𝔹 ((-1) ^ (i + 1) / i) * w ^ i) := by
    rw [tTildeExt_eq_sum hε hζ ρ n, map_add, map_mul, map_pow, hsum]
    ring
  rw [e]
  exact sub_mem h2 h1

theorem iota_tTildeExt {ρ : Set.Ioo (0 : ℝ) 1} (hρ : (p : ℝ)⁻¹ < ρ) :
    iota p hρ (tTildeExt p ε ρ) = fontaineT ε hε := by
  have hw : toBDeRhamPlus (normInteger ℂ_[p]) p ((RingHom.id 𝔸) (muA p ε)) ∈ 𝔪 :=
    muBdR_mem hε
  rw [map_tTildeExt hε hζ ρ (iota p hρ) (RingHom.id 𝔸) (fun a => iota_awayToExt hρ a) hw]
  rfl

theorem tTildeExt_ne_zero (ρ : Set.Ioo (0 : ℝ) 1) : tTildeExt p ε ρ ≠ 0 := by
  intro h
  have h1 := iota_tTildeExt hε hζ (ρ := rhoMid p) inv_p_lt_rhoMid
  have h2 : tTildeExt p ε (rhoMid p) = 0 := by
    apply (𝓣).ofRad_injective (rhoMid p)
    rw [ofRad_tTildeExt hε hζ, ← ofRad_tTildeExt hε hζ ρ, h, map_zero, map_zero]
  rw [h2, map_zero] at h1
  exact fontaineT_ne_zero hε hζ h1.symm

theorem tTilde_ne_zero : tTilde p ε ≠ 0 := by
  rw [← ofRad_tTildeExt hε hζ (rhoMid p)]
  exact fun h => tTildeExt_ne_zero hε hζ (rhoMid p)
    ((𝓣).ofRad_injective _ (by rw [h, map_zero]))

theorem tTilde_mem_tildeDom : tTilde p ε ∈ tildeDom p :=
  ⟨rhoMid p, inv_p_lt_rhoMid, _, ofRad_tTildeExt hε hζ (rhoMid p)⟩

theorem iotaTildeFun_tTilde : iotaTildeFun p (tTilde p ε) = fontaineT ε hε := by
  rw [← ofRad_tTildeExt hε hζ (rhoMid p), iotaTildeFun_ofRad inv_p_lt_rhoMid, iota_tTildeExt hε hζ]

theorem iota_extFrob_tTildeExt {ρ : Set.Ioo (0 : ℝ) 1}
    (hρ : (p : ℝ)⁻¹ < ((frob ℂ_[p] p).powRadius ρ : ℝ)) :
    iota p hρ ((frob ℂ_[p] p).extFrob ρ (tTildeExt p ε ρ)) = p * fontaineT ε hε := by
  have hk := one_add_pow_sub_one_mem (muBdR_mem hε) p
  have hw : toBDeRhamPlus (normInteger ℂ_[p]) p (ACris.phiAway ℂ_[p] p (muA p ε)) ∈ 𝔪 := by
    rw [toBDeRhamPlus_phiAway_muA]; exact hk
  have h := map_tTildeExt hε hζ ρ ((iota p hρ).comp ((frob ℂ_[p] p).extFrob ρ)) (ACris.phiAway ℂ_[p] p)
    (fun a => by rw [RingHom.comp_apply, extFrob_awayToExt, iota_awayToExt]) hw
  rw [RingHom.comp_apply] at h
  rw [h, logOnePlus_congr (toBDeRhamPlus_phiAway_muA ε) hw hk, logOnePlus_pow (muBdR_mem hε) p hk]
  rfl

theorem tildeFrob_tTilde : (frob ℂ_[p] p).tildeFrob (tTilde p ε) = p * tTilde p ε := by
  set ρ := (frob ℂ_[p] p).rootRadius (rhoMid p) with hρdef
  have hρ : (p : ℝ)⁻¹ < ((frob ℂ_[p] p).powRadius ρ : ℝ) := by
    rw [hρdef, (frob ℂ_[p] p).powRadius_rootRadius]; exact inv_p_lt_rhoMid
  have h : (frob ℂ_[p] p).extFrob ρ (tTildeExt p ε ρ) =
      p * tTildeExt p ε ((frob ℂ_[p] p).powRadius ρ) := by
    apply iota_injective hρ
    rw [iota_extFrob_tTildeExt hε hζ hρ, map_mul, map_natCast, iota_tTildeExt hε hζ hρ]
  rw [← ofRad_tTildeExt hε hζ ρ, TeichLift.TeichFrob.tildeFrob_ofRad, h, map_mul, map_natCast,
    ofRad_tTildeExt hε hζ, ofRad_tTildeExt hε hζ]

theorem extFrob_tTildeExt (ρ : Set.Ioo (0 : ℝ) 1) :
    (frob ℂ_[p] p).extFrob ρ (tTildeExt p ε ρ) = p * tTildeExt p ε ((frob ℂ_[p] p).powRadius ρ) := by
  apply (𝓣).ofRad_injective
  rw [← TeichLift.TeichFrob.tildeFrob_ofRad, ofRad_tTildeExt hε hζ, tildeFrob_tTilde hε hζ, map_mul,
    map_natCast, ofRad_tTildeExt hε hζ]

theorem natCast_mul_tildeFrobSymm_tTilde :
    (p : (𝓣).RobbaTilde) * (frob ℂ_[p] p).tildeFrobSymm (tTilde p ε) = tTilde p ε := by
  have h := congrArg (frob ℂ_[p] p).tildeFrobSymm (tildeFrob_tTilde hε hζ)
  rw [TeichLift.TeichFrob.tildeFrobSymm_tildeFrob, map_mul, map_natCast] at h
  exact h.symm

theorem pow_mul_phiNeg_tTilde (n : ℕ) :
    (p : (𝓣).RobbaTilde) ^ n * phiNeg p n (tTilde p ε) = tTilde p ε := by
  induction n with
  | zero => simp [phiNeg_apply]
  | succ n ih =>
    have h1 := congrArg (frob ℂ_[p] p).tildeFrobSymm ih
    rw [map_mul, map_pow, map_natCast] at h1
    rw [phiNeg_succ, pow_succ, mul_comm ((p : (𝓣).RobbaTilde) ^ n) p, mul_assoc, h1,
      natCast_mul_tildeFrobSymm_tTilde hε hζ]

theorem phiNeg_tTilde_mem (n : ℕ) : phiNeg p n (tTilde p ε) ∈ tildeDom p := by
  induction n with
  | zero => simpa [phiNeg_apply] using tTilde_mem_tildeDom hε hζ
  | succ n ih => rw [phiNeg_succ]; exact tildeFrobSymm_mem_tildeDom ih

theorem pow_mul_iotaN_tTilde (n : ℕ) : (p : 𝔹) ^ n * iotaN p n (tTilde p ε) = fontaineT ε hε := by
  have hm := phiNeg_tTilde_mem hε hζ n
  have hpn : ((p : (𝓣).RobbaTilde) ^ n) ∈ tildeDom p :=
    pow_mem (natCast_mem _ p) n
  have h := iotaTildeFun_mul hpn hm
  rw [pow_mul_phiNeg_tTilde hε hζ n, iotaTildeFun_tTilde hε hζ] at h
  have e : iotaTildeFun p ((p : (𝓣).RobbaTilde) ^ n) = (p : 𝔹) ^ n := by
    have := map_pow (iotaTilde p) (p : tildeDom p) n
    rw [map_natCast, iotaTilde_apply] at this
    simpa using this
  rw [iotaN, ← e, ← h]

theorem thetaN_tTilde (n : ℕ) : thetaN p n (tTilde p ε) = 0 := by
  have h := congrArg (IsPerfectoidField.thetaBDeRhamPlusField p) (pow_mul_iotaN_tTilde hε hζ n)
  rw [map_mul, map_pow, map_natCast] at h
  have h0 : IsPerfectoidField.thetaBDeRhamPlusField p (fontaineT ε hε) = 0 := by
    have := fontaineT_mem hε
    rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker] at this
    exact this
  rw [h0] at h
  have hp0 : (p : ℂ_[p]) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  exact (mul_eq_zero.1 h).resolve_left hp0

theorem galIso_tildeMap_tTilde {K : IntermediateField ℚ_[p] (PadicAlgCl p)} (σ : Gal(PadicAlgCl p/K)) :
    (galIso σ).tildeMap (tTilde p ε) = padicToTilde p ((cycloChar K σ : ℤ_[p]) : ℚ_[p]) * tTilde p ε := by
  set ρ := rhoMid p
  set c := awayToExt p ρ (wittFpbarToAway p (padicToWFrac p ((cycloChar K σ : ℤ_[p]) : ℚ_[p])))
    with hc
  have h : (galIso σ).extMap ρ (tTildeExt p ε ρ) = c * tTildeExt p ε ρ := by
    apply iota_injective inv_p_lt_rhoMid
    rw [iota_extMap, iota_tTildeExt hε hζ, gal_smul_fontaineT, map_mul, hc, iota_awayToExt_padic,
      iota_tTildeExt hε hζ]
  rw [← ofRad_tTildeExt hε hζ ρ, TeichLift.TeichIso.tildeMap_ofRad, h, map_mul, hc,
    ← padicToTilde_eq_ofRad]

end TTilde

end WAPeriodT

end GroundTheory.PAdicHodge
