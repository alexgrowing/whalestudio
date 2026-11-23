import Mathlib
import GroundTheory.PAdicHodge.BCrisNewtonLift
import GroundTheory.PAdicHodge.FactorizationFactorialLe
import GroundTheory.PAdicHodge.KerTheta
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace WittTilt

open _root_.WittVector Laurent

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "θ" => fontaineTheta (normInteger K) p

theorem norm_zcoeff_incl_le_one (x : AInf K p) (n : ℤ) :
    ‖(teichLift K p).zcoeff (incl K p x) n‖ ≤ 1 := by
  unfold TeichLift.zcoeff
  split_ifs
  · exact norm_coeff_incl_le_one x _
  · simp

theorem convergesAt_zcoeff_incl (x : AInf K p) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ConvergesAt ((teichLift K p).zcoeff (incl K p x)) ρ := by
  refine convergesAt_of_eventually hρ0 ((teichLift K p).zcoeff_neg_exists _) fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hρ1
  refine ⟨N, fun n hn => ?_⟩
  calc ‖(teichLift K p).zcoeff (incl K p x) n‖ * ρ ^ n ≤ 1 * ρ ^ (N : ℤ) :=
        mul_le_mul (norm_zcoeff_incl_le_one x n) (zpow_le_zpow_right_of_le_one₀ hρ0 hρ1.le hn)
          (zpow_pos hρ0 n).le zero_le_one
    _ ≤ ε := by rw [one_mul, zpow_natCast]; exact hN.le

theorem exists_toB_mul (z : 𝔸) : ∃ (M : ℕ) (x : AInf K p),
    toB K p z * algebraMap _ (teichLift K p).B (teichLift K p).π ^ M =
      algebraMap _ (teichLift K p).B (incl K p x) := by
  obtain ⟨M, x, hx⟩ := IsLocalization.Away.surj (p : AInf K p) z
  refine ⟨M, x, ?_⟩
  have h := congrArg (toB K p) hx
  rw [map_mul, map_pow, toB_algebraMap, toB_algebraMap, map_natCast, map_natCast] at h
  rw [show algebraMap (WittVector p K♭) (teichLift K p).B (teichLift K p).π = (p : (teichLift K p).B) from
    map_natCast _ p]
  exact h

theorem convergesAt_toB (z : 𝔸) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    ConvergesAt ((teichLift K p).coeffB (toB K p z)) ρ := by
  obtain ⟨M, x, h⟩ := exists_toB_mul z
  rw [TeichLift.coeffB_eq _ h]
  exact convergesAt_shift hρ0 (convergesAt_zcoeff_incl x hρ0 hρ1) M

variable (K p) in

def gn (ρ : ℝ) (z : 𝔸) : ℝ := gaussNorm ((teichLift K p).coeffB (toB K p z)) ρ

variable {ρ : ℝ}

theorem gn_nonneg (hρ0 : 0 < ρ) (z : 𝔸) : 0 ≤ gn K p ρ z := gaussNorm_nonneg hρ0

theorem gn_mul (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (z w : 𝔸) :
    gn K p ρ (z * w) = gn K p ρ z * gn K p ρ w := by
  unfold gn
  rw [map_mul]
  exact ((teichLift K p).convergesAt_coeffB_mul hρ0 hρ1 (convergesAt_toB z hρ0 hρ1)
    (convergesAt_toB w hρ0 hρ1)).2

theorem gn_add_le (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (z w : 𝔸) :
    gn K p ρ (z + w) ≤ max (gn K p ρ z) (gn K p ρ w) := by
  unfold gn
  rw [map_add]
  exact ((teichLift K p).convergesAt_coeffB_add hρ0 hρ1 (convergesAt_toB z hρ0 hρ1)
    (convergesAt_toB w hρ0 hρ1)).2

theorem gn_neg (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (z : 𝔸) : gn K p ρ (-z) = gn K p ρ z := by
  unfold gn
  rw [map_neg]
  exact ((teichLift K p).convergesAt_coeffB_neg hρ0 hρ1 (convergesAt_toB z hρ0 hρ1)).2

theorem gn_sub_le (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (z w : 𝔸) :
    gn K p ρ (z - w) ≤ max (gn K p ρ z) (gn K p ρ w) := by
  rw [sub_eq_add_neg, ← gn_neg hρ0 hρ1 w]
  exact gn_add_le hρ0 hρ1 z (-w)

theorem gn_pow (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (z : 𝔸) (n : ℕ) : gn K p ρ (z ^ n) = gn K p ρ z ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    unfold gn
    rw [map_one, ← map_one (algebraMap (WittVector p K♭) (teichLift K p).B),
      TeichLift.coeffB_algebraMap, TeichLift.zcoeff_one]
    refine le_antisymm (TeichLift.gaussNorm_single_zero_one_le (L := K♭) hρ0) ?_
    have := (TeichLift.convergesAt_pi_single (0 : ℤ) (1 : K♭) ρ).le_gaussNorm 0
    simpa using this
  | succ n ih => rw [pow_succ, gn_mul hρ0 hρ1, ih, pow_succ]

theorem gn_one (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : gn K p ρ (1 : 𝔸) = 1 := by
  simpa using gn_pow (K := K) hρ0 hρ1 (1 : 𝔸) 0

theorem gn_zero : gn K p ρ (0 : 𝔸) = 0 := by
  unfold gn
  rw [map_zero, ← map_zero (algebraMap (WittVector p K♭) (teichLift K p).B),
    TeichLift.coeffB_algebraMap, ((teichLift K p).zcoeff_eq_zero_iff 0).2 rfl]
  simp [gaussNorm]

theorem gn_algebraMap (x : AInf K p) :
    gn K p ρ (algebraMap (AInf K p) 𝔸 x) = gaussNorm ((teichLift K p).zcoeff (incl K p x)) ρ := by
  unfold gn
  rw [coeffB_toB_algebraMap]

theorem gn_pos (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {z : 𝔸} (hz : z ≠ 0) : 0 < gn K p ρ z := by
  obtain ⟨M, x, h⟩ := exists_toB_mul z
  have hx : x ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at h
    exact hz (toB_injective (by rw [map_zero]; exact (teichLift K p).eq_zero_of_mul_pow h))
  have hx' : (teichLift K p).zcoeff (incl K p x) ≠ 0 := fun h0 =>
    hx (incl_injective (by rw [((teichLift K p).zcoeff_eq_zero_iff _).1 h0, map_zero]))
  have hc := convergesAt_zcoeff_incl x hρ0 hρ1
  unfold gn
  rw [TeichLift.coeffB_eq _ h, gaussNorm_shift hρ0]
  exact mul_pos (gaussNorm_pos hρ0 hc hx') (zpow_pos hρ0 _)

theorem gaussNorm_single_one (hρ0 : 0 < ρ) :
    gaussNorm (Pi.single (1 : ℤ) (1 : K♭)) ρ = ρ := by
  refine le_antisymm (gaussNorm_le fun n => ?_) ?_
  · by_cases hn : n = 1
    · subst hn; simp
    · rw [Pi.single_eq_of_ne hn, norm_zero, zero_mul]; exact hρ0.le
  · have := (TeichLift.convergesAt_pi_single (1 : ℤ) (1 : K♭) ρ).le_gaussNorm 1
    simpa using this

theorem gn_natCast_p (hρ0 : 0 < ρ) : gn K p ρ (p : 𝔸) = ρ := by
  rw [← map_natCast (algebraMap (AInf K p) 𝔸) p, gn_algebraMap, map_natCast,
    show (p : WittVector p K♭) = (teichLift K p).π ^ 1 by rw [pow_one]; rfl,
    TeichLift.zcoeff_π_pow]
  exact_mod_cast gaussNorm_single_one hρ0

theorem gn_algebraMap_le_one (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (x : AInf K p) :
    gn K p ρ (algebraMap (AInf K p) 𝔸 x) ≤ 1 := by
  rw [gn_algebraMap]
  refine gaussNorm_le fun n => ?_
  by_cases hn : 0 ≤ n
  · exact mul_le_one₀ (norm_zcoeff_incl_le_one x n) (zpow_nonneg hρ0.le n)
      (zpow_le_one₀ hρ0 hρ1 hn)
  · rw [(teichLift K p).zcoeff_of_neg _ (not_le.1 hn), norm_zero, zero_mul]; exact zero_le_one

theorem gn_unit (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {x : AInf K p} (hx : IsUnit x) :
    gn K p ρ (algebraMap (AInf K p) 𝔸 x) = 1 := by
  obtain ⟨u, rfl⟩ := hx
  have h1 := gn_algebraMap_le_one (K := K) hρ0 hρ1.le (u : AInf K p)
  have h2 := gn_algebraMap_le_one (K := K) hρ0 hρ1.le (↑u⁻¹ : AInf K p)
  have h3 : gn K p ρ (algebraMap (AInf K p) 𝔸 u) * gn K p ρ (algebraMap (AInf K p) 𝔸 ↑u⁻¹) = 1 := by
    rw [← gn_mul hρ0 hρ1, ← map_mul, Units.mul_inv, map_one, gn_one hρ0 hρ1]
  nlinarith [gn_nonneg (K := K) hρ0 (algebraMap (AInf K p) 𝔸 u),
    gn_nonneg (K := K) hρ0 (algebraMap (AInf K p) 𝔸 ↑u⁻¹)]

theorem gn_natCast (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {m : ℕ} (hm : m ≠ 0) :
    gn K p ρ (m : 𝔸) = ρ ^ (m.factorization p) := by
  have e : (m : 𝔸) = (p : 𝔸) ^ (m.factorization p) * ((ordCompl[p] m : ℕ) : 𝔸) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
  rw [e, gn_mul hρ0 hρ1, gn_pow hρ0 hρ1, gn_natCast_p hρ0,
    ← map_natCast (algebraMap (AInf K p) 𝔸) (ordCompl[p] m),
    gn_unit hρ0 hρ1 (WittVector.isUnit_natCast_of_coprime ((Nat.coprime_ordCompl hp.out hm).symm)),
    mul_one]

theorem norm_coeff_zero_le_of_mem_ker {x : AInf K p} (hx : x ∈ RingHom.ker θ) :
    ‖x.coeff 0‖ ≤ ‖(p : K)‖ := by
  obtain ⟨v, hv⟩ := exists_eq_teichmuller_add_mul_p x
  have h := congrArg θ hv
  rw [RingHom.mem_ker.1 hx, map_add, map_mul, map_natCast, fontaineTheta_teichmuller] at h
  have h' : ((PreTilt.untilt (x.coeff 0) : 𝒪) : K) = -((θ v : 𝒪) : K) * p := by
    have := congrArg (fun y : 𝒪 => (y : K)) h
    push_cast at this
    linear_combination -this
  rw [preTilt_norm_def, h', norm_mul, norm_neg]
  exact mul_le_of_le_one_left (norm_nonneg _) (mem_normInteger.1 (θ v).2)

theorem zcoeff_incl_natCast (x : AInf K p) (n : ℕ) :
    (teichLift K p).zcoeff (incl K p x) n = algebraMap 𝒪♭ K♭ (tcoeff x n) := by
  simp [TeichLift.zcoeff, coeff_incl]

theorem zcoeff_incl_zero (x : AInf K p) :
    (teichLift K p).zcoeff (incl K p x) 0 = algebraMap 𝒪♭ K♭ (x.coeff 0) := by
  have := zcoeff_incl_natCast x 0
  rwa [tcoeff_zero, Nat.cast_zero] at this

theorem gn_ker_le (hp0 : ‖(p : K)‖ ≤ ρ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {x : AInf K p}
    (hx : x ∈ RingHom.ker θ) : gn K p ρ (algebraMap (AInf K p) 𝔸 x) ≤ ρ := by
  rw [gn_algebraMap]
  refine gaussNorm_le fun n => ?_
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · rw [(teichLift K p).zcoeff_of_neg _ hn, norm_zero, zero_mul]; exact hρ0.le
  · rw [zcoeff_incl_zero, norm_algebraMap_preTilt, zpow_zero, mul_one]
    exact (norm_coeff_zero_le_of_mem_ker hx).trans hp0
  · calc _ ≤ 1 * ρ ^ n :=
          mul_le_mul_of_nonneg_right (norm_zcoeff_incl_le_one x n) (zpow_nonneg hρ0.le n)
      _ ≤ ρ := by
          rw [one_mul]
          exact (zpow_le_zpow_right_of_le_one₀ hρ0 hρ1.le (show (1 : ℤ) ≤ n by omega)).trans_eq
            (zpow_one ρ)

theorem gn_dpow_le (hp0 : ‖(p : K)‖ ≤ ρ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {x : AInf K p}
    (hx : x ∈ RingHom.ker θ) (n : ℕ) : gn K p ρ (ACris.dpow n x) ≤ 1 := by
  have h := congrArg (gn K p ρ) (ACris.factorial_mul_dpow n x)
  rw [gn_mul hρ0 hρ1, gn_pow hρ0 hρ1, gn_natCast hρ0 hρ1 (Nat.factorial_ne_zero n)] at h
  have hv := ACris.factorization_factorial_le (p := p) n
  have hxn : gn K p ρ (algebraMap (AInf K p) 𝔸 x) ^ n ≤ ρ ^ n :=
    pow_le_pow_left₀ (gn_nonneg hρ0 _) (gn_ker_le hp0 hρ0 hρ1 hx) n
  have h2 : ρ ^ n ≤ ρ ^ (n.factorial.factorization p) := pow_le_pow_of_le_one hρ0.le hρ1.le hv
  have hpos : 0 < ρ ^ (n.factorial.factorization p) := pow_pos hρ0 _
  by_contra hc
  push_neg at hc
  have := mul_lt_mul_of_pos_left hc hpos
  linarith

theorem gn_acrisZero_le_one (hp0 : ‖(p : K)‖ ≤ ρ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {z : 𝔸}
    (hz : z ∈ ACris.ACrisZero K p) : gn K p ρ z ≤ 1 := by
  have hz' : z ∈ Algebra.adjoin (AInf K p) {y | ∃ n : ℕ, ∃ x ∈ RingHom.ker θ, ACris.dpow n x = y} := hz
  clear hz
  induction hz' using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨n, y, hy, rfl⟩ := hx
    exact gn_dpow_le hp0 hρ0 hρ1 hy n
  | algebraMap r => exact gn_algebraMap_le_one hρ0 hρ1.le r
  | add x y _ _ hx hy => exact (gn_add_le hρ0 hρ1 x y).trans (max_le hx hy)
  | mul x y _ _ hx hy =>
    rw [gn_mul hρ0 hρ1]
    exact mul_le_one₀ hx (gn_nonneg hρ0 _) hy

variable [CharZero K]

theorem norm_p_pos : 0 < ‖(p : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hp.out.ne_zero)

theorem norm_p_lt_one : ‖(p : K)‖ < 1 := IsPerfectoidField.norm_natCast_lt_one

theorem norm_theta_le (x : AInf K p) :
    ‖((θ x : 𝒪) : K)‖ ≤ gn K p ‖(p : K)‖ (algebraMap (AInf K p) 𝔸 x) := by
  set r₀ := ‖(p : K)‖ with hr₀
  set G := gn K p r₀ (algebraMap (AInf K p) 𝔸 x) with hG
  have hr0 : 0 < r₀ := norm_p_pos
  have hr1 : r₀ < 1 := norm_p_lt_one
  have key : ∀ n : ℕ, ‖((θ x : 𝒪) : K)‖ ≤ max G (r₀ ^ (n + 1)) := by
    intro n
    obtain ⟨d, hd⟩ := (WittVector.eq_teichmullerSeries_iff (tcoeff x) x).1
      (WittVector.teichmullerSeries_coeff_eq x).symm n
    have hθ : ((θ x : 𝒪) : K) = ∑ i ∈ Finset.Iic n,
        ((PreTilt.untilt (tcoeff x i) : 𝒪) : K) * (p : K) ^ i + (p : K) ^ (n + 1) * ((θ d : 𝒪) : K) := by
      have e := congrArg (fun y => ((θ y : 𝒪) : K)) (eq_add_of_sub_eq hd)
      simp only [map_add, map_sum, map_mul, map_pow, map_natCast, fontaineTheta_teichmuller] at e
      push_cast at e
      rw [e, add_comm]
    rw [hθ]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max ?_ ?_)
    · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (gn_nonneg hr0 _) fun i _ => ?_
      rw [norm_mul, norm_pow, ← preTilt_norm_def]
      have := (convergesAt_zcoeff_incl x hr0 hr1).le_gaussNorm (i : ℤ)
      rw [zcoeff_incl_natCast, norm_algebraMap_preTilt, zpow_natCast] at this
      rw [hG, gn_algebraMap]
      exact this
    · rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (mem_normInteger.1 (θ d).2)
  by_contra hlt
  push_neg at hlt
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (lt_of_le_of_lt (gn_nonneg hr0 _) hlt) hr1
  have h2 : r₀ ^ (n + 1) < ‖((θ x : 𝒪) : K)‖ :=
    (pow_le_pow_of_le_one hr0.le hr1.le (Nat.le_succ n)).trans_lt hn
  exact lt_irrefl _ ((key n).trans_lt (max_lt hlt h2))

theorem exists_eq_pow_mul_add_xi_mul {ξ : AInf K p} (hξ : RingHom.ker θ = Ideal.span {ξ}) {k : ℕ}
    {y : AInf K p} (hy : gn K p ‖(p : K)‖ (algebraMap (AInf K p) 𝔸 y) ≤ ‖(p : K)‖ ^ k) :
    ∃ w z : AInf K p, y = (p : AInf K p) ^ k * w + ξ * z := by
  have hθ := (norm_theta_le y).trans hy
  have hpk : ((p : K) ^ k) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hp.out.ne_zero)
  set c : K := ((θ y : 𝒪) : K) / (p : K) ^ k with hc_def
  have hc : ‖c‖ ≤ 1 := by
    rw [hc_def, norm_div, norm_pow, div_le_one (pow_pos norm_p_pos k)]
    exact hθ
  obtain ⟨w, hw⟩ := IsPerfectoidField.surjective_fontaineTheta (K := K) (p := p) ⟨c, mem_normInteger.2 hc⟩
  have hker : y - (p : AInf K p) ^ k * w ∈ RingHom.ker θ := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_pow, map_natCast, hw]
    apply Subtype.ext
    push_cast
    rw [hc_def]
    field_simp
    ring
  rw [hξ] at hker
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hker
  exact ⟨w, z, by rw [mul_comm ξ, hz]; ring⟩

theorem exists_eq_pow_mul_add_xi_pow_mul {ξ : AInf K p} (hξ : RingHom.ker θ = Ideal.span {ξ})
    (hξr : ‖(p : K)‖ ≤ gn K p ‖(p : K)‖ (algebraMap (AInf K p) 𝔸 ξ)) (m : ℕ) :
    ∀ (k : ℕ) (y : AInf K p), gn K p ‖(p : K)‖ (algebraMap (AInf K p) 𝔸 y) ≤ ‖(p : K)‖ ^ (k + m) →
      ∃ w z : AInf K p, y = (p : AInf K p) ^ k * w + ξ ^ (m + 1) * z := by
  set r₀ := ‖(p : K)‖ with hr₀
  have hr0 : 0 < r₀ := norm_p_pos
  have hr1 : r₀ < 1 := norm_p_lt_one
  induction m with
  | zero =>
    intro k y hy
    simpa using exists_eq_pow_mul_add_xi_mul hξ (by simpa using hy)
  | succ m ih =>
    intro k y hy
    obtain ⟨w₀, y₁, h₀⟩ := exists_eq_pow_mul_add_xi_mul hξ (k := k + (m + 1)) hy
    have hb : gn K p r₀ (algebraMap _ 𝔸 (ξ * y₁)) ≤ r₀ ^ (k + (m + 1)) := by
      have e : ξ * y₁ = y - (p : AInf K p) ^ (k + (m + 1)) * w₀ := by rw [h₀]; ring
      rw [e, map_sub, map_mul, map_pow, map_natCast]
      refine (gn_sub_le hr0 hr1 _ _).trans (max_le hy ?_)
      rw [gn_mul hr0 hr1, gn_pow hr0 hr1, gn_natCast_p hr0]
      exact mul_le_of_le_one_right (by positivity) (gn_algebraMap_le_one hr0 hr1.le w₀)
    rw [map_mul, gn_mul hr0 hr1] at hb
    have hy₁ : gn K p r₀ (algebraMap _ 𝔸 y₁) ≤ r₀ ^ (k + m) := by
      have h1 := mul_le_mul_of_nonneg_right hξr (gn_nonneg hr0 (algebraMap _ 𝔸 y₁))
      have h2 : r₀ * gn K p r₀ (algebraMap _ 𝔸 y₁) ≤ r₀ * r₀ ^ (k + m) := by
        calc _ ≤ _ := h1
          _ ≤ r₀ ^ (k + (m + 1)) := hb
          _ = r₀ * r₀ ^ (k + m) := by ring
      exact le_of_mul_le_mul_left h2 hr0
    obtain ⟨w₁, z₁, h₁⟩ := ih k y₁ hy₁
    refine ⟨(p : AInf K p) ^ (m + 1) * w₀ + ξ * w₁, z₁, ?_⟩
    rw [h₀, h₁]
    ring

end WittTilt

end GroundTheory.PAdicHodge
