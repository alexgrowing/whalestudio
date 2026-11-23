import Mathlib
import GroundTheory.PAdicHodge.ACrisPhi
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open _root_.WittVector

namespace ACris

section PD

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}
local notation "𝔭₀" => Ideal.span {(p : ACrisZero K p)}

theorem dpow_zero_right {n : ℕ} (hn : n ≠ 0) : dpow n (0 : AInf K p) = 0 := by
  rw [dpow, map_zero, zero_pow hn, mul_zero]

variable (K p) in

def pdIdeal : Ideal (AInf K p) where
  carrier := {x | ∀ n : ℕ, dpow n x ∈ ACrisZero K p}
  add_mem' {x y} hx hy n := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [dpow_add]
    exact Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (hx k) (hy (n - k))
  zero_mem' n := by
    rcases n with _ | n
    · rw [dpow_zero]; exact Subalgebra.one_mem _
    · rw [dpow_zero_right n.succ_ne_zero]; exact Subalgebra.zero_mem _
  smul_mem' c x hx n := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [smul_eq_mul, mul_comm, dpow_mul]
    exact Subalgebra.mul_mem _ (hx n) (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ c) n)

theorem mem_pdIdeal {x : AInf K p} : x ∈ pdIdeal K p ↔ ∀ n, dpow n x ∈ ACrisZero K p :=
  Iff.rfl

theorem ker_le_pdIdeal : RingHom.ker θ ≤ pdIdeal K p := fun _ hx n => dpow_mem hx n

theorem natCast_p_mem_pdIdeal : (p : AInf K p) ∈ pdIdeal K p := fun n => by
  obtain ⟨w, hw⟩ := exists_dpow_p_mul (K := K) (p := p) n 1
  rw [mul_one] at hw
  rw [hw]
  exact Subalgebra.algebraMap_mem _ w

theorem mem_pdIdeal_of_theta_mem {z : AInf K p} (hz : θ z ∈ Ideal.span {(p : 𝒪)}) :
    z ∈ pdIdeal K p := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hz
  obtain ⟨b, hb⟩ := IsPerfectoidField.surjective_fontaineTheta (K := K) p c
  have hk : z - (p : AInf K p) * b ∈ RingHom.ker θ := by
    rw [RingHom.mem_ker, map_sub, map_mul, map_natCast, hb, ← hc, mul_comm, sub_self]
  have h := add_mem (ker_le_pdIdeal hk) (Ideal.mul_mem_right b _ natCast_p_mem_pdIdeal)
  rwa [sub_add_cancel] at h

theorem one_add_pow_sub_one_mem_pdIdeal {z : AInf K p} (hz : z ∈ pdIdeal K p) :
    (1 + z) ^ p - 1 ∈ pdIdeal K p := by
  have h := geom_sum_mul (1 + z) p
  rw [add_sub_cancel_left] at h
  rw [← h]
  exact Ideal.mul_mem_left _ _ hz

def dpowJ {x : AInf K p} (hx : x ∈ pdIdeal K p) (n : ℕ) : ACrisZero K p :=
  ⟨dpow n x, hx n⟩

theorem coe_dpowJ {x : AInf K p} (hx : x ∈ pdIdeal K p) (n : ℕ) : (dpowJ hx n : 𝔸) = dpow n x :=
  rfl

def logTermJ {x : AInf K p} (hx : x ∈ pdIdeal K p) (n : ℕ) : ACrisZero K p :=
  (-1) ^ n * (n.factorial : ACrisZero K p) * dpowJ hx (n + 1)

theorem coe_logTermJ {x : AInf K p} (hx : x ∈ pdIdeal K p) (n : ℕ) :
    (logTermJ hx n : 𝔸) = (-1) ^ n * (n.factorial : 𝔸) * dpow (n + 1) x := by
  simp only [logTermJ, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg,
    Subalgebra.coe_one, SubringClass.coe_natCast, coe_dpowJ]

theorem logTermJ_mem {x : AInf K p} (hx : x ∈ pdIdeal K p) {k n : ℕ} (h : p * k ≤ n) :
    logTermJ hx n ∈ 𝔭₀ ^ k :=
  Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (natCast_mem_pow (pow_dvd_factorial h)))

def logTermJA {x : AInf K p} (hx : x ∈ pdIdeal K p) (n : ℕ) : ACris K p :=
  algebraMap (ACrisZero K p) (ACris K p) (logTermJ hx n)

theorem exists_isAdicSum_logTermJA {x : AInf K p} (hx : x ∈ pdIdeal K p) :
    ∃ s, IsAdicSum 𝔭 (logTermJA hx) s :=
  exists_isAdicSum fun k => ⟨p * k, fun _ hn => algebraMap_mem_pow (logTermJ_mem hx hn)⟩

def logJ {x : AInf K p} (hx : x ∈ pdIdeal K p) : ACris K p :=
  (exists_isAdicSum_logTermJA hx).choose

theorem isAdicSum_logJ {x : AInf K p} (hx : x ∈ pdIdeal K p) :
    IsAdicSum 𝔭 (logTermJA hx) (logJ hx) :=
  (exists_isAdicSum_logTermJA hx).choose_spec

theorem logJ_eq_of_isAdicSum {x : AInf K p} {hx : x ∈ pdIdeal K p} {s : ACris K p}
    (hs : IsAdicSum 𝔭 (logTermJA hx) s) : logJ hx = s :=
  (isAdicSum_logJ hx).unique hs

theorem logJ_congr {x y : AInf K p} (h : x = y) (hx : x ∈ pdIdeal K p) (hy : y ∈ pdIdeal K p) :
    logJ hx = logJ hy := by
  subst h; rfl

theorem logTermJ_one_add_pow {x : AInf K p} (hx : x ∈ pdIdeal K p) (n L : ℕ) (hL : p * (n + 1) ≤ L) :
    logTermJ (one_add_pow_sub_one_mem_pdIdeal hx) n =
      ∑ j ∈ Finset.range L, (logCoeff p n j : ACrisZero K p) * dpowJ hx (j + 1) := by
  apply Subtype.ext
  simp only [logTermJ, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_neg,
    Subalgebra.coe_one, SubringClass.coe_natCast, coe_dpowJ, AddSubmonoidClass.coe_finsetSum,
    SubringClass.coe_intCast]
  rw [mul_assoc, factorial_mul_dpow_eq_sum x n L hL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [logCoeff]
  push_cast
  ring

theorem p_mul_logTermJ {x : AInf K p} (hx : x ∈ pdIdeal K p) (j : ℕ) :
    (p : ACrisZero K p) * logTermJ hx j =
      ∑ n ∈ Finset.range (j + 1), (logCoeff p n j : ACrisZero K p) * dpowJ hx (j + 1) := by
  rw [← Finset.sum_mul, ← Int.cast_sum, sum_logCoeff, logTermJ]
  push_cast
  ring

theorem sum_p_mul_logTermJ_sub_mem {x : AInf K p} (hx : x ∈ pdIdeal K p) {k M : ℕ}
    (hM : p * (p * k + 1) ≤ M) :
    ∑ j ∈ Finset.range M, (p : ACrisZero K p) * logTermJ hx j -
      ∑ n ∈ Finset.range M, logTermJ (one_add_pow_sub_one_mem_pdIdeal hx) n ∈ 𝔭₀ ^ k := by
  have hpM : M ≤ p * M := Nat.le_mul_of_pos_left M hp.out.pos
  rw [Finset.sum_congr rfl fun n hn => logTermJ_one_add_pow hx n (p * M)
      (Nat.mul_le_mul_left p (Finset.mem_range.1 hn)),
    Finset.sum_congr rfl fun j _ => p_mul_logTermJ hx j]
  have h1 : ∀ j ∈ Finset.range M,
      ∑ n ∈ Finset.range (j + 1), (logCoeff p n j : ACrisZero K p) * dpowJ hx (j + 1) =
        ∑ n ∈ Finset.range M, (logCoeff p n j : ACrisZero K p) * dpowJ hx (j + 1) := by
    intro j hj
    apply Finset.sum_subset (Finset.range_subset_range.2 (Finset.mem_range.1 hj))
    intro n _ hn
    rw [Finset.mem_range, not_lt] at hn
    rw [logCoeff_of_lt (by omega), Int.cast_zero, zero_mul]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm (s := Finset.range M) (t := Finset.range (p * M)),
    ← Finset.sum_range_add_sum_Ico _ hpM, sub_add_cancel_left]
  refine neg_mem (Ideal.sum_mem _ fun j hj => Ideal.sum_mem _ fun n _ => ?_)
  have hj := (Finset.mem_Ico.1 hj).1
  by_cases hc : p * (n + 1) < j + 1
  · rw [logCoeff_of_gt hc, Int.cast_zero, zero_mul]
    exact zero_mem _
  · have hn : p * k ≤ n := by
      by_contra hlt
      have : p * (n + 1) ≤ p * (p * k) := Nat.mul_le_mul_left p (by omega)
      nlinarith
    obtain ⟨z, hz⟩ := factorial_dvd_logCoeff (p := p) n j
    rw [hz, Int.cast_mul, Int.cast_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (natCast_mem_pow (pow_dvd_factorial hn)))

theorem logJ_one_add_pow {x : AInf K p} (hx : x ∈ pdIdeal K p) :
    logJ (one_add_pow_sub_one_mem_pdIdeal hx) = (p : ACris K p) * logJ hx := by
  have hs := (isAdicSum_logJ hx).mul_left (p : ACris K p)
  apply logJ_eq_of_isAdicSum
  intro k
  obtain ⟨N, hN⟩ := hs k
  refine ⟨max N (p * (p * k + 1)), fun M hM => ?_⟩
  have h1 := hN M (le_of_max_le_left hM)
  have h2 : ∑ n ∈ Finset.range M, (p : ACris K p) * logTermJA hx n -
      ∑ n ∈ Finset.range M, logTermJA (one_add_pow_sub_one_mem_pdIdeal hx) n ∈ 𝔭 ^ k := by
    have h := algebraMap_mem_pow (sum_p_mul_logTermJ_sub_mem hx (le_of_max_le_right hM))
    rw [map_sub, map_sum, map_sum] at h
    simpa only [map_mul, map_natCast, logTermJA] using h
  have := add_mem h1 h2
  simp only at this
  rwa [sub_add_sub_cancel] at this

theorem phiZero_logTermJ {x : AInf K p} (hx : x ∈ pdIdeal K p) (hφ : φ x ∈ pdIdeal K p) (n : ℕ) :
    phiZero K p (logTermJ hx n) = logTermJ hφ n := by
  apply Subtype.ext
  rw [coe_phiZero, coe_logTermJ, coe_logTermJ, map_mul, map_mul, map_pow, map_neg, map_one,
    map_natCast, phiAway_dpow]

theorem phi_logTermJA {x : AInf K p} (hx : x ∈ pdIdeal K p) (hφ : φ x ∈ pdIdeal K p) (n : ℕ) :
    phi K p (logTermJA hx n) = logTermJA hφ n := by
  rw [logTermJA, logTermJA, phi_algebraMap_zero, phiZero_logTermJ hx hφ]

theorem phi_logJ {x : AInf K p} (hx : x ∈ pdIdeal K p) (hφ : φ x ∈ pdIdeal K p) :
    phi K p (logJ hx) = logJ hφ :=
  (logJ_eq_of_isAdicSum (((isAdicSum_logJ hx).map (phi K p) span_p_le_comap_phi).congr
    (phi_logTermJA hx hφ))).symm

theorem mu_mem_pdIdeal {x : 𝒪♭} (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)}) :
    AInf.mu (K := K) x ∈ pdIdeal K p :=
  mem_pdIdeal_of_theta_mem (by rwa [AInf.mu, map_sub, fontaineTheta_teichmuller, map_one])

def logTeich {x : 𝒪♭} (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)}) : ACris K p :=
  logJ (mu_mem_pdIdeal hx)

theorem phi_logTeich {x : 𝒪♭} (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)}) :
    phi K p (logTeich hx) = (p : ACris K p) * logTeich hx := by
  have h1 := one_add_pow_sub_one_mem_pdIdeal (mu_mem_pdIdeal hx)
  have hφ : φ (AInf.mu (K := K) x) ∈ pdIdeal K p := by rw [frobenius_mu]; exact h1
  rw [logTeich, phi_logJ _ hφ, logJ_congr (frobenius_mu x) hφ h1, logJ_one_add_pow]

end PD

section Theta

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p] [CharZero K]

local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}

theorem thetaZero_logTermJ_zero {x : AInf K p} (hx : x ∈ pdIdeal K p) :
    thetaZero K p (logTermJ hx 0) = θ x := by
  apply Subtype.ext
  rw [coe_thetaZero, coe_logTermJ, pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, one_mul,
    zero_add, dpow_one, thetaAway_algebraMap]

theorem thetaZero_logTermJ_mem {x : AInf K p} (hx : x ∈ pdIdeal K p) {c : 𝒪}
    (hc : θ x = (p : 𝒪) ^ 2 * c) (m : ℕ) :
    thetaZero K p (logTermJ hx (m + 1)) ∈ Ideal.span {(p : 𝒪) ^ 3} := by
  obtain ⟨w, hw⟩ := exists_natCast_mul_eq_pow (K := K) (p := p) (n := m + 2) (k := 2 * m + 1)
    (by omega) (by have := Nat.factorization_lt p (show m + 2 ≠ 0 by omega); omega)
  rw [Ideal.mem_span_singleton']
  refine ⟨(-1) ^ (m + 1) * (θ w * c ^ (m + 2)), Subtype.ext ?_⟩
  have hn1 : ((m + 2 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hf : (m + 2).factorial = (m + 2) * (m + 1).factorial := Nat.factorial_succ (m + 1)
  have e : ((m + 2 : ℕ) : 𝔸) * (((m + 1).factorial : 𝔸) * dpow (m + 2) x) =
      algebraMap (AInf K p) 𝔸 x ^ (m + 2) := by
    rw [← mul_assoc, ← Nat.cast_mul, ← hf, factorial_mul_dpow]
  have e2 := congrArg (thetaAway K p) e
  rw [map_mul, map_natCast, map_pow, thetaAway_algebraMap] at e2
  have hw2 : ((m + 2 : ℕ) : K) * (θ w : K) = (p : K) ^ (2 * m + 1) := by
    have := congrArg (fun a => ((θ a : 𝒪) : K)) hw
    simpa only [map_mul, map_natCast, map_pow, MulMemClass.coe_mul, SubringClass.coe_natCast,
      SubmonoidClass.coe_pow] using this
  have hc2 : (θ x : K) = (p : K) ^ 2 * (c : K) := by
    have := congrArg (fun a : 𝒪 => (a : K)) hc
    simpa only [MulMemClass.coe_mul, SubringClass.coe_natCast, SubmonoidClass.coe_pow] using this
  rw [hc2] at e2
  have e3 : thetaAway K p ((-1) ^ (m + 1) * ((m + 1).factorial : 𝔸) * dpow (m + 1 + 1) x) =
      (-1 : K) ^ (m + 1) * thetaAway K p (((m + 1).factorial : 𝔸) * dpow (m + 2) x) := by
    rw [mul_assoc, map_mul, map_pow, map_neg, map_one]
  rw [coe_thetaZero, coe_logTermJ, e3]
  apply mul_left_cancel₀ hn1
  push_cast at hw2 e2 ⊢
  linear_combination ((-1 : K) ^ (m + 1) * (c : K) ^ (m + 2) * (p : K) ^ 3) * hw2 -
    (-1 : K) ^ (m + 1) * e2

theorem theta_logJ_sub_mem {x : AInf K p} (hx : x ∈ pdIdeal K p) {c : 𝒪}
    (hc : θ x = (p : 𝒪) ^ 2 * c) : theta K p (logJ hx) - θ x ∈ Ideal.span {(p : 𝒪) ^ 3} := by
  have hle : 𝔭 ≤ (Ideal.span {(p : 𝒪)}).comap (theta K p) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_span_singleton_self _
  obtain ⟨N, hN⟩ := (isAdicSum_logJ hx).map (theta K p) hle 3
  have h := hN (N + 1) (Nat.le_succ N)
  have ht : ∀ n, theta K p (logTermJA hx n) = thetaZero K p (logTermJ hx n) := fun n => by
    rw [logTermJA, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      theta_of]
  simp only [ht] at h
  rw [Finset.sum_range_succ', thetaZero_logTermJ_zero, Ideal.span_singleton_pow] at h
  have hs : ∑ n ∈ Finset.range N, thetaZero K p (logTermJ hx (n + 1)) ∈
      Ideal.span {(p : 𝒪) ^ 3} :=
    Ideal.sum_mem _ fun n _ => thetaZero_logTermJ_mem hx hc n
  have := add_mem h hs
  convert this using 1
  ring

theorem theta_logTeich_sub_mem {x : 𝒪♭} (hx : PreTilt.untilt x - 1 ∈ Ideal.span {(p : 𝒪)})
    {c : 𝒪} (hc : PreTilt.untilt x - 1 = (p : 𝒪) ^ 2 * c) :
    theta K p (logTeich hx) - (p : 𝒪) ^ 2 * c ∈ Ideal.span {(p : 𝒪) ^ 3} := by
  have hθ : θ (AInf.mu (K := K) x) = PreTilt.untilt x - 1 := by
    rw [AInf.mu, map_sub, fontaineTheta_teichmuller, map_one]
  have h := theta_logJ_sub_mem (mu_mem_pdIdeal hx) (c := c) (by rw [hθ, hc])
  rwa [hθ, hc] at h

end Theta

end ACris

end GroundTheory.PAdicHodge
