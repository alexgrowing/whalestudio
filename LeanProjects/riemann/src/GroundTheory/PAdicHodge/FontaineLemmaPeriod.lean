import Mathlib
import GroundTheory.PAdicHodge.ACrisLog
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open _root_.WittVector

namespace ACris

section NumberTheory

variable {p : ℕ} [hp : Fact p.Prime]

theorem mul_sub_one_add_one_le_pow (k : ℕ) : k * (p - 1) + 1 ≤ p ^ k := by
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.out.one_le).symm⟩
  rw [hm, Nat.add_sub_cancel]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h1 : 1 ≤ (m + 1) ^ k := Nat.one_le_pow _ _ (Nat.succ_pos m)
    nlinarith

theorem two_mul_mul_sub_one_le_pow_add (k : ℕ) : 2 * k * (p - 1) ≤ p ^ k + p := by
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.out.one_le).symm⟩
  have hm1 : 1 ≤ m := by have := hp.out.two_le; omega
  rw [hm, Nat.add_sub_cancel]
  induction k with
  | zero => simp
  | succ k ih =>
    rcases k with _ | k
    · rw [zero_add, pow_one]; omega
    · have h2 : 2 ≤ (m + 1) ^ (k + 1) :=
        calc 2 ≤ (m + 1) ^ 1 := by rw [pow_one]; omega
          _ ≤ (m + 1) ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      rw [pow_succ]
      nlinarith

theorem factorization_succ_le_div (n : ℕ) : (n + 1).factorization p ≤ n / (p - 1) := by
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
  rw [Nat.le_div_iff_mul_le hp1]
  have h1 := Nat.ordProj_le p (Nat.succ_ne_zero n)
  have h2 := mul_sub_one_add_one_le_pow (p := p) ((n + 1).factorization p)
  generalize (n + 1).factorization p = k at h1 h2 ⊢
  generalize p ^ k = A at h1 h2
  generalize k * (p - 1) = B at h2 ⊢
  omega

theorem add_factorization_succ_le_div {n j : ℕ} (hn : 2 * (p - 1) * j + 3 * p ≤ n) :
    j + (n + 1).factorization p ≤ n / (p - 1) := by
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
  rw [Nat.le_div_iff_mul_le hp1]
  have h1 := Nat.ordProj_le p (Nat.succ_ne_zero n)
  have h2 := two_mul_mul_sub_one_le_pow_add (p := p) ((n + 1).factorization p)
  generalize (n + 1).factorization p = k at h1 h2 ⊢
  generalize p ^ k = A at h1 h2
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.out.one_le).symm⟩
  subst hm
  rw [Nat.add_sub_cancel] at hn h2 ⊢
  nlinarith

end NumberTheory

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}

theorem dpow_p_pow_succ (x : AInf K p) (j : ℕ) :
    dpow p x ^ (j + 1) =
      ((∏ i ∈ Finset.range j, ((i + 2) * p).choose p : ℕ) : 𝔸) * dpow ((j + 1) * p) x := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : (j + 1) * p + p = (j + 2) * p := by ring
    have e2 : (j + 1 + 1) * p = (j + 2) * p := by ring
    rw [pow_succ, ih, mul_assoc, dpow_mul_dpow, Nat.choose_symm_add, e, e2,
      Finset.prod_range_succ, Nat.cast_mul]
    ring

theorem dpow_p_pow_p_mem {x : AInf K p} (hx : x ∈ RingHom.ker θ) :
    (⟨dpow p x, dpow_mem hx p⟩ : ACrisZero K p) ^ p ∈ Ideal.span {(p : ACrisZero K p)} := by
  have hp2 := hp.out.two_le
  have hdvd : p ∣ ∏ i ∈ Finset.range (p - 1), ((i + 2) * p).choose p := by
    have hmem : p - 2 ∈ Finset.range (p - 1) := Finset.mem_range.2 (by omega)
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ hmem)
    have e : (p - 2 + 2) * p = p ^ 2 := by rw [Nat.sub_add_cancel hp2, sq]
    rw [e]
    refine (Nat.Prime.dvd_choose_pow_iff hp.out).2 ⟨hp.out.ne_zero, fun h => ?_⟩
    nlinarith
  obtain ⟨N, hN⟩ := hdvd
  have h := dpow_p_pow_succ (K := K) x (p - 1)
  rw [Nat.sub_add_cancel hp.out.one_le, hN] at h
  rw [Ideal.mem_span_singleton']
  refine ⟨(N : ACrisZero K p) * ⟨dpow (p * p) x, dpow_mem hx _⟩, Subtype.ext ?_⟩
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, SubringClass.coe_natCast]
  rw [h, Nat.cast_mul]
  ring

theorem exists_mu_pow_eq_pow_mem {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    ∃ c : ACrisZero K p,
      (algebraMap (AInf K p) (ACrisZero K p) (AInf.mu ε)) ^ (p - 1) = (p : ACrisZero K p) * c ∧
        c ^ p ∈ Ideal.span {(p : ACrisZero K p)} := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (xi_sub_pow_mem (K := K) ε)
  have hξ : AInf.xi ε ∈ RingHom.ker θ := RingHom.mem_ker.2 (AInf.fontaineTheta_xi hε hζ)
  set ξ := AInf.xi (K := K) ε
  set v := (φ).symm (AInf.mu ε)
  have hμ : AInf.mu ε = ξ * v := AInf.mu_eq_xi_mul ε
  have hW : AInf.mu ε ^ (p - 1) = ξ ^ p - (p : AInf K p) * (a * ξ ^ (p - 1)) := by
    have hv : v ^ (p - 1) = ξ - a * p := by rw [ha]; ring
    have hp1 : ξ ^ p = ξ ^ (p - 1) * ξ := by rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le]
    rw [hμ, mul_pow, hv, hp1]
    ring
  set D : ACrisZero K p := ⟨dpow p ξ, dpow_mem hξ p⟩ with hD
  set B : ACrisZero K p := algebraMap (AInf K p) (ACrisZero K p) (a * ξ ^ (p - 1)) with hB
  have hξp : (algebraMap (AInf K p) (ACrisZero K p) ξ) ^ p = (p.factorial : ACrisZero K p) * D := by
    apply Subtype.ext
    simp only [Subalgebra.coe_pow, Subalgebra.coe_mul, SubringClass.coe_natCast,
      Subalgebra.coe_algebraMap, hD]
    rw [factorial_mul_dpow]
  refine ⟨((p - 1).factorial : ACrisZero K p) * D - B, ?_, ?_⟩
  · apply Subtype.ext
    simp only [Subalgebra.coe_pow, Subalgebra.coe_mul, Subalgebra.coe_sub, SubringClass.coe_natCast,
      Subalgebra.coe_algebraMap, hD, hB]
    rw [← map_pow, hW, map_sub, map_pow, ← factorial_mul_dpow, map_mul, map_natCast,
      ← Nat.mul_factorial_pred hp.out.ne_zero, Nat.cast_mul]
    ring
  · have hDp : D ^ p ∈ Ideal.span {(p : ACrisZero K p)} := dpow_p_pow_p_mem hξ
    have hBp : B ^ p ∈ Ideal.span {(p : ACrisZero K p)} := by
      have e : B ^ p = algebraMap (AInf K p) (ACrisZero K p) a ^ p *
          ((p.factorial : ACrisZero K p) * D) ^ (p - 1) := by
        rw [hB, ← hξp, map_mul, map_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm (p - 1) p]
      rw [e]
      refine Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ?_ _ (Nat.sub_pos_of_lt hp.out.one_lt))
      rw [← Nat.mul_factorial_pred hp.out.ne_zero, Nat.cast_mul, mul_assoc]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out (((p - 1).factorial : ACrisZero K p) * D) (-B)
    rw [sub_eq_add_neg, hr]
    refine add_mem (add_mem ?_ ?_) ?_
    · rw [mul_pow]; exact Ideal.mul_mem_left _ _ hDp
    · rw [show (-B) ^ p = (-1) ^ p * B ^ p by ring]; exact Ideal.mul_mem_left _ _ hBp
    · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
        (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

theorem mem_jacobson_of_pow_mem {x : ACris K p} {m : ℕ} (h : x ^ m ∈ 𝔭) :
    x ∈ (⊥ : Ideal (ACris K p)).jacobson :=
  Ideal.isRadical_jacobson ⊥ ⟨m, IsAdicComplete.le_jacobson_bot _ h⟩

set_option maxHeartbeats 1600000 in

theorem exists_periodT_eq_mu_mul_unit {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    ∃ u : ACris K p, IsUnit u ∧
      periodT hε = algebraMap (AInf K p) (ACris K p) (AInf.mu ε) * u := by
  obtain ⟨c, hc, hcp⟩ := exists_mu_pow_eq_pow_mem hε hζ
  set M : ACrisZero K p := algebraMap (AInf K p) (ACrisZero K p) (AInf.mu ε) with hM
  have hw : ∀ n : ℕ, ∃ w : AInf K p,
      ((n + 1 : ℕ) : AInf K p) * w = (p : AInf K p) ^ (n + 1).factorization p :=
    fun n => exists_natCast_mul_eq_pow (Nat.succ_ne_zero n) le_rfl
  choose w hw using hw
  let V : ℕ → ACrisZero K p := fun n => (-1) ^ n * M ^ (n % (p - 1)) * c ^ (n / (p - 1)) *
    algebraMap (AInf K p) (ACrisZero K p) (w n)
  let U : ℕ → ACrisZero K p := fun n =>
    (p : ACrisZero K p) ^ (n / (p - 1) - (n + 1).factorization p) * V n

  have hU : ∀ n : ℕ, ((n + 1 : ℕ) : ACrisZero K p) * U n = (-1) ^ n * M ^ n := by
    intro n
    have hk := factorization_succ_le_div (p := p) n
    have hwn : ((n + 1 : ℕ) : ACrisZero K p) * algebraMap (AInf K p) (ACrisZero K p) (w n) =
        (p : ACrisZero K p) ^ (n + 1).factorization p := by
      rw [← map_natCast (algebraMap (AInf K p) (ACrisZero K p)), ← map_mul, hw n, map_pow,
        map_natCast]
    have hMn : M ^ n = M ^ (n % (p - 1)) * ((p : ACrisZero K p) * c) ^ (n / (p - 1)) := by
      rw [← hc, ← pow_mul, ← pow_add, Nat.mod_add_div]
    calc ((n + 1 : ℕ) : ACrisZero K p) * U n
        = (-1) ^ n * M ^ (n % (p - 1)) * c ^ (n / (p - 1)) *
            ((p : ACrisZero K p) ^ (n / (p - 1) - (n + 1).factorization p) *
              (((n + 1 : ℕ) : ACrisZero K p) * algebraMap (AInf K p) (ACrisZero K p) (w n))) := by
          simp only [U, V]; ring
      _ = (-1) ^ n * M ^ (n % (p - 1)) * c ^ (n / (p - 1)) * (p : ACrisZero K p) ^ (n / (p - 1)) := by
          rw [hwn, pow_sub_mul_pow _ hk]
      _ = (-1) ^ n * M ^ n := by rw [hMn, mul_pow]; ring

  have hlog : ∀ n : ℕ, logTermZero (mu_mem_ker hε) n = M * U n := by
    intro n
    have h1 := isUnit_natCast (K := K) (p := p) (Nat.succ_ne_zero n)
    apply Subtype.ext
    apply h1.mul_left_cancel
    have e1 : ((n + 1 : ℕ) : ACrisZero K p) * logTermZero (mu_mem_ker hε) n =
        ((n + 1 : ℕ) : ACrisZero K p) * (M * U n) := by
      have hfac : ((n + 1 : ℕ) : ACrisZero K p) * (n.factorial : ACrisZero K p) *
          dpowZero (mu_mem_ker hε) (n + 1) = M ^ (n + 1) := by
        apply Subtype.ext
        simp only [Subalgebra.coe_mul, SubringClass.coe_natCast, coe_dpowZero, Subalgebra.coe_pow,
          hM, Subalgebra.coe_algebraMap]
        rw [← Nat.cast_mul, ← Nat.factorial_succ, factorial_mul_dpow]
      calc ((n + 1 : ℕ) : ACrisZero K p) * logTermZero (mu_mem_ker hε) n
          = (-1) ^ n * (((n + 1 : ℕ) : ACrisZero K p) * (n.factorial : ACrisZero K p) *
              dpowZero (mu_mem_ker hε) (n + 1)) := by rw [logTermZero]; ring
        _ = ((n + 1 : ℕ) : ACrisZero K p) * (M * U n) := by
          rw [hfac, mul_left_comm, hU n]; ring
    have e2 := congrArg (fun y : ACrisZero K p => (y : 𝔸)) e1
    simpa only [Subalgebra.coe_mul, SubringClass.coe_natCast] using e2

  have hsmall : ∀ j : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      algebraMap (ACrisZero K p) (ACris K p) (U n) ∈ 𝔭 ^ j := by
    intro j
    refine ⟨2 * (p - 1) * j + 3 * p, fun n hn => ?_⟩
    have hj := add_factorization_succ_le_div (p := p) hn
    have hle : j ≤ n / (p - 1) - (n + 1).factorization p := by omega
    simp only [U, map_mul, map_pow, map_natCast]
    refine Ideal.pow_le_pow_right hle (Ideal.mul_mem_right _ _ ?_)
    exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _
  obtain ⟨u, hu⟩ := exists_isAdicSum (I := 𝔭)
    (a := fun n => algebraMap (ACrisZero K p) (ACris K p) (U n)) hsmall
  have hMc : algebraMap (ACrisZero K p) (ACris K p) M =
      algebraMap (AInf K p) (ACris K p) (AInf.mu ε) := (AdicCompletion.algebraMap_apply _ _).symm
  have ht : periodT hε = algebraMap (AInf K p) (ACris K p) (AInf.mu ε) * u := by
    refine log_eq_of_isAdicSum ((hu.mul_left (algebraMap (ACrisZero K p) (ACris K p) M)).congr
      fun n => ?_) |>.trans ?_
    · rw [logTerm, hlog]; exact (map_mul _ _ _).symm
    · rw [hMc]
  refine ⟨u, Ideal.isUnit_of_sub_one_mem_jacobson_bot u ?_, ht⟩

  set J := (⊥ : Ideal (ACris K p)).jacobson
  have hMJ : algebraMap (ACrisZero K p) (ACris K p) M ∈ J := by
    refine mem_jacobson_of_pow_mem (m := p - 1) ?_
    rw [← map_pow, hc, map_mul, map_natCast]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hcJ : algebraMap (ACrisZero K p) (ACris K p) c ∈ J := by
    refine mem_jacobson_of_pow_mem (m := p) ?_
    rw [← map_pow]
    have := Ideal.mem_map_of_mem (algebraMap (ACrisZero K p) (ACris K p)) hcp
    rwa [Ideal.map_span, Set.image_singleton, map_natCast] at this
  have hU0 : U 0 = 1 := by
    have h0 := hw 0
    simp only [zero_add, Nat.cast_one, one_mul, Nat.factorization_one, Finsupp.coe_zero,
      Pi.zero_apply, pow_zero] at h0
    simp [U, V, h0]
  have hUJ : ∀ n : ℕ, 1 ≤ n → algebraMap (ACrisZero K p) (ACris K p) (U n) ∈ J := by
    intro n hn
    simp only [U, V, map_mul, map_pow, map_neg, map_one]
    rcases Nat.eq_zero_or_pos (n % (p - 1)) with hr | hr
    · have hq : 0 < n / (p - 1) := by
        have := Nat.mod_add_div n (p - 1)
        rcases Nat.eq_zero_or_pos (n / (p - 1)) with h | h
        · rw [h, hr, mul_zero, add_zero] at this; omega
        · exact h
      refine Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ?_))
      exact Ideal.pow_mem_of_mem _ hcJ _ hq
    · refine Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
        (Ideal.mul_mem_left _ _ ?_)))
      exact Ideal.pow_mem_of_mem _ hMJ _ hr
  have hsum : IsAdicSum 𝔭 (fun n => algebraMap (ACrisZero K p) (ACris K p) (U n) -
      if n = 0 then 1 else 0) (u - 1) := by
    have h1 : IsAdicSum 𝔭 (fun n : ℕ => if n = 0 then (1 : ACris K p) else 0) 1 := by
      have := isAdicSum_of_eq_zero (I := 𝔭) (a := fun n : ℕ => if n = 0 then (1 : ACris K p) else 0)
        (m := 1) fun n hn => by simp only [ite_eq_right_iff]; omega
      simpa using this
    exact hu.sub h1
  refine hsum.mem (k := 1) (by rw [pow_one]; exact IsAdicComplete.le_jacobson_bot _) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hU0]
  · rw [if_neg hn.ne', sub_zero]
    exact hUJ n hn

theorem mu_mem_span_periodT {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    algebraMap (AInf K p) (ACris K p) (AInf.mu ε) ∈ Ideal.span {periodT (K := K) hε} := by
  obtain ⟨u, hu, ht⟩ := exists_periodT_eq_mu_mul_unit hε hζ
  rw [Ideal.mem_span_singleton']
  exact ⟨↑hu.unit⁻¹, by rw [ht, mul_comm, mul_assoc, IsUnit.mul_val_inv, mul_one]⟩

theorem span_periodT_eq_span_mu {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    Ideal.span {periodT (K := K) hε} =
      Ideal.span {algebraMap (AInf K p) (ACris K p) (AInf.mu ε)} := by
  obtain ⟨u, hu, ht⟩ := exists_periodT_eq_mu_mul_unit hε hζ
  rw [ht, Ideal.span_singleton_mul_right_unit hu]

end ACris

end GroundTheory.PAdicHodge
