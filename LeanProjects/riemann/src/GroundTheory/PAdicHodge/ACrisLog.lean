import Mathlib
import GroundTheory.PAdicHodge.FactorizationFactorialLe
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open _root_.WittVector

section AdicSum

variable {R : Type*} [CommRing R] (I : Ideal R)

def IsAdicSum (a : ℕ → R) (s : R) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ M, N ≤ M → s - ∑ n ∈ Finset.range M, a n ∈ I ^ k

variable {I}

theorem sum_Ico_mem_of_forall {J : Ideal R} {a : ℕ → R} {N : ℕ} (h : ∀ n, N ≤ n → a n ∈ J)
    (M : ℕ) : ∑ n ∈ Finset.Ico N M, a n ∈ J :=
  Ideal.sum_mem _ fun n hn => h n (Finset.mem_Ico.1 hn).1

theorem IsAdicSum.unique [IsHausdorff I R] {a : ℕ → R} {s s' : R} (hs : IsAdicSum I a s)
    (hs' : IsAdicSum I a s') : s = s' := by
  rw [← sub_eq_zero]
  apply IsHausdorff.haus' (I := I)
  intro k
  obtain ⟨N, hN⟩ := hs k
  obtain ⟨N', hN'⟩ := hs' k
  have h := sub_mem (hN (max N N') (le_max_left _ _)) (hN' (max N N') (le_max_right _ _))
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  convert h using 1
  ring

theorem exists_isAdicSum [IsPrecomplete I R] {a : ℕ → R}
    (ha : ∀ k, ∃ N, ∀ n, N ≤ n → a n ∈ I ^ k) : ∃ s, IsAdicSum I a s := by
  choose g hg using ha
  set G : ℕ → ℕ := fun k => ∑ j ∈ Finset.range (k + 1), g j
  have hG : ∀ k, g k ≤ G k := fun k =>
    Finset.single_le_sum (f := g) (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ k)
  have hGm : Monotone G := fun m n hmn =>
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (Nat.succ_le_succ hmn))
  have hdiff : ∀ k M, G k ≤ M →
      ∑ n ∈ Finset.range M, a n - ∑ n ∈ Finset.range (G k), a n ∈ I ^ k := fun k M hM => by
    rw [← Finset.sum_range_add_sum_Ico _ hM, add_sub_cancel_left]
    exact sum_Ico_mem_of_forall (fun n hn => hg k n ((hG k).trans hn)) M
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) inferInstance
    (f := fun k => ∑ n ∈ Finset.range (G k), a n) (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have := hdiff m (G n) (hGm hmn)
      rw [← neg_sub]
      exact neg_mem this)
  refine ⟨L, fun k => ⟨G k, fun M hM => ?_⟩⟩
  have h1 := hL k
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  have h2 := hdiff k M hM
  have := add_mem (neg_mem h1) (neg_mem h2)
  convert this using 1
  ring

theorem IsAdicSum.add {a b : ℕ → R} {s t : R} (hs : IsAdicSum I a s) (ht : IsAdicSum I b t) :
    IsAdicSum I (fun n => a n + b n) (s + t) := fun k => by
  obtain ⟨N, hN⟩ := hs k
  obtain ⟨N', hN'⟩ := ht k
  refine ⟨max N N', fun M hM => ?_⟩
  have := add_mem (hN M (le_of_max_le_left hM)) (hN' M (le_of_max_le_right hM))
  rw [Finset.sum_add_distrib]
  convert this using 1
  ring

theorem IsAdicSum.mul_left (c : R) {a : ℕ → R} {s : R} (hs : IsAdicSum I a s) :
    IsAdicSum I (fun n => c * a n) (c * s) := fun k => by
  obtain ⟨N, hN⟩ := hs k
  refine ⟨N, fun M hM => ?_⟩
  rw [← Finset.mul_sum, ← mul_sub]
  exact Ideal.mul_mem_left _ c (hN M hM)

theorem IsAdicSum.neg {a : ℕ → R} {s : R} (hs : IsAdicSum I a s) :
    IsAdicSum I (fun n => -a n) (-s) := by
  simpa using hs.mul_left (-1)

theorem IsAdicSum.sub {a b : ℕ → R} {s t : R} (hs : IsAdicSum I a s) (ht : IsAdicSum I b t) :
    IsAdicSum I (fun n => a n - b n) (s - t) := by
  simpa [sub_eq_add_neg] using hs.add ht.neg

theorem IsAdicSum.congr {a b : ℕ → R} {s : R} (hs : IsAdicSum I a s) (h : ∀ n, a n = b n) :
    IsAdicSum I b s := by
  have : a = b := funext h
  rwa [← this]

theorem isAdicSum_of_eq_zero {a : ℕ → R} {m : ℕ} (h : ∀ n, m ≤ n → a n = 0) :
    IsAdicSum I a (∑ n ∈ Finset.range m, a n) := fun k => ⟨m, fun M hM => by
  rw [← Finset.sum_range_add_sum_Ico _ hM, Finset.sum_eq_zero (fun n hn => h n (Finset.mem_Ico.1 hn).1),
    add_zero, sub_self]
  exact zero_mem _⟩

theorem IsAdicSum.map {S : Type*} [CommRing S] {J : Ideal S} (f : R →+* S) (hf : I ≤ J.comap f)
    {a : ℕ → R} {s : R} (hs : IsAdicSum I a s) : IsAdicSum J (fun n => f (a n)) (f s) := fun k => by
  obtain ⟨N, hN⟩ := hs k
  refine ⟨N, fun M hM => ?_⟩
  rw [← map_sum, ← map_sub]
  exact (Ideal.pow_right_mono hf k).trans (Ideal.le_comap_pow f k) (hN M hM)

theorem IsAdicSum.mem {J : Ideal R} {k : ℕ} (hJ : I ^ k ≤ J) {a : ℕ → R} {s : R}
    (hs : IsAdicSum I a s) (ha : ∀ n, a n ∈ J) : s ∈ J := by
  obtain ⟨N, hN⟩ := hs k
  have := add_mem (hJ (hN N le_rfl)) (Ideal.sum_mem J (t := Finset.range N) fun n _ => ha n)
  rwa [sub_add_cancel] at this

end AdicSum

namespace ACris

section Log

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}

omit [IsPerfectoidField K p] in

theorem pow_dvd_factorial {k n : ℕ} (h : p * k ≤ n) : p ^ k ∣ n.factorial :=
  ((pow_dvd_pow p (by rw [padicValNat_factorial_mul]; omega)).trans pow_padicValNat_dvd).trans
    (Nat.factorial_dvd_factorial h)

theorem natCast_mem_pow {k n : ℕ} (h : p ^ k ∣ n) :
    (n : ACrisZero K p) ∈ Ideal.span {(p : ACrisZero K p)} ^ k := by
  obtain ⟨c, rfl⟩ := h
  rw [Nat.cast_mul, Nat.cast_pow, Ideal.span_singleton_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem map_span_p_pow (k : ℕ) :
    (Ideal.span {(p : ACrisZero K p)} ^ k).map (algebraMap (ACrisZero K p) (ACris K p)) = 𝔭 ^ k := by
  rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton, map_natCast]

theorem algebraMap_mem_pow {k : ℕ} {y : ACrisZero K p} (hy : y ∈ Ideal.span {(p : ACrisZero K p)} ^ k) :
    algebraMap (ACrisZero K p) (ACris K p) y ∈ 𝔭 ^ k := by
  rw [← map_span_p_pow]
  exact Ideal.mem_map_of_mem _ hy

theorem algebraMap_p_mem : algebraMap (ACrisZero K p) (ACris K p) (p : ACrisZero K p) ∈ 𝔭 := by
  simpa using algebraMap_mem_pow (k := 1) (y := (p : ACrisZero K p)) (by simpa using Ideal.mem_span_singleton_self _)

def dpowZero {x : AInf K p} (hx : x ∈ RingHom.ker θ) (n : ℕ) : ACrisZero K p :=
  ⟨dpow n x, dpow_mem hx n⟩

theorem coe_dpowZero {x : AInf K p} (hx : x ∈ RingHom.ker θ) (n : ℕ) :
    (dpowZero hx n : 𝔸) = dpow n x :=
  rfl

def logTermZero {x : AInf K p} (hx : x ∈ RingHom.ker θ) (n : ℕ) : ACrisZero K p :=
  (-1) ^ n * (n.factorial : ACrisZero K p) * dpowZero hx (n + 1)

def logTerm {x : AInf K p} (hx : x ∈ RingHom.ker θ) (n : ℕ) : ACris K p :=
  algebraMap (ACrisZero K p) (ACris K p) (logTermZero hx n)

theorem logTermZero_mem {x : AInf K p} (hx : x ∈ RingHom.ker θ) {k n : ℕ} (h : p * k ≤ n) :
    logTermZero hx n ∈ Ideal.span {(p : ACrisZero K p)} ^ k :=
  Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (natCast_mem_pow (pow_dvd_factorial h)))

theorem logTerm_mem {x : AInf K p} (hx : x ∈ RingHom.ker θ) {k n : ℕ} (h : p * k ≤ n) :
    logTerm hx n ∈ 𝔭 ^ k :=
  algebraMap_mem_pow (logTermZero_mem hx h)

theorem exists_isAdicSum_logTerm {x : AInf K p} (hx : x ∈ RingHom.ker θ) :
    ∃ s, IsAdicSum 𝔭 (logTerm hx) s :=
  exists_isAdicSum fun k => ⟨p * k, fun _ hn => logTerm_mem hx hn⟩

def log {x : AInf K p} (hx : x ∈ RingHom.ker θ) : ACris K p :=
  (exists_isAdicSum_logTerm hx).choose

theorem isAdicSum_log {x : AInf K p} (hx : x ∈ RingHom.ker θ) :
    IsAdicSum 𝔭 (logTerm hx) (log hx) :=
  (exists_isAdicSum_logTerm hx).choose_spec

theorem log_eq_of_isAdicSum {x : AInf K p} {hx : x ∈ RingHom.ker θ} {s : ACris K p}
    (hs : IsAdicSum 𝔭 (logTerm hx) s) : log hx = s :=
  (isAdicSum_log hx).unique hs

theorem mu_mem_ker {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) : AInf.mu (K := K) ε ∈ RingHom.ker θ :=
  RingHom.mem_ker.2 (AInf.fontaineTheta_mu hε)

def periodT {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) : ACris K p :=
  log (mu_mem_ker hε)

section Theta

variable [CharZero K]

theorem theta_logTerm {x : AInf K p} (hx : x ∈ RingHom.ker θ) (n : ℕ) :
    theta K p (logTerm hx n) = 0 := by
  rw [logTerm, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    theta_of, logTermZero, map_mul, dpowZero, thetaZero_dpow hx n.succ_ne_zero, mul_zero]

theorem theta_log {x : AInf K p} (hx : x ∈ RingHom.ker θ) : theta K p (log hx) = 0 := by
  have hle : 𝔭 ≤ (Ideal.span {(p : 𝒪)}).comap (theta K p) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_span_singleton_self _
  have h := (isAdicSum_log hx).map (theta K p) hle
  have h0 : IsAdicSum (Ideal.span {(p : 𝒪)}) (fun n => theta K p (logTerm hx n)) 0 := by
    have := isAdicSum_of_eq_zero (I := Ideal.span {(p : 𝒪)})
      (a := fun n => theta K p (logTerm hx n)) (m := 0) (fun n _ => theta_logTerm hx n)
    simpa using this
  exact h.unique h0

theorem theta_periodT {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) : theta K p (periodT hε) = 0 :=
  theta_log _

end Theta

end Log

end ACris

namespace ACris

section Divisibility

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "𝔸" => Localization.Away (p : AInf K p)
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)
local notation "𝔭" => Ideal.span {(p : ACris K p)}

theorem xi_sub_pow_mem (ε : 𝒪♭) :
    AInf.xi (K := K) ε - ((φ).symm (AInf.mu ε)) ^ (p - 1) ∈ Ideal.span {(p : AInf K p)} := by
  haveI := IsPerfectoidField.isDomain_preTilt (K := K) p
  rw [mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply,
    AInf.frobeniusEquiv_symm_mu, AInf.xi]
  simp only [map_sub, map_sum, map_pow, map_one, WittVector.constantCoeff_apply,
    teichmuller_coeff_zero]
  set e := (_root_.frobeniusEquiv 𝒪♭ p).symm ε
  have h1 := geom_sum_mul e p
  have h2 : (e - 1) ^ p = e ^ p - 1 := by rw [sub_pow_char, one_pow]
  by_cases he : e - 1 = 0
  · rw [he, zero_pow (Nat.sub_ne_zero_of_lt hp.out.one_lt), sub_zero, sub_eq_zero.1 he]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact CharP.cast_eq_zero _ p
  · rw [sub_eq_zero]
    apply mul_right_cancel₀ he
    rw [h1, ← h2, ← pow_succ, Nat.sub_add_cancel hp.out.one_le]

theorem exists_mu_pow_eq {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    ∃ c : ACrisZero K p,
      (algebraMap (AInf K p) (ACrisZero K p) (AInf.mu ε)) ^ (p - 1) = (p : ACrisZero K p) * c := by
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
  refine ⟨((p - 1).factorial : ACrisZero K p) * ⟨dpow p ξ, dpow_mem hξ p⟩ -
    algebraMap (AInf K p) (ACrisZero K p) (a * ξ ^ (p - 1)), ?_⟩
  apply Subtype.ext
  simp only [Subalgebra.coe_pow, Subalgebra.coe_mul, Subalgebra.coe_sub, SubringClass.coe_natCast,
    Subalgebra.coe_algebraMap]
  rw [← map_pow, hW, map_sub, map_pow, ← factorial_mul_dpow, map_mul, map_natCast,
    ← Nat.mul_factorial_pred hp.out.ne_zero, Nat.cast_mul]
  ring

theorem logTermZero_eq_mul_of_lt {x : AInf K p} (hx : x ∈ RingHom.ker θ) {n : ℕ} (hn : n + 1 < p) :
    ∃ w : ACrisZero K p, logTermZero hx n = algebraMap (AInf K p) (ACrisZero K p) x * w := by
  have hcop : (n + 1).Coprime p := (Nat.coprime_of_lt_prime (Nat.succ_ne_zero n) hn hp.out).symm
  have hu := WittVector.isUnit_natCast_of_coprime (R := 𝒪♭) hcop
  refine ⟨(-1) ^ n * algebraMap (AInf K p) (ACrisZero K p) (x ^ n * ↑hu.unit⁻¹), ?_⟩
  apply Subtype.ext
  simp only [logTermZero, Subalgebra.coe_pow, Subalgebra.coe_mul, Subalgebra.coe_neg,
    Subalgebra.coe_one, SubringClass.coe_natCast, Subalgebra.coe_algebraMap, coe_dpowZero]
  have h1 := isUnit_natCast (K := K) (p := p) (Nat.succ_ne_zero n)
  apply h1.mul_left_cancel
  have h2 : ((n + 1 : ℕ) : 𝔸) * (n.factorial : 𝔸) = ((n + 1).factorial : 𝔸) := by
    rw [← Nat.cast_mul, Nat.factorial_succ]
  have h3 : ((n + 1 : ℕ) : 𝔸) * algebraMap (AInf K p) 𝔸 ↑hu.unit⁻¹ = 1 := by
    rw [← map_natCast (algebraMap (AInf K p) 𝔸), ← map_mul, IsUnit.mul_val_inv, map_one]
  calc ((n + 1 : ℕ) : 𝔸) * ((-1) ^ n * (n.factorial : 𝔸) * dpow (n + 1) x)
      = (-1) ^ n * (((n + 1 : ℕ) : 𝔸) * n.factorial * dpow (n + 1) x) := by ring
    _ = (-1) ^ n * algebraMap (AInf K p) 𝔸 x ^ (n + 1) := by
        rw [h2, factorial_mul_dpow]
    _ = ((n + 1 : ℕ) : 𝔸) * (algebraMap (AInf K p) 𝔸 x *
        ((-1) ^ n * algebraMap (AInf K p) 𝔸 (x ^ n * ↑hu.unit⁻¹))) := by
        rw [map_mul, map_pow]
        linear_combination (-1) ^ n * algebraMap (AInf K p) 𝔸 x ^ (n + 1) * h3.symm

theorem logTermZero_pred_eq {x : AInf K p} (hx : x ∈ RingHom.ker θ) {c : ACrisZero K p}
    (hc : (algebraMap (AInf K p) (ACrisZero K p) x) ^ (p - 1) = (p : ACrisZero K p) * c) :
    logTermZero hx (p - 1) = algebraMap (AInf K p) (ACrisZero K p) x * ((-1) ^ (p - 1) * c) := by
  have hcc := congrArg (fun y : ACrisZero K p => (y : 𝔸)) hc
  apply Subtype.ext
  simp only [logTermZero, Subalgebra.coe_pow, Subalgebra.coe_mul, Subalgebra.coe_neg,
    Subalgebra.coe_one, SubringClass.coe_natCast, Subalgebra.coe_algebraMap, coe_dpowZero] at hcc ⊢
  have h1 := isUnit_natCast (K := K) (p := p) hp.out.ne_zero
  apply h1.mul_left_cancel
  rw [Nat.sub_add_cancel hp.out.one_le]
  have h2 : (p : 𝔸) * ((p - 1).factorial : 𝔸) = (p.factorial : 𝔸) := by
    rw [← Nat.cast_mul, Nat.mul_factorial_pred hp.out.ne_zero]
  calc (p : 𝔸) * ((-1) ^ (p - 1) * ((p - 1).factorial : 𝔸) * dpow p x)
      = (-1) ^ (p - 1) * ((p : 𝔸) * (p - 1).factorial * dpow p x) := by ring
    _ = (-1) ^ (p - 1) * (algebraMap (AInf K p) 𝔸 x * algebraMap (AInf K p) 𝔸 x ^ (p - 1)) := by
        rw [h2, factorial_mul_dpow, ← pow_succ', Nat.sub_add_cancel hp.out.one_le]
    _ = (p : 𝔸) * (algebraMap (AInf K p) 𝔸 x * ((-1) ^ (p - 1) * (c : 𝔸))) := by
        rw [hcc]; ring

set_option maxHeartbeats 2000000 in

theorem log_pow_mem {x : AInf K p} (hx : x ∈ RingHom.ker θ) {c : ACrisZero K p}
    (hc : (algebraMap (AInf K p) (ACrisZero K p) x) ^ (p - 1) = (p : ACrisZero K p) * c) :
    log hx ^ (p - 1) ∈ 𝔭 := by
  have hsmall : ∀ n, ∃ w : ACrisZero K p, n < p →
      logTermZero hx n = algebraMap (AInf K p) (ACrisZero K p) x * w := fun n => by
    by_cases hn' : n + 1 < p
    · obtain ⟨w, hw⟩ := logTermZero_eq_mul_of_lt hx hn'
      exact ⟨w, fun _ => hw⟩
    · by_cases hn : n < p
      · have hnp : n = p - 1 := by omega
        subst hnp
        exact ⟨_, fun _ => logTermZero_pred_eq hx hc⟩
      · exact ⟨0, fun h => absurd h hn⟩
  choose w hw using hsmall
  let b0 : ℕ → ACrisZero K p := fun n => if n < p then 0 else
    (-1) ^ n * ((n.factorial / p : ℕ) : ACrisZero K p) * dpowZero hx (n + 1)
  have hbmem : ∀ k n, p * (k + 1) ≤ n →
      algebraMap (ACrisZero K p) (ACris K p) (b0 n) ∈ 𝔭 ^ k := fun k n hn => by
    have hnp : ¬ n < p := by nlinarith [hp.out.one_lt]
    refine algebraMap_mem_pow ?_
    simp only [b0, hnp, if_false]
    refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (natCast_mem_pow ?_))
    obtain ⟨d, hd⟩ := pow_dvd_factorial (p := p) hn
    rw [hd, pow_succ', mul_assoc, Nat.mul_div_cancel_left _ hp.out.pos]
    exact Dvd.intro d rfl
  obtain ⟨s, hs⟩ := exists_isAdicSum (I := 𝔭)
    (a := fun n => algebraMap (ACrisZero K p) (ACris K p) (b0 n)) fun k => ⟨p * (k + 1), hbmem k⟩
  let a0 : ℕ → ACrisZero K p := fun n => if n < p then logTermZero hx n else 0
  have hsplit : ∀ n, a0 n + (p : ACrisZero K p) * b0 n = logTermZero hx n := fun n => by
    by_cases hn : n < p
    · simp [a0, b0, hn]
    · simp only [a0, b0, hn, if_false, zero_add, logTermZero]
      have hdvd : p ∣ n.factorial := Nat.dvd_factorial hp.out.pos (not_lt.1 hn)
      conv_rhs => rw [← Nat.mul_div_cancel' hdvd, Nat.cast_mul]
      ring
  have hsplit' : ∀ n, algebraMap (ACrisZero K p) (ACris K p) (a0 n) +
      algebraMap (ACrisZero K p) (ACris K p) (p : ACrisZero K p) *
        algebraMap (ACrisZero K p) (ACris K p) (b0 n) = logTerm hx n := fun n => by
    rw [logTerm, ← hsplit n, map_add, map_mul]
  have ha'sum : IsAdicSum 𝔭 (fun n => algebraMap (ACrisZero K p) (ACris K p) (a0 n))
      (∑ n ∈ Finset.range p, algebraMap (ACrisZero K p) (ACris K p) (a0 n)) :=
    isAdicSum_of_eq_zero fun n hn => by simp [a0, not_lt.2 hn]
  have ht : log hx = ∑ n ∈ Finset.range p, algebraMap (ACrisZero K p) (ACris K p) (a0 n) +
      algebraMap (ACrisZero K p) (ACris K p) (p : ACrisZero K p) * s :=
    log_eq_of_isAdicSum ((ha'sum.add (hs.mul_left _)).congr hsplit')
  have hfin : ∑ n ∈ Finset.range p, algebraMap (ACrisZero K p) (ACris K p) (a0 n) =
      algebraMap (ACrisZero K p) (ACris K p) (algebraMap (AInf K p) (ACrisZero K p) x) *
        ∑ n ∈ Finset.range p, algebraMap (ACrisZero K p) (ACris K p) (w n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' := Finset.mem_range.1 hn
    simp only [a0, hn', if_true]
    rw [hw n hn', map_mul]
  have hp0 : Ideal.Quotient.mk 𝔭 (algebraMap (ACrisZero K p) (ACris K p) (p : ACrisZero K p)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 algebraMap_p_mem
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, ht, hfin, map_add, map_mul (Ideal.Quotient.mk 𝔭)
    (algebraMap (ACrisZero K p) (ACris K p) (p : ACrisZero K p)), hp0, zero_mul, add_zero, map_mul,
    mul_pow, ← map_pow, ← map_pow, hc, map_mul, map_mul, hp0, zero_mul, zero_mul]

theorem periodT_pow_mem {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    periodT hε ^ (p - 1) ∈ 𝔭 := by
  obtain ⟨c, hc⟩ := exists_mu_pow_eq hε hζ
  exact log_pow_mem _ hc

end Divisibility

end ACris

end GroundTheory.PAdicHodge
