import Mathlib
import GroundTheory.PAdicHodge.LogMul
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.CompanionTheory.LogAlgPf

open Polynomial

section Ring

variable {S : Type*} [CommRing S] [Algebra ℚ S]

def dv (k : ℕ) (x : S) : S := ((k.factorial : ℚ)⁻¹) • x ^ k

def DP (T : Subring S) (x : S) : Prop := ∀ k, dv k x ∈ T

theorem dv_one (x : S) : dv 1 x = x := by simp [dv]

theorem dv_add (k : ℕ) (x y : S) :
    dv k (x + y) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, dv p.1 x * dv p.2 y := by
  unfold dv
  rw [(Commute.all x y).add_pow', Finset.smul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨i, j⟩ := p
  have hk : i + j = k := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  subst hk
  simp only
  rw [smul_mul_smul_comm, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  have h := Nat.add_choose_mul_factorial_mul_factorial i j
  have h' : (((i + j).choose i : ℕ) : ℚ) * (i.factorial : ℚ) * (j.factorial : ℚ) = ((i + j).factorial : ℚ) := by
    rw [Nat.choose_symm_add]; exact_mod_cast h
  have hi : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have hj : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hij : ((i + j).factorial : ℚ) ≠ 0 := by exact_mod_cast (i + j).factorial_ne_zero
  rw [← h']
  rw [← h'] at hij
  have hc : (((i + j).choose i : ℕ) : ℚ) ≠ 0 := fun h0 => hij (by rw [h0]; ring)
  field_simp

theorem dv_mul (k : ℕ) (x y : S) : dv k (x * y) = x ^ k * dv k y := by
  unfold dv
  rw [mul_pow, mul_smul_comm]

theorem DP.mem {T : Subring S} {x : S} (h : DP T x) : x ∈ T := by
  have := h 1
  rwa [dv_one] at this

theorem DP.add {T : Subring S} {x y : S} (hx : DP T x) (hy : DP T y) : DP T (x + y) := fun k => by
  rw [dv_add]
  exact T.sum_mem fun p _ => T.mul_mem (hx _) (hy _)

theorem DP.mul {T : Subring S} {x y : S} (hx : DP T x) (hy : DP T y) : DP T (x * y) := fun k => by
  rw [dv_mul]
  exact T.mul_mem (T.pow_mem hx.mem _) (hy _)

theorem DP.comb {T : Subring S} {x y : S} (hx : DP T x) (hy : DP T y) : DP T (x + y + x * y) :=
  (hx.add hy).add (hx.mul hy)

def large₂ (N : ℕ) (u : S) : S :=
  ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : S) * dv (k + 1) u

def FF (N : ℕ) (x y : S) : S := large₂ N (x + y + x * y) - large₂ N x - large₂ N y

theorem map_dv {S' : Type*} [CommRing S'] [Algebra ℚ S'] (f : S →+* S') (k : ℕ) (x : S) :
    f (dv k x) = dv k (f x) := by
  unfold dv
  rw [map_rat_smul, map_pow]

theorem map_Lg {S' : Type*} [CommRing S'] [Algebra ℚ S'] (f : S →+* S') (N : ℕ) (x : S) :
    f (large₂ N x) = large₂ N (f x) := by
  unfold large₂
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, map_pow, map_neg, map_one, map_natCast, map_dv]

theorem map_FF {S' : Type*} [CommRing S'] [Algebra ℚ S'] (f : S →+* S') (N : ℕ) (x y : S) :
    f (FF N x y) = FF N (f x) (f y) := by
  unfold FF
  rw [map_sub, map_sub, map_Lg, map_Lg, map_Lg, map_add, map_add, map_mul]

theorem Lg_sub {T : Subring S} {u : S} (h : DP T u) {N M : ℕ} (hNM : N ≤ M) :
    ∃ c ∈ T, large₂ M u - large₂ N u = (N.factorial : S) * c := by
  induction M, hNM using Nat.le_induction with
  | base => exact ⟨0, T.zero_mem, by simp⟩
  | succ M hM ih =>
    obtain ⟨c, hc, e⟩ := ih
    obtain ⟨d, hd⟩ := Nat.factorial_dvd_factorial hM
    refine ⟨c + (-1) ^ M * (d : S) * dv (M + 1) u,
      T.add_mem hc (T.mul_mem (T.mul_mem (T.pow_mem (T.neg_mem T.one_mem) _) (natCast_mem T d)) (h _)), ?_⟩
    have e2 : large₂ (M + 1) u = large₂ M u + (-1) ^ M * (M.factorial : S) * dv (M + 1) u := by
      unfold large₂
      rw [Finset.sum_range_succ]
    rw [e2, hd]
    push_cast
    linear_combination e

theorem FF_sub {T : Subring S} {x y : S} (hx : DP T x) (hy : DP T y) {N M : ℕ} (hNM : N ≤ M) :
    ∃ c ∈ T, FF M x y - FF N x y = (N.factorial : S) * c := by
  obtain ⟨a, ha, ea⟩ := Lg_sub (hx.comb hy) hNM
  obtain ⟨b, hb, eb⟩ := Lg_sub hx hNM
  obtain ⟨c, hc, ec⟩ := Lg_sub hy hNM
  refine ⟨a - b - c, T.sub_mem (T.sub_mem ha hb) hc, ?_⟩
  unfold FF
  linear_combination ea - eb - ec

theorem Lg_eq_truncEval {n : ℕ} (s : S) (hs : s ^ (n + 1) = 0) :
    truncEval s hs (PowerSeries.log ℚ) = large₂ n s := by
  rw [truncEval_eq_sum, Finset.sum_range_succ']
  simp only [PowerSeries.coeff_log]
  rw [if_pos trivial, map_zero, zero_mul, add_zero]
  unfold large₂
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [if_neg (Nat.succ_ne_zero k)]
  unfold dv
  rw [Algebra.smul_def, ← mul_assoc]
  congr 1
  have e : (-1 : S) ^ k * (k.factorial : S) * algebraMap ℚ S (((k + 1).factorial : ℚ)⁻¹) =
      algebraMap ℚ S ((-1) ^ k * (k.factorial : ℚ) * ((k + 1).factorial : ℚ)⁻¹) := by
    rw [map_mul, map_mul, map_pow, map_neg, map_one, map_natCast]
  rw [e]
  congr 1
  have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  rw [Nat.factorial_succ]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  push_cast
  field_simp
  ring

theorem pow_dvd_FF {R : Type*} [CommRing R] [Algebra ℚ R] {t a b : R} (ha : t ∣ a) (hb : t ∣ b)
    (M : ℕ) : t ^ (M + 1) ∣ FF M a b := by
  set J : Ideal R := Ideal.span {t ^ (M + 1)} with hJ
  have hpow : ∀ u : R, t ∣ u → (Ideal.Quotient.mk J u) ^ (M + 1) = 0 := by
    intro u hu
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, hJ, Ideal.mem_span_singleton]
    exact pow_dvd_pow_of_dvd hu _
  have hz : t ∣ a + b + a * b := dvd_add (dvd_add ha hb) (ha.mul_right b)
  have key := truncEval_log_mul (hpow a ha) (hpow b hb) (hpow _ hz) (by
    rw [map_add, map_add, map_mul]; ring)
  rw [Lg_eq_truncEval, Lg_eq_truncEval, Lg_eq_truncEval, ← map_Lg, ← map_Lg, ← map_Lg, ← map_add,
    Ideal.Quotient.eq] at key
  have : FF M a b ∈ J := by
    have e : FF M a b = large₂ M (a + b + a * b) - (large₂ M a + large₂ M b) := by unfold FF; ring
    rw [e]; exact key
  rwa [hJ, Ideal.mem_span_singleton] at this

end Ring

section Poly

variable {S : Type*} [CommRing S] [Algebra ℚ S]

def TX (T : Subring S) : Subring S[X] where
  carrier := {p | ∀ n, p.coeff n ∈ T}
  mul_mem' hp hq n := by
    rw [coeff_mul]
    exact T.sum_mem fun c _ => T.mul_mem (hp _) (hq _)
  one_mem' n := by
    rw [coeff_one]
    split_ifs
    exacts [T.one_mem, T.zero_mem]
  add_mem' hp hq n := by
    rw [coeff_add]
    exact T.add_mem (hp n) (hq n)
  zero_mem' n := by
    rw [coeff_zero]
    exact T.zero_mem
  neg_mem' hp n := by
    rw [coeff_neg]
    exact T.neg_mem (hp n)

theorem mem_TX {T : Subring S} {p : S[X]} : p ∈ TX T ↔ ∀ n, p.coeff n ∈ T := Iff.rfl

theorem dv_CX (k : ℕ) (x : S) : dv k (C x * X : S[X]) = C (dv k x) * X ^ k := by
  unfold dv
  rw [mul_pow, ← C_pow, ← smul_C, smul_mul_assoc]

theorem DP_CX {T : Subring S} {x : S} (hx : DP T x) : DP (TX T) (C x * X : S[X]) := fun k n => by
  rw [dv_CX, coeff_C_mul, coeff_X_pow]
  split_ifs
  · rw [mul_one]; exact hx k
  · rw [mul_zero]; exact T.zero_mem

theorem natDegree_Lg_le {u : S[X]} {d : ℕ} (hu : u.natDegree ≤ d) (N : ℕ) :
    (large₂ N u).natDegree ≤ d * N := by
  unfold large₂
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  have e : (-1 : S[X]) ^ k * (k.factorial : S[X]) * dv (k + 1) u =
      C ((-1) ^ k * (k.factorial : S) * algebraMap ℚ S (((k + 1).factorial : ℚ)⁻¹)) * u ^ (k + 1) := by
    unfold dv
    rw [Algebra.smul_def, Polynomial.algebraMap_apply, map_mul, map_mul, map_pow, map_neg, map_one,
      map_natCast]
    ring
  rw [e]
  refine (natDegree_C_mul_le _ _).trans ((natDegree_pow_le).trans ?_)
  have hk' : k + 1 ≤ N := Finset.mem_range.1 hk
  calc (k + 1) * u.natDegree ≤ N * d := Nat.mul_le_mul hk' hu
    _ = d * N := Nat.mul_comm _ _

theorem natDegree_FF_le (x y : S) (N : ℕ) :
    (FF N (C x * X : S[X]) (C y * X)).natDegree ≤ 2 * N := by
  have hx : ∀ s : S, (C s * X : S[X]).natDegree ≤ 1 := fun s => (natDegree_C_mul_le _ _).trans natDegree_X_le
  have hz : (C x * X + C y * X + (C x * X) * (C y * X) : S[X]).natDegree ≤ 2 := by
    refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ((hx x).trans (by norm_num))
      ((hx y).trans (by norm_num))) (natDegree_mul_le.trans ?_)
    have := hx x
    have := hx y
    omega
  have h1 := natDegree_Lg_le hz N
  have h2 := natDegree_Lg_le (hx x) N
  have h3 := natDegree_Lg_le (hx y) N
  unfold FF
  refine (natDegree_sub_le _ _).trans (max_le ((natDegree_sub_le _ _).trans (max_le h1 ?_)) ?_) <;> omega

theorem FF_mem {T : Subring S} {x y : S} (hx : DP T x) (hy : DP T y) (N : ℕ) :
    ∃ c ∈ T, FF N x y = (N.factorial : S) * c := by
  obtain ⟨c, hc, e⟩ := FF_sub (DP_CX hx) (DP_CX hy) (show N ≤ 2 * N by omega)
  have hd : (X : S[X]) ^ (2 * N + 1) ∣ FF (2 * N) (C x * X) (C y * X) :=
    pow_dvd_FF (dvd_mul_left _ _) (dvd_mul_left _ _) _
  have hdeg : (FF N (C x * X : S[X]) (C y * X)).natDegree < 2 * N + 1 :=
    Nat.lt_succ_of_le (natDegree_FF_le x y N)
  have hcoef : ∀ i ∈ Finset.range (2 * N + 1),
      (FF N (C x * X : S[X]) (C y * X)).coeff i * 1 ^ i = (N.factorial : S) * (-(c.coeff i)) := by
    intro i hi
    have h0 := X_pow_dvd_iff.1 hd i (Finset.mem_range.1 hi)
    have h1 := congrArg (fun p : S[X] => p.coeff i) e
    simp only [coeff_sub, coeff_natCast_mul, h0] at h1
    rw [one_pow, mul_one]
    linear_combination -h1
  refine ⟨∑ i ∈ Finset.range (2 * N + 1), -(c.coeff i),
    T.sum_mem fun i _ => T.neg_mem (hc i), ?_⟩
  have hev : FF N x y = eval 1 (FF N (C x * X : S[X]) (C y * X)) := by
    have := map_FF (evalRingHom (1 : S)) N (C x * X : S[X]) (C y * X)
    simpa using this.symm
  rw [hev, eval_eq_sum_range' hdeg, Finset.sum_congr rfl hcoef, Finset.mul_sum]

end Poly

theorem logAlg : CrystallineSemistableComparison.E.LogAlg := by
  intro S _ _ T γ hγ x y hx hy
  have hγ' : γ = dv := by
    funext k u
    exact hγ k u
  subst hγ'
  refine ⟨DP.comb hx hy, fun N => ?_⟩
  obtain ⟨c, hc, e⟩ := FF_mem (T := T) hx hy N
  refine ⟨c, hc, ?_⟩
  change large₂ N (x + y + x * y) = large₂ N x + large₂ N y + _
  unfold FF at e
  linear_combination e

end GlobalTheory.CompanionTheory.LogAlgPf
