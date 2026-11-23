import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open Polynomial Module Finset

namespace SemilinearResidue

section Poly

variable {k : Type*} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]

include hp in

theorem coeff_pow_prime_pow (f : k[X]) (e n : ℕ) :
    (f ^ p ^ e).coeff n = if p ^ e ∣ n then f.coeff (n / p ^ e) ^ p ^ e else 0 := by
  have : ExpChar k p := ExpChar.prime hp.out
  rw [← map_iterateFrobenius_expand p f e, coeff_map, coeff_expand (pow_pos hp.out.pos e)]
  split_ifs <;> simp [iterateFrobenius_def, hp.out.ne_zero]

noncomputable def recPoly (q : ℕ) (c : ℕ → k) (ε : k) : ℕ → k[X]
  | 0 => C (c 0) * X ^ q - C ε
  | i + 1 => recPoly q c ε i ^ q + C (c (i + 1)) * X ^ q

omit [CharP k p] in
include hp in
theorem two_le_pow {e : ℕ} (he : 0 < e) : 2 ≤ p ^ e :=
  calc 2 ≤ p := hp.out.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ e := Nat.pow_le_pow_right hp.out.pos he

variable {e : ℕ}

theorem recPoly_coeff_one (he : 0 < e) (c : ℕ → k) (ε : k) :
    ∀ i, (recPoly (p ^ e) c ε i).coeff 1 = 0 := by
  have h2 := two_le_pow (p := p) he
  have hq1 : (1 : ℕ) ≠ p ^ e := by omega
  have hnd : ¬ p ^ e ∣ 1 := fun h => by have := Nat.le_of_dvd one_pos h; omega
  intro i
  cases i with
  | zero => simp [recPoly, coeff_C_mul, coeff_X_pow, hq1]
  | succ i => simp [recPoly, coeff_C_mul, coeff_pow_prime_pow, hnd]

theorem recPoly_coeff_zero (c : ℕ → k) : ∀ i, (recPoly (p ^ e) c 0 i).coeff 0 = 0 := by
  have hq0 : (0 : ℕ) ≠ p ^ e := (pow_pos hp.out.pos e).ne
  intro i
  induction i with
  | zero => simp [recPoly, coeff_X_pow, hq0]
  | succ i ih =>
    simp [recPoly, coeff_pow_prime_pow, ih, hp.out.ne_zero]

theorem recPoly_coeff_q (he : 0 < e) (c : ℕ → k) (ε : k) :
    ∀ j, (recPoly (p ^ e) c ε j).coeff (p ^ e) = c j := by
  have h2 := two_le_pow (p := p) he
  have hq0 : p ^ e ≠ 0 := by omega
  intro j
  cases j with
  | zero => simp [recPoly, coeff_C_mul, coeff_X_pow, coeff_C, hp.out.ne_zero]
  | succ j =>
    simp [recPoly, coeff_C_mul, coeff_pow_prime_pow, Nat.div_self (by omega : 0 < p ^ e),
      recPoly_coeff_one he, hp.out.ne_zero]

theorem recPoly_coeff_lead (he : 0 < e) (c : ℕ → k) (ε : k) (j : ℕ) :
    ∀ t, (recPoly (p ^ e) c ε (j + t)).coeff ((p ^ e) ^ (t + 1)) = c j ^ (p ^ e) ^ t := by
  have h2 := two_le_pow (p := p) he
  intro t
  induction t with
  | zero => simpa using recPoly_coeff_q he c ε j
  | succ t ih =>
    have hne : (p ^ e) ^ (t + 1 + 1) ≠ p ^ e := by
      intro h
      have : (p ^ e) ^ (t + 1 + 1) = p ^ e * (p ^ e) ^ (t + 1) := by ring
      have h3 : 2 ≤ (p ^ e) ^ (t + 1) := le_trans h2 (Nat.le_self_pow (by omega) _)
      nlinarith
    have hdvd : p ^ e ∣ (p ^ e) ^ (t + 1 + 1) := dvd_pow_self _ (by omega)
    have hdiv : (p ^ e) ^ (t + 1 + 1) / p ^ e = (p ^ e) ^ (t + 1) := by
      rw [pow_succ, Nat.mul_div_cancel _ (by omega)]
    rw [show j + (t + 1) = (j + t) + 1 by ring, recPoly, coeff_add, coeff_pow_prime_pow,
      if_pos hdvd, hdiv, ih, coeff_C_mul, coeff_X_pow, if_neg hne, mul_zero, add_zero, ← pow_mul,
      pow_succ]

end Poly

section Vec

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem linearIndependent_of_notMem_span (v : ℕ → V) : ∀ m : ℕ,
    (∀ j < m, v j ∉ Submodule.span k (Set.range (fun i : Fin j => v i))) →
      LinearIndependent k (fun i : Fin m => v i)
  | 0, _ => linearIndependent_empty_type
  | m + 1, h => by
    have ih := linearIndependent_of_notMem_span v m (fun j hj => h j (by omega))
    have : (fun i : Fin (m + 1) => v i) = Fin.snoc (fun i : Fin m => v i) (v m) := by
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
    rw [this]
    exact linearIndependent_finSnoc.mpr ⟨ih, h m (by omega)⟩

variable (k) in

theorem exists_rel [FiniteDimensional k V] (v : ℕ → V) :
    ∃ m, (∃ c : ℕ → k, v m = ∑ i ∈ range m, c i • v i) ∧
      LinearIndependent k (fun i : Fin m => v i) := by
  classical
  let P : ℕ → Prop := fun j => v j ∈ Submodule.span k (Set.range (fun i : Fin j => v i))
  have hex : ∃ j, P j := by
    by_contra hcon
    push Not at hcon
    have li := linearIndependent_of_notMem_span v (finrank k V + 1) (fun j _ => hcon j)
    have := li.fintype_card_le_finrank
    simp at this
  refine ⟨Nat.find hex, ?_, linearIndependent_of_notMem_span v _ (fun j hj => Nat.find_min hex hj)⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp (Nat.find_spec hex)
  refine ⟨fun i => if h : i < Nat.find hex then c ⟨i, h⟩ else 0, ?_⟩
  rw [← hc, Finset.sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [i.2]

variable {p : ℕ} [hp : Fact p.Prime] [CharP k p] {e : ℕ} {φ : V →+ V}

omit hp [CharP k p] in
theorem solve_of_root (hφ : ∀ (c : k) (x : V), φ (c • x) = c ^ p ^ e • φ x) (z : V) (n : ℕ)
    (c : ℕ → k) (hrel : (⇑φ)^[n + 1] z = ∑ i ∈ range (n + 1), c i • (⇑φ)^[i] z) (ε y : k)
    (hy : (recPoly (p ^ e) c ε n).eval y = y) :
    φ (∑ i ∈ range (n + 1), (recPoly (p ^ e) c ε i).eval y • (⇑φ)^[i] z) =
      (∑ i ∈ range (n + 1), (recPoly (p ^ e) c ε i).eval y • (⇑φ)^[i] z) + ε • z := by
  have hit : ∀ i, φ ((⇑φ)^[i] z) = (⇑φ)^[i + 1] z := fun i =>
    (Function.iterate_succ_apply' _ _ _).symm
  rw [map_sum]
  simp_rw [hφ, hit]
  rw [Finset.sum_range_succ, hy, hrel, Finset.smul_sum, Finset.sum_range_succ' _ n,
    Finset.sum_range_succ' (fun i => (recPoly (p ^ e) c ε i).eval y • (⇑φ)^[i] z) n]
  simp only [recPoly, eval_add, eval_pow, eval_mul, eval_C, eval_X, eval_sub,
    Function.iterate_zero, id, smul_smul, add_smul, sub_smul, Finset.sum_add_distrib]
  simp only [mul_comm (y ^ p ^ e)]
  abel

theorem exists_sub_eq [IsAlgClosed k] [FiniteDimensional k V] (he : 0 < e)
    (hφ : ∀ (c : k) (x : V), φ (c • x) = c ^ p ^ e • φ x) (z : V) : ∃ x, φ x - x = z := by
  obtain ⟨m, ⟨c, hrel⟩, -⟩ := exists_rel k (fun i => (⇑φ)^[i] z)
  cases m with
  | zero => exact ⟨0, by simpa using hrel.symm⟩
  | succ n =>
    set P : k[X] := recPoly (p ^ e) c 1 n - X with hP
    have hc1 : P.coeff 1 = -1 := by simp [hP, recPoly_coeff_one he]
    have hdeg : P.degree ≠ 0 := by
      intro h
      rw [Polynomial.eq_C_of_degree_eq_zero h] at hc1
      simp at hc1
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root P hdeg
    have hy' : (recPoly (p ^ e) c 1 n).eval y = y := by
      have := hy.eq_zero
      simp [hP] at this
      exact sub_eq_zero.mp this
    refine ⟨∑ i ∈ range (n + 1), (recPoly (p ^ e) c 1 i).eval y • (⇑φ)^[i] z, ?_⟩
    rw [solve_of_root hφ z n c hrel 1 y hy', one_smul, add_sub_cancel_left]

theorem exists_fixed_ne_zero [IsAlgClosed k] [FiniteDimensional k V] (he : 0 < e)
    (hφ : ∀ (c : k) (x : V), φ (c • x) = c ^ p ^ e • φ x) (z : V)
    (hz : ∀ N, (⇑φ)^[N] z ≠ 0) : ∃ x, x ≠ 0 ∧ φ x = x := by
  obtain ⟨m, ⟨c, hrel⟩, hli⟩ := exists_rel k (fun i => (⇑φ)^[i] z)
  cases m with
  | zero => exact absurd (by simpa using hrel) (hz 0)
  | succ n =>
    have h2 := two_le_pow (p := p) he
    obtain ⟨j, hj, hcj⟩ : ∃ j ∈ range (n + 1), c j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hz (n + 1)
      rw [hrel]
      exact Finset.sum_eq_zero (fun i hi => by rw [hcon i hi, zero_smul])
    obtain ⟨t, rfl⟩ : ∃ t, n = j + t := ⟨n - j, by simp at hj; omega⟩
    set N := (p ^ e) ^ (t + 1) with hN
    have hN2 : 2 ≤ N := le_trans h2 (Nat.le_self_pow (by omega) _)
    set P : k[X] := recPoly (p ^ e) c 0 (j + t) - X with hP
    have hP0 : P.coeff 0 = 0 := by simp [hP, recPoly_coeff_zero]
    have hP1 : P.coeff 1 = -1 := by simp [hP, recPoly_coeff_one he]
    have hPN : P.coeff N ≠ 0 := by
      have hN1 : N ≠ 1 := by omega
      simp only [hP, coeff_sub, coeff_X, hN, recPoly_coeff_lead he c 0 j t]
      rw [if_neg (by omega), sub_zero]
      exact pow_ne_zero _ hcj
    obtain ⟨Q, hQ⟩ := X_dvd_iff.mpr hP0
    have hQ0 : Q.coeff 0 = -1 := by
      rw [← hP1, hQ, show (1 : ℕ) = 0 + 1 from rfl, coeff_X_mul]
    have hQN : Q.coeff (N - 1) ≠ 0 := by
      rw [← coeff_X_mul, show N - 1 + 1 = N by omega, ← hQ]
      exact hPN
    have hdeg : Q.degree ≠ 0 := by
      intro h
      rw [Polynomial.eq_C_of_degree_eq_zero h, coeff_C, if_neg (by omega)] at hQN
      exact hQN rfl
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root Q hdeg
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [IsRoot, ← coeff_zero_eq_eval_zero, hQ0] at hy
      exact one_ne_zero (neg_eq_zero.mp hy)
    have hy' : (recPoly (p ^ e) c 0 (j + t)).eval y = y := by
      have : P.eval y = 0 := by rw [hQ, eval_mul, hy.eq_zero, mul_zero]
      simp only [hP, eval_sub, eval_X] at this
      exact sub_eq_zero.mp this
    refine ⟨_, ?_, by rw [solve_of_root hφ z (j + t) c hrel 0 y hy', zero_smul, add_zero]⟩
    intro hx
    rw [Finset.sum_range] at hx
    have := Fintype.linearIndependent_iff.mp hli
      (fun i : Fin (j + t + 1) => (recPoly (p ^ e) c 0 i).eval y) hx ⟨j + t, by omega⟩
    exact hy0 (by simpa [hy'] using this)

end Vec

end SemilinearResidue

end GroundTheory.PAdicHodge
