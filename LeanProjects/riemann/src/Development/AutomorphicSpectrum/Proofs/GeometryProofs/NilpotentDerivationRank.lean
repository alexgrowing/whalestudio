import Mathlib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ggeo.DerivFree

variable {k : Type} [Field k] {R : Type} [CommRing R] [Algebra k R]

theorem deriv_mul_pow (D : Derivation k R R) {z : R} (hz : D z = 1) {c : R} (hc : D c = 0) (m : ℕ) :
    D (c * z ^ m) = (m : R) * c * z ^ (m - 1) := by
  rw [D.leibniz, D.leibniz_pow, hz, hc]
  simp only [smul_eq_mul, nsmul_eq_mul, mul_one, mul_zero, add_zero]
  ring

theorem iter_mul_pow (D : Derivation k R R) {z : R} (hz : D z = 1) {c : R} (hc : D c = 0)
    (n i : ℕ) :
    (⇑D)^[n] (c * z ^ i) = (i.descFactorial n : R) * c * z ^ (i - n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    have hdc : D ((i.descFactorial n : R) * c) = 0 := by
      rw [D.leibniz, hc, Derivation.map_natCast]
      simp
    rw [deriv_mul_pow D hz hdc, Nat.descFactorial_succ, Nat.sub_sub]
    push_cast
    ring

theorem iter_sum (D : Derivation k R R) (n : ℕ) {ι : Type} (s : Finset ι) (f : ι → R) :
    (⇑D)^[n] (∑ i ∈ s, f i) = ∑ i ∈ s, (⇑D)^[n] (f i) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih, map_sum]

theorem iter_sub (D : Derivation k R R) (n : ℕ) (a b : R) :
    (⇑D)^[n] (a - b) = (⇑D)^[n] a - (⇑D)^[n] b := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih, map_sub]

theorem iter_smul (D : Derivation k R R) (n : ℕ) (r : k) (a : R) :
    (⇑D)^[n] (r • a) = r • (⇑D)^[n] a := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih, D.map_smul]

theorem factorial_ne_zero_of_lt (p : ℕ) [Fact p.Prime] [CharP k p] {j : ℕ} (hj : j < p) :
    ((j.factorial : ℕ) : k) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff k p] at h
  have := (Nat.Prime.dvd_factorial (Fact.out : p.Prime)).1 h
  omega

theorem coeff_zero (p : ℕ) [Fact p.Prime] [CharP k p] (D : Derivation k R R) {z : R}
    (hz : D z = 1) (m : ℕ) (hm : m ≤ p) (c : ℕ → R) (hc : ∀ i, D (c i) = 0)
    (h : ∑ i ∈ Finset.range m, c i * z ^ i = 0) : ∀ i < m, c i = 0 := by
  induction m with
  | zero => intro i hi; omega
  | succ m ih =>
    have hlast : c m = 0 := by
      have h1 := congrArg (⇑D)^[m] h
      have h0 : (⇑D)^[m] (0 : R) = 0 := by
        have := iter_smul D m (0 : k) (0 : R)
        simpa using this
      rw [iter_sum, h0, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add,
        iter_mul_pow D hz (hc m), Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one] at h1
      · have hf : ((m.factorial : ℕ) : k) ≠ 0 := factorial_ne_zero_of_lt p (by omega)
        have h2 : ((m.factorial : ℕ) : k) • c m = 0 := by
          rw [Algebra.smul_def, map_natCast]; exact h1
        exact (smul_eq_zero.1 h2).resolve_left hf
      · intro i hi
        have hi' : i < m := Finset.mem_range.1 hi
        rw [iter_mul_pow D hz (hc i), Nat.descFactorial_eq_zero_iff_lt.2 hi']
        simp
    rw [Finset.sum_range_succ, hlast, zero_mul, add_zero] at h
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact ih (by omega) h i hi
    · exact hlast

theorem exists_coeff (p : ℕ) [Fact p.Prime] [CharP k p] (D : Derivation k R R) {z : R}
    (hz : D z = 1) (j : ℕ) (hj : j ≤ p) (a : R) (ha : (⇑D)^[j] a = 0) :
    ∃ c : ℕ → R, (∀ i, D (c i) = 0) ∧ a = ∑ i ∈ Finset.range j, c i * z ^ i := by
  induction j generalizing a with
  | zero => exact ⟨fun _ => 0, by simp, by simpa using ha⟩
  | succ j ih =>
    set b := (⇑D)^[j] a with hb
    have hDb : D b = 0 := by
      rw [hb, ← Function.iterate_succ_apply' (⇑D)]; exact ha
    have hf : ((j.factorial : ℕ) : k) ≠ 0 := factorial_ne_zero_of_lt p (by omega)
    set e := (((j.factorial : ℕ) : k))⁻¹ • b with he
    have hDe : D e = 0 := by rw [he, D.map_smul, hDb, smul_zero]
    have hker : (⇑D)^[j] (a - e * z ^ j) = 0 := by
      rw [iter_sub, iter_mul_pow D hz hDe, Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one,
        ← hb, he, mul_smul_comm]
      have hnb : ((j.factorial : ℕ) : R) * b = ((j.factorial : ℕ) : k) • b := by
        rw [Algebra.smul_def, map_natCast]
      rw [hnb, smul_smul, inv_mul_cancel₀ hf, one_smul, sub_self]
    obtain ⟨c, hc, hac⟩ := ih (by omega) _ hker
    refine ⟨fun i => if i = j then e else c i, ?_, ?_⟩
    · intro i; by_cases hi : i = j <;> simp [hi, hDe, hc]
    · rw [Finset.sum_range_succ]
      have : ∑ i ∈ Finset.range j, (if i = j then e else c i) * z ^ i
          = ∑ i ∈ Finset.range j, c i * z ^ i := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [if_neg (Finset.mem_range.1 hi).ne]
      rw [this, ← hac]
      simp

theorem exists_deriv_eq_one (p : ℕ) [Fact p.Prime] (D : Derivation k R R)
    (hnil : ∀ a : R, (⇑D)^[p] a = 0) (t : R) (ht : IsUnit ((⇑D)^[p - 1] t)) :
    ∃ z : R, D z = 1 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨w, hw⟩ := ht
  have hp1 : p - 1 = (p - 2) + 1 := by omega
  have hs : D ((⇑D)^[p - 2] t) = (w : R) := by
    rw [hw, hp1, Function.iterate_succ_apply']
  have hDw : D (w : R) = 0 := by
    have h := hnil t
    have hp2 : p = (p - 1) + 1 := by omega
    rw [hp2, Function.iterate_succ_apply'] at h
    rw [hw]
    simpa using h
  have hDinv : D ((w⁻¹ : Rˣ) : R) = 0 := by
    have h1 : D ((w : R) * ((w⁻¹ : Rˣ) : R)) = 0 := by
      rw [Units.mul_inv, D.map_one_eq_zero]
    rw [D.leibniz, hDw, smul_zero, add_zero, smul_eq_mul] at h1
    exact (Units.mul_right_eq_zero w).1 h1
  refine ⟨((w⁻¹ : Rˣ) : R) * (⇑D)^[p - 2] t, ?_⟩
  rw [D.leibniz, hs, hDinv, smul_zero, add_zero, smul_eq_mul, Units.inv_mul]

noncomputable def coeffMap (p : ℕ) (D : Derivation k R R) (z : R) :
    (Fin p → LinearMap.ker (D : R →ₗ[k] R)) →ₗ[k] R where
  toFun a := ∑ i, (a i : R) * z ^ (i : ℕ)
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' r a := by simp [Finset.smul_sum, smul_mul_assoc]

theorem coeffMap_bijective (p : ℕ) [Fact p.Prime] [CharP k p] (D : Derivation k R R) {z : R}
    (hz : D z = 1) (hnil : ∀ a : R, (⇑D)^[p] a = 0) :
    Function.Bijective (coeffMap p D z) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    let c : ℕ → R := fun i => if h : i < p then (a ⟨i, h⟩ : R) else 0
    have hc : ∀ i, D (c i) = 0 := by
      intro i
      by_cases h : i < p
      · have h3 : D (a ⟨i, h⟩ : R) = 0 := LinearMap.mem_ker.1 (a ⟨i, h⟩).2
        simpa [c, h] using h3
      · simp [c, h]
    have hsum : ∑ i ∈ Finset.range p, c i * z ^ i = 0 := by
      rw [Finset.sum_range]
      have h2 : (∑ i : Fin p, (a i : R) * z ^ (i : ℕ)) = 0 := ha
      rw [← h2]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [c]
    have h0 := coeff_zero p D hz p le_rfl c hc hsum
    funext i
    apply Subtype.ext
    have := h0 i i.2
    simpa [c] using this
  · intro a
    obtain ⟨c, hc, hac⟩ := exists_coeff p D hz p le_rfl a (hnil a)
    refine ⟨fun i => ⟨c i, hc i⟩, ?_⟩
    rw [hac, Finset.sum_range]
    rfl

theorem finrank_and_vanishing : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (R : Type) [CommRing R] [Algebra k R] [Module.Finite k R] (D : Derivation k R R) (ε : R →ₐ[k] k),
    (∀ a : R, (⇑D)^[p] a = 0) → ∀ t : R, IsUnit ((⇑D)^[p - 1] t) →
      Module.finrank k R = p * Module.finrank k (LinearMap.ker (D : R →ₗ[k] R)) ∧
      ∃ z : R, ε (D z) ≠ 0 ∧ ∀ u : R →ₗ[k] k, (∀ a b : R, u (a * b) = u a * ε b + ε a * u b) →
        (∀ a : R, D a = 0 → u a = 0) → u z = 0 → u = 0 := by
  intro k _ p _ _ R _ _ _ D ε hnil t ht
  obtain ⟨z, hz⟩ := exists_deriv_eq_one p D hnil t ht
  have hbij := coeffMap_bijective p D hz hnil
  refine ⟨?_, z, ?_, ?_⟩
  · have e := (LinearEquiv.ofBijective (coeffMap p D z) hbij).finrank_eq
    rw [← e, Module.finrank_pi_fintype]
    simp
  · rw [hz, map_one]
    exact one_ne_zero
  · intro u hmul hker huz
    have hpow : ∀ i : ℕ, u (z ^ i) = 0 := by
      intro i
      induction i with
      | zero => rw [pow_zero]; exact hker 1 D.map_one_eq_zero
      | succ i ih => rw [pow_succ, hmul, ih, huz]; simp
    apply LinearMap.ext
    intro a
    obtain ⟨b, rfl⟩ := hbij.2 a
    have h2 : coeffMap p D z b = ∑ i, (b i : R) * z ^ (i : ℕ) := rfl
    rw [h2, map_sum]
    simp only [LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hmul, hpow, hker _ (b i).2]
    simp

end GlobalTheory.CompanionTheory.Ggeo.DerivFree
