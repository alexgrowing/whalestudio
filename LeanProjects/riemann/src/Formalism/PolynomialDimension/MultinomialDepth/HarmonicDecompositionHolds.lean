import Formalism.PolynomialDimension.StatementHar

noncomputable section
open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.CountingSumsFrames
namespace Har2

variable {K : Type} [Field K] {k : ℕ}

private theorem mem_PolAB_iff_forall_support_bidegree {A B : ℕ} {f : PolXY K k} :
    f ∈ PolAB K k A B ↔ ∀ m ∈ f.support, xDeg m = A ∧ yDeg m = B := Iff.rfl

theorem monomial_mem {A B : ℕ} {m : XY k →₀ ℕ} (c : K) (hx : xDeg m = A) (hy : yDeg m = B) :
    monomial m c ∈ PolAB K k A B := by
  classical
  refine mem_PolAB_iff_forall_support_bidegree.2 fun m' hm' => ?_
  rw [Finset.mem_singleton.1 (MvPolynomial.support_monomial_subset hm')]
  exact ⟨hx, hy⟩

theorem lin_mem {A B : ℕ} (T : PolXY K k →ₗ[K] PolXY K k) (S : Submodule K (PolXY K k))
    (h : ∀ (m : XY k →₀ ℕ) (c : K), xDeg m = A → yDeg m = B → T (monomial m c) ∈ S)
    {f : PolXY K k} (hf : f ∈ PolAB K k A B) : T f ∈ S := by
  rw [MvPolynomial.as_sum f, map_sum]
  exact Submodule.sum_mem _ fun m hm =>
    h m _ (mem_PolAB_iff_forall_support_bidegree.1 hf m hm).1 (mem_PolAB_iff_forall_support_bidegree.1 hf m hm).2

theorem lin_eq {A B : ℕ} (T T' : PolXY K k →ₗ[K] PolXY K k)
    (h : ∀ (m : XY k →₀ ℕ) (c : K), xDeg m = A → yDeg m = B → T (monomial m c) = T' (monomial m c))
    {f : PolXY K k} (hf : f ∈ PolAB K k A B) : T f = T' f := by
  rw [MvPolynomial.as_sum f, map_sum, map_sum]
  exact Finset.sum_congr rfl fun m hm =>
    h m _ (mem_PolAB_iff_forall_support_bidegree.1 hf m hm).1 (mem_PolAB_iff_forall_support_bidegree.1 hf m hm).2

theorem xDeg_add (m m' : XY k →₀ ℕ) : xDeg (m + m') = xDeg m + xDeg m' := by
  simp only [xDeg, Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
theorem yDeg_add (m m' : XY k →₀ ℕ) : yDeg (m + m') = yDeg m + yDeg m' := by
  simp only [yDeg, Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
theorem xDeg_inl (i : Fin k) : xDeg (Finsupp.single (Sum.inl i : XY k) 1) = 1 := by
  simp [xDeg, Finsupp.single_apply]
theorem yDeg_inl (i : Fin k) : yDeg (Finsupp.single (Sum.inl i : XY k) 1) = 0 := by
  simp [yDeg, Finsupp.single_apply]
theorem xDeg_inr (i : Fin k) : xDeg (Finsupp.single (Sum.inr i : XY k) 1) = 0 := by
  simp [xDeg, Finsupp.single_apply]
theorem yDeg_inr (i : Fin k) : yDeg (Finsupp.single (Sum.inr i : XY k) 1) = 1 := by
  simp [yDeg, Finsupp.single_apply]

theorem X_inl_mul_mem {A B : ℕ} (i : Fin k) {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    X (Sum.inl i) * f ∈ PolAB K k (A + 1) B := by
  have key := lin_mem (A := A) (B := B) (LinearMap.mulLeft K (X (Sum.inl i) : PolXY K k))
    (PolAB K k (A + 1) B) (fun m c hx hy => by
      rw [LinearMap.mulLeft_apply,
        show (X (Sum.inl i) : PolXY K k) = monomial (Finsupp.single (Sum.inl i) 1) 1 from rfl,
        monomial_mul, one_mul]
      exact monomial_mem _ (by rw [xDeg_add, xDeg_inl]; omega) (by rw [yDeg_add, yDeg_inl]; omega)) hf
  simpa only [LinearMap.mulLeft_apply] using key

theorem X_inr_mul_mem {A B : ℕ} (i : Fin k) {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    X (Sum.inr i) * f ∈ PolAB K k A (B + 1) := by
  have key := lin_mem (A := A) (B := B) (LinearMap.mulLeft K (X (Sum.inr i) : PolXY K k))
    (PolAB K k A (B + 1)) (fun m c hx hy => by
      rw [LinearMap.mulLeft_apply,
        show (X (Sum.inr i) : PolXY K k) = monomial (Finsupp.single (Sum.inr i) 1) 1 from rfl,
        monomial_mul, one_mul]
      exact monomial_mem _ (by rw [xDeg_add, xDeg_inr]; omega) (by rw [yDeg_add, yDeg_inr]; omega)) hf
  simpa only [LinearMap.mulLeft_apply] using key

theorem h_mul_mem {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    hXY K k * f ∈ PolAB K k (A + 1) (B + 1) := by
  simp only [hXY, Finset.sum_mul]
  exact Submodule.sum_mem _ fun i _ => by
    rw [mul_assoc]; exact X_inl_mul_mem i (X_inr_mul_mem i hf)

theorem h_pow_mul_mem {A B : ℕ} (l : ℕ) {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    hXY K k ^ l * f ∈ PolAB K k (A + l) (B + l) := by
  induction l with
  | zero => simpa using hf
  | succ l ih =>
    rw [pow_succ', mul_assoc, ← add_assoc, ← add_assoc]
    exact h_mul_mem ih

private theorem xDeg_yDeg_sub_single_add_single (m : XY k →₀ ℕ) (v : XY k) (hv : 1 ≤ m v) :
    xDeg (m - Finsupp.single v 1) + xDeg (Finsupp.single v 1) = xDeg m ∧
    yDeg (m - Finsupp.single v 1) + yDeg (Finsupp.single v 1) = yDeg m := by
  have hle : Finsupp.single v 1 ≤ m := Finsupp.single_le_iff.2 hv
  rw [← xDeg_add, ← yDeg_add, tsub_add_cancel_of_le hle]
  exact ⟨rfl, rfl⟩

theorem pderiv_inl_mem {A B : ℕ} (i : Fin k) {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    pderiv (Sum.inl i) f ∈ PolAB K k (A - 1) B := by
  have key := lin_mem (A := A) (B := B) (pderiv (R := K) (Sum.inl i : XY k)).toLinearMap
    (PolAB K k (A - 1) B) (fun m c hx hy => by
      change pderiv (Sum.inl i) (monomial m c) ∈ PolAB K k (A - 1) B
      rw [pderiv_monomial]
      by_cases h0 : m (Sum.inl i) = 0
      · rw [h0, Nat.cast_zero, mul_zero, monomial_zero]; exact Submodule.zero_mem _
      · obtain ⟨h1, h2⟩ := xDeg_yDeg_sub_single_add_single m (Sum.inl i) (Nat.one_le_iff_ne_zero.2 h0)
        rw [xDeg_inl] at h1; rw [yDeg_inl] at h2
        exact monomial_mem _ (by omega) (by omega)) hf
  exact key

theorem pderiv_inr_mem {A B : ℕ} (i : Fin k) {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    pderiv (Sum.inr i) f ∈ PolAB K k A (B - 1) := by
  have key := lin_mem (A := A) (B := B) (pderiv (R := K) (Sum.inr i : XY k)).toLinearMap
    (PolAB K k A (B - 1)) (fun m c hx hy => by
      change pderiv (Sum.inr i) (monomial m c) ∈ PolAB K k A (B - 1)
      rw [pderiv_monomial]
      by_cases h0 : m (Sum.inr i) = 0
      · rw [h0, Nat.cast_zero, mul_zero, monomial_zero]; exact Submodule.zero_mem _
      · obtain ⟨h1, h2⟩ := xDeg_yDeg_sub_single_add_single m (Sum.inr i) (Nat.one_le_iff_ne_zero.2 h0)
        rw [xDeg_inr] at h1; rw [yDeg_inr] at h2
        exact monomial_mem _ (by omega) (by omega)) hf
  exact key

private theorem apply_inl_le_xDeg (m : XY k →₀ ℕ) (i : Fin k) : m (Sum.inl i) ≤ xDeg m := by
  unfold xDeg
  exact Finset.single_le_sum (f := fun j => m (Sum.inl j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

private theorem apply_inr_le_yDeg (m : XY k →₀ ℕ) (i : Fin k) : m (Sum.inr i) ≤ yDeg m := by
  unfold yDeg
  exact Finset.single_le_sum (f := fun j => m (Sum.inr j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem pderiv_inl_zero {B : ℕ} (i : Fin k) {f : PolXY K k} (hf : f ∈ PolAB K k 0 B) :
    pderiv (Sum.inl i) f = 0 := by
  have key := lin_eq (A := 0) (B := B) (pderiv (R := K) (Sum.inl i : XY k)).toLinearMap 0
    (fun m c hx _ => by
      have h0 : m (Sum.inl i) = 0 := by have := apply_inl_le_xDeg m i; omega
      change pderiv (Sum.inl i) (monomial m c) = (0 : PolXY K k →ₗ[K] PolXY K k) (monomial m c)
      rw [LinearMap.zero_apply, pderiv_monomial, h0, Nat.cast_zero, mul_zero, monomial_zero]) hf
  simpa using key

theorem pderiv_inr_zero {A : ℕ} (i : Fin k) {f : PolXY K k} (hf : f ∈ PolAB K k A 0) :
    pderiv (Sum.inr i) f = 0 := by
  have key := lin_eq (A := A) (B := 0) (pderiv (R := K) (Sum.inr i : XY k)).toLinearMap 0
    (fun m c _ hy => by
      have h0 : m (Sum.inr i) = 0 := by have := apply_inr_le_yDeg m i; omega
      change pderiv (Sum.inr i) (monomial m c) = (0 : PolXY K k →ₗ[K] PolXY K k) (monomial m c)
      rw [LinearMap.zero_apply, pderiv_monomial, h0, Nat.cast_zero, mul_zero, monomial_zero]) hf
  simpa using key

theorem ctrF_apply (f : PolXY K k) :
    ctrF K k f = ∑ i : Fin k, pderiv (Sum.inl i) (pderiv (Sum.inr i) f) := by
  unfold ctrF
  rw [LinearMap.sum_apply]
  rfl

theorem ctrF_mem {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    ctrF K k f ∈ PolAB K k (A - 1) (B - 1) := by
  rw [ctrF_apply]
  exact Submodule.sum_mem _ fun i _ => pderiv_inl_mem i (pderiv_inr_mem i hf)

theorem ctrF_zero_left {B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k 0 B) : ctrF K k f = 0 := by
  rw [ctrF_apply]
  exact Finset.sum_eq_zero fun i _ => pderiv_inl_zero i (pderiv_inr_mem i hf)

theorem ctrF_zero_right {A : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A 0) : ctrF K k f = 0 := by
  rw [ctrF_apply]
  exact Finset.sum_eq_zero fun i _ => by rw [pderiv_inr_zero i hf, map_zero]

theorem ctrF_pow_mem {A B : ℕ} (l : ℕ) {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    (ctrF K k ^ l) f ∈ PolAB K k (A - l) (B - l) := by
  induction l with
  | zero => simpa using hf
  | succ l ih =>
    rw [pow_succ', Module.End.mul_apply, Nat.sub_add_eq, Nat.sub_add_eq]
    exact ctrF_mem ih

theorem ctrF_pow_zero {A B : ℕ} {l : ℕ} (hl : min A B < l) {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    (ctrF K k ^ l) f = 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, l = d + (min A B + 1) := ⟨l - (min A B + 1), by omega⟩
  rw [pow_add, Module.End.mul_apply, pow_succ', Module.End.mul_apply]
  have hm := ctrF_pow_mem (min A B) hf
  rcases le_total A B with h | h
  · rw [min_eq_left h] at hm ⊢
    rw [Nat.sub_self] at hm
    rw [ctrF_zero_left hm, map_zero]
  · rw [min_eq_right h] at hm ⊢
    rw [Nat.sub_self] at hm
    rw [ctrF_zero_right hm, map_zero]

theorem pderiv_inr_h (i : Fin k) : pderiv (Sum.inr i) (hXY K k) = X (Sum.inl i) := by
  classical
  simp [hXY, Derivation.leibniz, pderiv_X, Pi.single_apply]

theorem pderiv_inl_h (i : Fin k) : pderiv (Sum.inl i) (hXY K k) = X (Sum.inr i) := by
  classical
  simp [hXY, Derivation.leibniz, pderiv_X, Pi.single_apply]

private theorem X_mul_pderiv_monomialMultinomialDepth (v : XY k) (m : XY k →₀ ℕ) (c : K) :
    (X v : PolXY K k) * pderiv v (monomial m c) = monomial m (c * (m v : K)) := by
  rw [pderiv_monomial]
  by_cases h0 : m v = 0
  · simp only [h0, Nat.cast_zero, mul_zero, monomial_zero]
  · rw [show (X v : PolXY K k) = monomial (Finsupp.single v 1) 1 from rfl, monomial_mul, one_mul,
      add_tsub_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h0))]

theorem euler_X_sum {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    ∑ i : Fin k, X (Sum.inl i) * pderiv (Sum.inl i) f = (A : K) • f := by
  have hf' := mem_PolAB_iff_forall_support_bidegree.1 hf
  conv_lhs => rw [MvPolynomial.as_sum f]
  conv_rhs => rw [MvPolynomial.as_sum f]
  simp only [map_sum, Finset.mul_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [X_mul_pderiv_monomialMultinomialDepth]
  rw [← map_sum (monomial m), ← Finset.mul_sum, ← Nat.cast_sum,
    show (∑ i : Fin k, m (Sum.inl i)) = A from (hf' m hm).1, smul_monomial, smul_eq_mul, mul_comm]

theorem euler_y {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    ∑ i : Fin k, X (Sum.inr i) * pderiv (Sum.inr i) f = (B : K) • f := by
  have hf' := mem_PolAB_iff_forall_support_bidegree.1 hf
  conv_lhs => rw [MvPolynomial.as_sum f]
  conv_rhs => rw [MvPolynomial.as_sum f]
  simp only [map_sum, Finset.mul_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [X_mul_pderiv_monomialMultinomialDepth]
  rw [← map_sum (monomial m), ← Finset.mul_sum, ← Nat.cast_sum,
    show (∑ i : Fin k, m (Sum.inr i)) = B from (hf' m hm).2, smul_monomial, smul_eq_mul, mul_comm]

theorem ctr_h {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    ctrF K k (hXY K k * f) = hXY K k * ctrF K k f + ((A + B + k : ℕ) : K) • f := by
  rw [ctrF_apply, ctrF_apply]
  have e : ∀ i : Fin k, pderiv (Sum.inl i) (pderiv (Sum.inr i) (hXY K k * f)) =
      f + X (Sum.inl i) * pderiv (Sum.inl i) f + X (Sum.inr i) * pderiv (Sum.inr i) f +
        hXY K k * pderiv (Sum.inl i) (pderiv (Sum.inr i) f) := by
    intro i
    simp only [Derivation.leibniz, map_add, pderiv_inr_h, pderiv_inl_h, pderiv_X_self, smul_eq_mul]
    ring
  simp only [e, Finset.sum_add_distrib, euler_X_sum hf, euler_y hf, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, MvPolynomial.smul_eq_C_mul, map_natCast]
  push_cast
  ring

theorem ctr_h_pow {a b : ℕ} (l : ℕ) {g : PolXY K k} (hg : g ∈ PolAB K k a b) :
    ctrF K k (hXY K k ^ (l + 1) * g) = hXY K k ^ (l + 1) * ctrF K k g +
      (((l + 1) * (a + b + k + l) : ℕ) : K) • (hXY K k ^ l * g) := by
  induction l with
  | zero =>
    rw [zero_add, pow_one, ctr_h hg]
    simp only [MvPolynomial.smul_eq_C_mul, map_natCast]
    push_cast
    ring
  | succ l ih =>
    rw [pow_succ' (hXY K k) (l + 1), mul_assoc, ctr_h (h_pow_mul_mem (l + 1) hg), ih]
    simp only [MvPolynomial.smul_eq_C_mul, map_natCast]
    push_cast
    ring

private theorem mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero {A B : ℕ} {f : PolXY K k} :
    f ∈ HarAB K k A B ↔ f ∈ PolAB K k A B ∧ ctrF K k f = 0 := Iff.rfl

theorem ctr_h_pow_har {a b : ℕ} (i : ℕ) {w : PolXY K k} (hw : w ∈ HarAB K k a b) :
    ctrF K k (hXY K k ^ (i + 1) * w) = (((i + 1) * (a + b + k + i) : ℕ) : K) • (hXY K k ^ i * w) := by
  rw [ctr_h_pow i (mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.1 hw).1, (mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.1 hw).2, mul_zero, zero_add]

theorem ctr_pow_h_pow_har (hk : 1 ≤ k) {a b : ℕ} {w : PolXY K k} (hw : w ∈ HarAB K k a b) (m : ℕ) :
    ∀ i : ℕ, (ctrF K k ^ m) (hXY K k ^ i * w) =
      ((i.descFactorial m * (a + b + k + i - 1).descFactorial m : ℕ) : K) • (hXY K k ^ (i - m) * w) := by
  obtain ⟨h1, h2⟩ := mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.1 hw
  induction m with
  | zero => intro i; simp
  | succ m ih =>
    intro i
    rw [pow_succ, Module.End.mul_apply]
    rcases i with _ | j
    · rw [pow_zero, one_mul, h2, map_zero, Nat.zero_descFactorial_succ, zero_mul, Nat.cast_zero,
        zero_smul]
    · rw [ctr_h_pow_har j hw, map_smul, ih j, smul_smul, Nat.add_sub_add_right]
      congr 1
      have hN : a + b + k + (j + 1) - 1 = (a + b + k + j - 1) + 1 := by omega
      rw [hN, Nat.succ_descFactorial_succ, Nat.succ_descFactorial_succ]
      have hN2 : a + b + k + j - 1 + 1 = a + b + k + j := by omega
      rw [hN2]
      push_cast
      ring

theorem har_indep [CharZero K] (hk : 1 ≤ k) (n : ℕ) : ∀ (a b : ℕ → ℕ) (w : ℕ → PolXY K k),
    (∀ j, w j ∈ HarAB K k (a j) (b j)) → ∑ j ∈ range n, hXY K k ^ j * w j = 0 → ∀ j < n, w j = 0 := by
  induction n with
  | zero => intro a b w _ _ j hj; exact absurd hj (Nat.not_lt_zero _)
  | succ n ih =>
    intro a b w hw hs
    have hwn : w n = 0 := by
      have h1 : (ctrF K k ^ n) (∑ j ∈ range (n + 1), hXY K k ^ j * w j) = 0 := by rw [hs, map_zero]
      have hz : ∑ j ∈ range n, (ctrF K k ^ n) (hXY K k ^ j * w j) = 0 :=
        Finset.sum_eq_zero fun j hj => by
          rw [ctr_pow_h_pow_har hk (hw j) n j,
            Nat.descFactorial_eq_zero_iff_lt.2 (Finset.mem_range.1 hj), zero_mul, Nat.cast_zero, zero_smul]
      rw [map_sum, Finset.sum_range_succ, hz, zero_add, ctr_pow_h_pow_har hk (hw n) n n, Nat.sub_self,
        pow_zero, one_mul, smul_eq_zero] at h1
      rcases h1 with h1 | h1
      · exfalso
        rw [Nat.cast_eq_zero, mul_eq_zero, Nat.descFactorial_self, Nat.descFactorial_eq_zero_iff_lt] at h1
        rcases h1 with h1 | h1
        · exact Nat.factorial_ne_zero n h1
        · omega
      · exact h1
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [Finset.sum_range_succ, hwn, mul_zero, add_zero] at hs
      exact ih a b w hw hs j hj
    · rw [hj]; exact hwn

def cP (K : Type) [Field K] (M l : ℕ) : K :=
  (-1 : K) ^ l / ((M.choose l : ℕ) : K) * (((l.factorial : ℕ) : K)⁻¹ * ((l.factorial : ℕ) : K)⁻¹)

theorem cPoint_zero (M : ℕ) : cP K M 0 = 1 := by
  simp [cP]

theorem harmonic_identity_cancel (x y t s φ e : K) (hx : x ≠ 0) (hy : y ≠ 0) (ht : t ≠ 0) (hφ : φ ≠ 0) (h : y * t = x * s) :
    e / x * (φ⁻¹ * φ⁻¹) + (e * -1) / y * ((t * φ)⁻¹ * (t * φ)⁻¹) * (t * s) = 0 := by
  obtain rfl : s = y * t / x := by
    rw [eq_div_iff hx]
    linear_combination -h
  field_simp
  all_goals ring

theorem harmonicCoeff_recurrence [CharZero K] {M N : ℕ} (h : N < M) :
    cP K M N + cP K M (N + 1) * (((N + 1) * (M - N) : ℕ) : K) = 0 := by
  unfold cP
  rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_mul]
  exact harmonic_identity_cancel _ _ _ _ _ _ (Nat.cast_ne_zero.2 (Nat.choose_pos h.le).ne')
    (Nat.cast_ne_zero.2 (Nat.choose_pos h).ne') (Nat.cast_ne_zero.2 (Nat.succ_ne_zero N))
    (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero N))
    (by rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_succ_right_eq])

theorem harProj_apply (A B : ℕ) (f : PolXY K k) : harProj K k A B f =
    ∑ l ∈ range (min A B + 1), cP K (A + B + k - 2) l • (hXY K k ^ l * (ctrF K k ^ l) f) := by
  unfold harProj
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, hDiv, ctrDiv, LinearMap.mulLeft_apply,
    mul_smul_comm, smul_smul, cP]
  all_goals (congr 1; ring)

theorem ctr_partial [CharZero K] (hk : 1 ≤ k) {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) (N : ℕ)
    (hN : N ≤ min A B) :
    ctrF K k (∑ l ∈ range (N + 1), cP K (A + B + k - 2) l • (hXY K k ^ l * (ctrF K k ^ l) f)) =
      cP K (A + B + k - 2) N • (hXY K k ^ N * (ctrF K k ^ (N + 1)) f) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h1 := min_le_left A B
    have h2 := min_le_right A B
    have e1 : ctrF K k ((ctrF K k ^ (N + 1)) f) = (ctrF K k ^ (N + 1 + 1)) f := by
      rw [pow_succ' (ctrF K k) (N + 1), Module.End.mul_apply]
    have hc : (N + 1) * (A - (N + 1) + (B - (N + 1)) + k + N) = (N + 1) * (A + B + k - 2 - N) := by
      congr 1
      omega
    have hrec := harmonicCoeff_recurrence (K := K) (M := A + B + k - 2) (N := N) (by omega)
    rw [Finset.sum_range_succ, map_add, ih (by omega), map_smul,
      ctr_h_pow N (ctrF_pow_mem (N + 1) hf), e1, hc, smul_add, smul_smul, add_left_comm, ← add_smul,
      hrec, zero_smul, add_zero]

theorem harProj_ker [CharZero K] (hk : 1 ≤ k) {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    ctrF K k (harProj K k A B f) = 0 := by
  rw [harProj_apply, ctr_partial hk hf (min A B) le_rfl, ctrF_pow_zero (Nat.lt_add_one _) hf, mul_zero,
    smul_zero]

theorem harProj_memPol {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    harProj K k A B f ∈ PolAB K k A B := by
  rw [harProj_apply]
  refine Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ ?_
  have hl' := Finset.mem_range.1 hl
  have h1 := min_le_left A B
  have h2 := min_le_right A B
  have := h_pow_mul_mem l (ctrF_pow_mem l hf)
  rwa [Nat.sub_add_cancel (by omega : l ≤ A), Nat.sub_add_cancel (by omega : l ≤ B)] at this

theorem harProj_mem [CharZero K] (hk : 1 ≤ k) {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    harProj K k A B f ∈ HarAB K k A B := by
  exact mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.2 ⟨harProj_memPol hf, harProj_ker hk hf⟩

theorem harProj_sub {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    ∃ g ∈ PolAB K k (A - 1) (B - 1), f - harProj K k A B f = hXY K k * g := by
  have h1 := min_le_left A B
  have h2 := min_le_right A B
  refine ⟨-∑ l ∈ range (min A B), cP K (A + B + k - 2) (l + 1) • (hXY K k ^ l * (ctrF K k ^ (l + 1)) f),
    ?_, ?_⟩
  · refine Submodule.neg_mem _ (Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ ?_)
    have hl' := Finset.mem_range.1 hl
    have := h_pow_mul_mem l (ctrF_pow_mem (l + 1) hf)
    rwa [show A - (l + 1) + l = A - 1 by omega, show B - (l + 1) + l = B - 1 by omega] at this
  · rw [harProj_apply, Finset.sum_range_succ']
    simp only [pow_zero, one_mul, Module.End.one_apply, cPoint_zero, one_smul, mul_neg, Finset.mul_sum,
      mul_smul_comm, ← mul_assoc, ← pow_succ']
    abel

theorem harProj_har {A B : ℕ} {f : PolXY K k} (hf : f ∈ HarAB K k A B) : harProj K k A B f = f := by
  obtain ⟨_, h2⟩ := mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.1 hf
  have hz : ∀ l : ℕ, cP K (A + B + k - 2) (l + 1) • (hXY K k ^ (l + 1) * (ctrF K k ^ (l + 1)) f) = 0 :=
    fun l => by rw [pow_succ (ctrF K k), Module.End.mul_apply, h2, map_zero, mul_zero, smul_zero]
  rw [harProj_apply, Finset.sum_range_succ']
  simp [hz, cPoint_zero]

theorem har_of_left {B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k 0 B) : f ∈ HarAB K k 0 B := by
  exact mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.2 ⟨hf, ctrF_zero_left hf⟩

theorem har_of_right {A : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A 0) : f ∈ HarAB K k A 0 := by
  exact mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.2 ⟨hf, ctrF_zero_right hf⟩

theorem decomp_exists [CharZero K] (hk : 1 ≤ k) : ∀ (A B : ℕ) (f : PolXY K k), f ∈ PolAB K k A B →
    ∃ w : ℕ → PolXY K k, (∀ j, w j ∈ HarAB K k (A - j) (B - j)) ∧
      f = ∑ j ∈ range (min A B + 1), hXY K k ^ j * w j := by
  intro A
  induction A with
  | zero =>
    intro B f hf
    refine ⟨fun j => if j = 0 then f else 0, fun j => ?_, ?_⟩
    · by_cases hj : j = 0
      · subst hj
        simpa using har_of_left hf
      · simp [hj]
    · simp
  | succ A ih =>
    intro B f hf
    rcases B with _ | B
    · refine ⟨fun j => if j = 0 then f else 0, fun j => ?_, ?_⟩
      · by_cases hj : j = 0
        · subst hj
          simpa using har_of_right hf
        · simp [hj]
      · simp
    · obtain ⟨g, hg, hfg⟩ := harProj_sub hf
      simp only [Nat.add_sub_cancel] at hg
      obtain ⟨v, hv, hgv⟩ := ih B g hg
      refine ⟨fun j => if j = 0 then harProj K k (A + 1) (B + 1) f else v (j - 1), fun j => ?_, ?_⟩
      · by_cases hj : j = 0
        · subst hj
          simpa using harProj_mem hk hf
        · simp only [hj, ↓reduceIte]
          have := hv (j - 1)
          rwa [show A - (j - 1) = A + 1 - j by omega, show B - (j - 1) = B + 1 - j by omega] at this
      · rw [min_add_add_right, Finset.sum_range_succ']
        simp only [Nat.add_one_ne_zero, ↓reduceIte, add_tsub_cancel_right, pow_zero, one_mul]
        have e : f = harProj K k (A + 1) (B + 1) f + hXY K k * g := by rw [← hfg]; abel
        conv_lhs => rw [e]
        rw [hgv, Finset.mul_sum, add_comm]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← mul_assoc, ← pow_succ']

theorem har_inter [CharZero K] (hk : 1 ≤ k) {A B a b : ℕ} {u g : PolXY K k} (hu : u ∈ HarAB K k A B)
    (hg : g ∈ PolAB K k a b) (h : u = hXY K k * g) : u = 0 := by
  obtain ⟨w, hw, hgw⟩ := decomp_exists hk a b g hg
  have key := har_indep hk (min a b + 1 + 1) (fun j => if j = 0 then A else a - (j - 1))
    (fun j => if j = 0 then B else b - (j - 1)) (fun j => if j = 0 then u else -w (j - 1))
    (fun j => by
      by_cases hj : j = 0
      · simp [hj, hu]
      · simp only [hj, ↓reduceIte]
        exact Submodule.neg_mem _ (hw (j - 1)))
    (by
      rw [Finset.sum_range_succ']
      simp only [Nat.add_one_ne_zero, ↓reduceIte, add_tsub_cancel_right, pow_zero, one_mul, mul_neg,
        Finset.sum_neg_distrib]
      rw [neg_add_eq_zero, h, hgw, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [← mul_assoc, ← pow_succ'])
  simpa using key 0 (by omega)

theorem harProj_kill [CharZero K] (hk : 1 ≤ k) {A B : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) {g : PolXY K k}
    (hg : g ∈ PolAB K k (A - 1) (B - 1)) : harProj K k A B (hXY K k * g) = 0 := by
  have hhg : hXY K k * g ∈ PolAB K k A B := by
    have := h_mul_mem hg
    rwa [Nat.sub_add_cancel hA, Nat.sub_add_cancel hB] at this
  obtain ⟨g', hg', he⟩ := harProj_sub hhg
  exact har_inter hk (harProj_mem hk hhg) (Submodule.sub_mem _ hg hg') (by rw [mul_sub, ← he]; abel)

theorem exists_laplacian_eq [CharZero K] (hk : 1 ≤ k) {A B : ℕ} {g : PolXY K k} (hg : g ∈ PolAB K k A B) :
    ∃ f ∈ PolAB K k (A + 1) (B + 1), ctrF K k f = g := by
  obtain ⟨w, hw, hgw⟩ := decomp_exists hk A B g hg
  have h1 := min_le_left A B
  have h2 := min_le_right A B
  refine ⟨∑ j ∈ range (min A B + 1),
    ((((j + 1) * (A - j + (B - j) + k + j) : ℕ) : K)⁻¹) • (hXY K k ^ (j + 1) * w j), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
    have hj' := Finset.mem_range.1 hj
    have := h_pow_mul_mem (j + 1) (mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.1 (hw j)).1
    rwa [show A - j + (j + 1) = A + 1 by omega, show B - j + (j + 1) = B + 1 by omega] at this
  · rw [map_sum, hgw]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [map_smul, ctr_h_pow_har j (hw j), smul_smul, inv_mul_cancel₀, one_smul]
    exact Nat.cast_ne_zero.2 (Nat.mul_ne_zero (Nat.succ_ne_zero j) (by omega))

theorem levelProj_apply (A B j : ℕ) (f : PolXY K k) : levelProj K k A B j f =
    hXY K k ^ j * (((((A + B + k - 2 * j + j - 1).choose j : ℕ) : K)⁻¹ * ((j.factorial : ℕ) : K)⁻¹) •
      harProj K k (A - j) (B - j) (ctrDiv K k j f)) := by
  simp only [levelProj, LinearMap.smul_apply, LinearMap.comp_apply, hDiv, LinearMap.mulLeft_apply,
    mul_smul_comm, smul_smul]

theorem ctrDiv_mem {A B : ℕ} (j : ℕ) {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    ctrDiv K k j f ∈ PolAB K k (A - j) (B - j) := by
  simp only [ctrDiv, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (ctrF_pow_mem j hf)

theorem levelProj_image [CharZero K] (hk : 1 ≤ k) {A B : ℕ} (j : ℕ) {f : PolXY K k}
    (hf : f ∈ PolAB K k A B) :
    ∃ w ∈ HarAB K k (A - j) (B - j), levelProj K k A B j f = hXY K k ^ j * w := by
  exact ⟨((((A + B + k - 2 * j + j - 1).choose j : ℕ) : K)⁻¹ * ((j.factorial : ℕ) : K)⁻¹) •
    harProj K k (A - j) (B - j) (ctrDiv K k j f),
    Submodule.smul_mem _ _ (harProj_mem hk (ctrDiv_mem j hf)), levelProj_apply A B j f⟩

theorem levelProj_level [CharZero K] (hk : 1 ≤ k) {A B i j : ℕ} (hi : i ≤ min A B) (hj : j ≤ min A B)
    {w : PolXY K k} (hw : w ∈ HarAB K k (A - i) (B - i)) :
    levelProj K k A B j (hXY K k ^ i * w) = if i = j then hXY K k ^ i * w else 0 := by
  rw [levelProj_apply]
  obtain ⟨hw1, hw2⟩ := mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.1 hw
  have hA := min_le_left A B
  have hB := min_le_right A B
  have hc : ctrDiv K k j (hXY K k ^ i * w) = (((j.factorial : ℕ) : K)⁻¹ *
      ((i.descFactorial j * (A - i + (B - i) + k + i - 1).descFactorial j : ℕ) : K)) •
        (hXY K k ^ (i - j) * w) := by
    simp only [ctrDiv, LinearMap.smul_apply]
    rw [ctr_pow_h_pow_har hk hw j i, smul_smul]
  rw [hc]
  rcases lt_trichotomy i j with hij | hij | hij
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 hij, zero_mul, Nat.cast_zero, mul_zero, zero_smul, map_zero,
      smul_zero, mul_zero, if_neg hij.ne]
  · subst hij
    rw [if_pos rfl, Nat.sub_self, pow_zero, one_mul, map_smul, harProj_har hw, smul_smul]
    congr 1
    convert one_smul K w using 2
    have hN : A - i + (B - i) + k + i - 1 = A + B + k - 2 * i + i - 1 := by omega
    have h1 : ((i.factorial : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero i)
    have h2 : (((A + B + k - 2 * i + i - 1).choose i : ℕ) : K) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.choose_pos (by omega)).ne'
    rw [hN, Nat.descFactorial_self, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, Nat.cast_mul]
    field_simp
    all_goals ring
  · rw [if_neg hij.ne', map_smul]
    have hpow : hXY K k ^ (i - j) * w = hXY K k * (hXY K k ^ (i - j - 1) * w) := by
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega)]
    have hg : hXY K k ^ (i - j - 1) * w ∈ PolAB K k (A - j - 1) (B - j - 1) := by
      have := h_pow_mul_mem (i - j - 1) hw1
      rwa [show A - i + (i - j - 1) = A - j - 1 by omega, show B - i + (i - j - 1) = B - j - 1 by omega] at this
    rw [hpow, harProj_kill hk (by omega) (by omega) hg, smul_zero, smul_zero, mul_zero]

theorem levelProj_sum [CharZero K] (hk : 1 ≤ k) {A B : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k A B) :
    ∑ j ∈ range (min A B + 1), levelProj K k A B j f = f := by
  obtain ⟨w, hw, hfw⟩ := decomp_exists hk A B f hf
  conv_rhs => rw [hfw]
  conv_lhs => rw [hfw]
  simp only [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ min A B := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  calc ∑ j ∈ range (min A B + 1), levelProj K k A B j (hXY K k ^ i * w i)
      = ∑ j ∈ range (min A B + 1), if i = j then hXY K k ^ i * w i else 0 :=
        Finset.sum_congr rfl fun j hj =>
          levelProj_level hk hi' (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) (hw i)
    _ = hXY K k ^ i * w i := by rw [Finset.sum_ite_eq, if_pos hi]

end Har2

open Har2

theorem harmonicProjection_holds : HarProj := by
  unfold HarProj
  intro K _ _ k A B hk
  exact ⟨fun f hf => ⟨harProj_mem hk hf, harProj_sub hf⟩, fun f hf => harProj_har hf,
    fun hA hB g hg => harProj_kill hk hA hB hg⟩

theorem isotypicProjection_holds : LevelProj := by
  unfold LevelProj
  intro K _ _ k A B hk
  refine ⟨fun f hf j _ => levelProj_image hk j hf, fun f hf => levelProj_sum hk hf,
    fun f hf i hi j hj => ?_, fun i hi j hj w hw => levelProj_level hk hi hj hw⟩
  obtain ⟨w, hw, he⟩ := levelProj_image hk j hf
  rw [he, levelProj_level hk hj hi hw]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg (Ne.symm h), if_neg h]

theorem laplacianSurjective_holds : CtrSurj := by
  unfold CtrSurj
  intro K _ _ k A B hk g hg
  exact exists_laplacian_eq hk hg

theorem harmonicDecomposition_holds : HarDecomp := by
  unfold HarDecomp
  intro K _ _ k A B hk f hf
  obtain ⟨w, hw, hfw⟩ := decomp_exists hk A B f hf
  have e2 := Fin.sum_univ_eq_sum_range (fun j => hXY K k ^ j * w j) (min A B + 1)
  refine ⟨fun j => w j, ⟨fun j => hw j, hfw.trans e2.symm⟩, ?_⟩
  rintro v ⟨hv, hfv⟩
  funext j
  have key := har_indep hk (min A B + 1) (fun j => A - j) (fun j => B - j)
    (fun j => if h : j < min A B + 1 then v ⟨j, h⟩ - w j else 0)
    (fun j => by
      by_cases h : j < min A B + 1
      · simp only [h, ↓reduceDIte]
        exact Submodule.sub_mem _ (hv ⟨j, h⟩) (hw j)
      · simp only [h, ↓reduceDIte]
        exact Submodule.zero_mem _)
    (by
      have e1 := Fin.sum_univ_eq_sum_range
        (fun j => hXY K k ^ j * (if h : j < min A B + 1 then v ⟨j, h⟩ - w j else 0)) (min A B + 1)
      refine e1.symm.trans ?_
      simp only [Fin.is_lt, ↓reduceDIte, Fin.eta, mul_sub, Finset.sum_sub_distrib]
      rw [← hfv, e2, ← hfw, sub_self])
  have := key j j.isLt
  simp only [j.isLt, ↓reduceDIte, Fin.eta, sub_eq_zero] at this
  exact this

namespace Har2

variable {K : Type} [Field K] {k : ℕ}

theorem polAB_eq_restrict (A B : ℕ) :
    PolAB K k A B = restrictSupport K {m : XY k →₀ ℕ | xDeg m = A ∧ yDeg m = B} := by
  ext f
  rw [mem_PolAB_iff_forall_support_bidegree, MvPolynomial.mem_restrictSupport_iff]
  exact ⟨fun h m hm => h m hm, fun h m hm => h hm⟩

private theorem card_finsupp_fin_sum_eq_choose (n A : ℕ) :
    Nat.card {x : Fin (n + 1) →₀ ℕ // ∑ i, x i = A} = (A + n).choose n := by
  have e : {x : Fin (n + 1) →₀ ℕ // ∑ i, x i = A} ≃ Sym (Fin (n + 1)) A :=
    Equiv.subtypeEquiv Multiset.toFinsupp.symm.toEquiv fun x => by
      simp [Multiset.toFinsupp_symm_apply, Finsupp.card_toMultiset, Finsupp.sum_fintype]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, Fintype.card_fin,
    show n + 1 + A - 1 = A + n by omega, Nat.choose_symm_add]

theorem card_bideg (k' A B : ℕ) :
    Nat.card {m : XY (k' + 1) →₀ ℕ | xDeg m = A ∧ yDeg m = B} =
      (A + k').choose k' * (B + k').choose k' := by
  have e := (Equiv.subtypeEquiv (p := fun m : XY (k' + 1) →₀ ℕ => xDeg m = A ∧ yDeg m = B)
      (q := fun c : (Fin (k' + 1) →₀ ℕ) × (Fin (k' + 1) →₀ ℕ) => (∑ i, c.1 i = A) ∧ (∑ i, c.2 i = B))
      Finsupp.sumFinsuppEquivProdFinsupp fun m => by
        simp [xDeg, yDeg, Finsupp.fst_sumFinsuppEquivProdFinsupp,
          Finsupp.snd_sumFinsuppEquivProdFinsupp]).trans
    (Equiv.subtypeProdEquivProd (p := fun x : Fin (k' + 1) →₀ ℕ => ∑ i, x i = A)
      (q := fun y : Fin (k' + 1) →₀ ℕ => ∑ i, y i = B))
  rw [show Nat.card ↥{m : XY (k' + 1) →₀ ℕ | xDeg m = A ∧ yDeg m = B} = _ from Nat.card_congr e,
    Nat.card_prod]
  exact congrArg₂ (· * ·) (card_finsupp_fin_sum_eq_choose k' A) (card_finsupp_fin_sum_eq_choose k' B)

theorem finrank_polAB (k' A B : ℕ) :
    Module.finrank K (PolAB K (k' + 1) A B) = (A + k').choose k' * (B + k').choose k' := by
  rw [polAB_eq_restrict, ← card_bideg k' A B]
  exact Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport K _)

theorem finite_polAB (k' A B : ℕ) : Module.Finite K (PolAB K (k' + 1) A B) := by
  exact Module.finite_of_finrank_pos (by
    rw [finrank_polAB]
    exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))

theorem finrank_har [CharZero K] (k' A B : ℕ) :
    Module.finrank K (HarAB K (k' + 1) (A + 1) (B + 1)) + Module.finrank K (PolAB K (k' + 1) A B) =
      Module.finrank K (PolAB K (k' + 1) (A + 1) (B + 1)) := by
  have hk1 : (1 : ℕ) ≤ k' + 1 := by omega
  haveI := finite_polAB (K := K) k' (A + 1) (B + 1)
  have hmaps : ∀ x ∈ PolAB K (k' + 1) (A + 1) (B + 1), ctrF K (k' + 1) x ∈ PolAB K (k' + 1) A B :=
    fun x hx => by simpa using ctrF_mem hx
  let φ := (ctrF K (k' + 1)).restrict hmaps
  have hsurj : LinearMap.range φ = ⊤ := by
    refine LinearMap.range_eq_top.2 fun y => ?_
    obtain ⟨f, hf, hfy⟩ := exists_laplacian_eq hk1 y.2
    exact ⟨⟨f, hf⟩, Subtype.ext hfy⟩
  have hker : (LinearMap.ker φ).map (PolAB K (k' + 1) (A + 1) (B + 1)).subtype =
      HarAB K (k' + 1) (A + 1) (B + 1) := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.2 ⟨y.2, congrArg Subtype.val hy⟩
    · intro hx
      obtain ⟨h1, h2⟩ := mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.1 hx
      exact ⟨⟨x, h1⟩, Subtype.ext h2, rfl⟩
  have := LinearMap.finrank_range_add_finrank_ker φ
  rw [hsurj, finrank_top, ← Submodule.finrank_map_subtype_eq, hker] at this
  omega

end Har2

theorem harmonicFinrank_holds : HarDim := by
  unfold HarDim
  intro K _ _ k' A B
  refine ⟨finrank_polAB k' A B, ?_, ?_, ?_⟩
  · rw [← finrank_polAB (K := K) k' A B, ← finrank_polAB (K := K) k' (A + 1) (B + 1)]
    exact finrank_har k' A B
  · ext f
    exact ⟨fun h => (mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.1 h).1, har_of_right⟩
  · ext f
    exact ⟨fun h => (mem_HarAB_iff_mem_PolAB_and_ctrF_eq_zero.1 h).1, har_of_left⟩

end Formalism.CountingSumsFrames
