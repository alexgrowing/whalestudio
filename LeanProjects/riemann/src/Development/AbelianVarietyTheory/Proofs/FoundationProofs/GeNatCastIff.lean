import Mathlib

namespace GlobalTheory.AxSen

variable {K : Type} [Field K]

def Ge (A : ValuationSubring K) (ϖ w : K) (q : ℚ) : Prop :=
  ∀ (a : ℤ) (b : ℕ), 0 < b → (a : ℚ) ≤ q * b → A.valuation w ^ b ≤ A.valuation ϖ ^ a

variable {A : ValuationSubring K} {ϖ : K}

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.ge_zero (q : ℚ) : _root_.GlobalTheory.AxSen.Ge A ϖ 0 q := by
  intro a b hb _
  rw [map_zero, zero_pow hb.ne']
  exact zero_le'

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.mono {w : K} {q q' : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ w q) (hq : q' ≤ q) :
    _root_.GlobalTheory.AxSen.Ge A ϖ w q' :=
  fun a b hb hab => h a b hb (hab.trans (mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg b)))

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.of_le {w w' : K} {q : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ w q) (hw : A.valuation w' ≤ A.valuation w) :
    _root_.GlobalTheory.AxSen.Ge A ϖ w' q :=
  fun a b hb hab => (pow_le_pow_left' hw b).trans (h a b hb hab)

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.add {w w' : K} {q : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ w q) (h' : _root_.GlobalTheory.AxSen.Ge A ϖ w' q) :
    _root_.GlobalTheory.AxSen.Ge A ϖ (w + w') q := by
  rcases le_total (A.valuation w) (A.valuation w') with hle | hle
  · exact h'.of_le ((Valuation.map_add _ _ _).trans (max_le hle le_rfl))
  · exact h.of_le ((Valuation.map_add _ _ _).trans (max_le le_rfl hle))

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.symm {x y : K} {q : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ (x - y) q) : _root_.GlobalTheory.AxSen.Ge A ϖ (y - x) q :=
  h.of_le (by rw [Valuation.map_sub_swap])

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.trans {x y z : K} {q : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ (x - y) q) (h' : _root_.GlobalTheory.AxSen.Ge A ϖ (y - z) q) :
    _root_.GlobalTheory.AxSen.Ge A ϖ (x - z) q := by
  have := h.add h'
  rwa [sub_add_sub_cancel] at this

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.mul (h0 : ϖ ≠ 0) (h1 : A.valuation ϖ ≤ 1)
    {w w' : K} {q q' : ℚ} (h : _root_.GlobalTheory.AxSen.Ge A ϖ w q)
    (h' : _root_.GlobalTheory.AxSen.Ge A ϖ w' q') :
    _root_.GlobalTheory.AxSen.Ge A ϖ (w * w') (q + q') := by
  intro a b hb hab
  have hv : A.valuation ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have hd : 0 < q.den := q.den_pos
  have hd' : 0 < q'.den := q'.den_pos
  have h₁ := h (q.num * q'.den * b) (q.den * q'.den * b) (by positivity)
    (le_of_eq (by push_cast; rw [← Rat.mul_den_eq_num q]; ring))
  have h₂ := h' (q'.num * q.den * b) (q.den * q'.den * b) (by positivity)
    (le_of_eq (by push_cast; rw [← Rat.mul_den_eq_num q']; ring))
  have hexp : a * ((q.den * q'.den : ℕ) : ℤ) ≤ (q.num * q'.den * b + q'.num * q.den * b) := by
    have hq : ((a * ((q.den * q'.den : ℕ) : ℤ) : ℤ) : ℚ)
        ≤ ((q.num * q'.den * b + q'.num * q.den * b : ℤ) : ℚ) := by
      push_cast
      rw [← Rat.mul_den_eq_num q, ← Rat.mul_den_eq_num q']
      have hdd : (0 : ℚ) ≤ q.den * q'.den := by positivity
      calc (a : ℚ) * (q.den * q'.den) ≤ ((q + q') * b) * (q.den * q'.den) :=
            mul_le_mul_of_nonneg_right hab hdd
        _ = _ := by ring
    exact_mod_cast hq
  have key : (A.valuation (w * w') ^ b) ^ (q.den * q'.den)
      ≤ (A.valuation ϖ ^ a) ^ (q.den * q'.den) := by
    calc (A.valuation (w * w') ^ b) ^ (q.den * q'.den)
        = A.valuation w ^ (q.den * q'.den * b) * A.valuation w' ^ (q.den * q'.den * b) := by
          rw [map_mul, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm b]
      _ ≤ A.valuation ϖ ^ (q.num * q'.den * b) * A.valuation ϖ ^ (q'.num * q.den * b) :=
          mul_le_mul' h₁ h₂
      _ = A.valuation ϖ ^ (q.num * q'.den * b + q'.num * q.den * b) := by
          rw [← zpow_add₀ hv]
      _ ≤ A.valuation ϖ ^ (a * ((q.den * q'.den : ℕ) : ℤ)) :=
          zpow_le_zpow_right_of_le_one₀ (zero_lt_iff.2 hv) h1 hexp
      _ = (A.valuation ϖ ^ a) ^ (q.den * q'.den) := by rw [zpow_mul, zpow_natCast]
  exact (pow_le_pow_iff_left₀ zero_le' zero_le' (by positivity)).1 key

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.root {w : K} {q : ℚ} {N : ℕ} (hN : 0 < N)
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ (w ^ N) (q * N)) : _root_.GlobalTheory.AxSen.Ge A ϖ w q := by
  intro a b hb hab
  have h₁ := h (a * N) b hb (by
    push_cast
    calc (a : ℚ) * N ≤ q * b * N := mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg N)
      _ = q * N * b := by ring)
  refine (pow_le_pow_iff_left₀ zero_le' zero_le' hN.ne').1 ?_
  calc (A.valuation w ^ b) ^ N = A.valuation (w ^ N) ^ b := by
        rw [map_pow, ← pow_mul, ← pow_mul, mul_comm]
    _ ≤ A.valuation ϖ ^ (a * (N : ℤ)) := h₁
    _ = (A.valuation ϖ ^ a) ^ N := by rw [zpow_mul, zpow_natCast]

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.Ge.div (h0 : ϖ ≠ 0) (h1 : A.valuation ϖ ≤ 1)
    {c w : K} {q : ℚ} {e : ℕ} (hc : A.valuation ϖ ^ e ≤ A.valuation c)
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ (c * w) q) :
    _root_.GlobalTheory.AxSen.Ge A ϖ w (q - e) := by
  intro a b hb hab
  have hv : A.valuation ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have hc0 : A.valuation c ≠ 0 := by
    intro hc0
    rw [hc0] at hc
    exact pow_ne_zero e hv (le_zero_iff.1 hc)
  have h₁ := h (a + e * b) b hb (by push_cast; linarith [hab, sub_mul q (e : ℚ) b])
  rw [map_mul, mul_pow, zpow_add₀ hv] at h₁
  have h₂ : A.valuation ϖ ^ ((e : ℤ) * (b : ℤ)) ≤ A.valuation c ^ b := by
    rw [zpow_mul, zpow_natCast, zpow_natCast]
    exact pow_le_pow_left' hc b
  refine (mul_le_mul_iff_of_pos_right (zero_lt_iff.2 (pow_ne_zero b hc0))).1 ?_
  calc A.valuation w ^ b * A.valuation c ^ b = A.valuation c ^ b * A.valuation w ^ b := mul_comm _ _
    _ ≤ A.valuation ϖ ^ a * A.valuation ϖ ^ ((e : ℤ) * (b : ℤ)) := h₁
    _ ≤ A.valuation ϖ ^ a * A.valuation c ^ b := mul_le_mul' le_rfl h₂

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in
theorem _root_.GlobalTheory.AxSen.ge_natCast_iff (h0 : ϖ ≠ 0) (h1 : A.valuation ϖ ≤ 1) {w : K}
    {m : ℕ} : _root_.GlobalTheory.AxSen.Ge A ϖ w m ↔ ∃ z ∈ A, w = ϖ ^ m * z := by
  have hv : A.valuation ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  constructor
  · intro h
    have h₁ := h m 1 one_pos (by simp)
    rw [pow_one, zpow_natCast, ← map_pow] at h₁
    refine ⟨w / ϖ ^ m, ?_, by field_simp⟩
    rw [← ValuationSubring.valuation_le_one_iff, map_div₀]
    exact (div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (pow_ne_zero m h0)))).2 h₁
  · rintro ⟨z, hz, rfl⟩ a b hb hab
    have hz' : A.valuation z ≤ 1 := (ValuationSubring.valuation_le_one_iff A z).2 hz
    have hab' : a ≤ ((m * b : ℕ) : ℤ) := by
      have : (a : ℚ) ≤ ((m * b : ℕ) : ℚ) := by push_cast; exact hab
      exact_mod_cast this
    rw [map_mul, mul_pow, map_pow]
    calc (A.valuation ϖ ^ m) ^ b * A.valuation z ^ b ≤ (A.valuation ϖ ^ m) ^ b * 1 :=
          mul_le_mul' le_rfl (pow_le_one' hz' b)
      _ = A.valuation ϖ ^ ((m * b : ℕ) : ℤ) := by rw [mul_one, ← pow_mul, zpow_natCast]
      _ ≤ A.valuation ϖ ^ a := zpow_le_zpow_right_of_le_one₀ (zero_lt_iff.2 hv) h1 hab'

variable {K : Type} [Field K] in
variable {A : ValuationSubring K} {ϖ : K} in

theorem _root_.GlobalTheory.AxSen.Ge.map (h0 : ϖ ≠ 0) (f : K →+* K)
    (hf : ∀ x ∈ A, f x ∈ A) (hϖ : f ϖ = ϖ) {w : K} {q : ℚ}
    (h : _root_.GlobalTheory.AxSen.Ge A ϖ w q) : _root_.GlobalTheory.AxSen.Ge A ϖ (f w) q := by
  intro a b hb hab
  have hv : A.valuation ϖ ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have h₁ := h a b hb hab
  have hpos : 0 < A.valuation ϖ ^ a := zero_lt_iff.2 (zpow_ne_zero a hv)
  rw [← div_le_one₀ hpos, ← map_pow, ← map_zpow₀, ← map_div₀,
    ValuationSubring.valuation_le_one_iff] at h₁ ⊢
  have := hf _ h₁
  rwa [map_div₀, map_pow, map_zpow₀, hϖ] at this

end GlobalTheory.AxSen
