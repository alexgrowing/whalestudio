import Mathlib

noncomputable section

namespace PI.WADVR

variable {W Q : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Q]
  [Algebra W Q] [IsFractionRing W Q]

def Sm (Q : Type*) [Field Q] [Algebra W Q] (ϖ : W) (k : ℤ) (q : Q) : Prop :=
  ∃ c : W, q = algebraMap W Q ϖ ^ k * algebraMap W Q c

variable {ϖ : W}

lemma alg_ne_zero (hϖ : Irreducible ϖ) : algebraMap W Q ϖ ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective W Q)).mpr hϖ.ne_zero

lemma Sm.mul (hϖ : Irreducible ϖ) {k l : ℤ} {a b : Q} (ha : Sm Q ϖ k a) (hb : Sm Q ϖ l b) :
    Sm Q ϖ (k + l) (a * b) := by
  obtain ⟨c, rfl⟩ := ha
  obtain ⟨d, rfl⟩ := hb
  refine ⟨c * d, ?_⟩
  rw [zpow_add₀ (alg_ne_zero hϖ), map_mul]
  ring

lemma Sm.add {k : ℤ} {a b : Q} (ha : Sm Q ϖ k a) (hb : Sm Q ϖ k b) : Sm Q ϖ k (a + b) := by
  obtain ⟨c, rfl⟩ := ha
  obtain ⟨d, rfl⟩ := hb
  exact ⟨c + d, by rw [map_add]; ring⟩

lemma Sm.neg {k : ℤ} {a : Q} (ha : Sm Q ϖ k a) : Sm Q ϖ k (-a) := by
  obtain ⟨c, rfl⟩ := ha
  exact ⟨-c, by rw [map_neg]; ring⟩

lemma Sm.sub {k : ℤ} {a b : Q} (ha : Sm Q ϖ k a) (hb : Sm Q ϖ k b) : Sm Q ϖ k (a - b) := by
  rw [sub_eq_add_neg]; exact ha.add hb.neg

lemma Sm.zero (k : ℤ) : Sm Q ϖ k (0 : Q) := ⟨0, by simp⟩

lemma Sm.alg (w : W) : Sm Q ϖ 0 (algebraMap W Q w) := ⟨w, by simp⟩

lemma Sm.one : Sm Q ϖ 0 (1 : Q) := ⟨1, by simp⟩

lemma Sm.mono (hϖ : Irreducible ϖ) {k l : ℤ} {a : Q} (ha : Sm Q ϖ k a) (h : l ≤ k) :
    Sm Q ϖ l a := by
  obtain ⟨c, rfl⟩ := ha
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h)
  refine ⟨ϖ ^ n * c, ?_⟩
  have : k = l + (n : ℤ) := by omega
  rw [this, zpow_add₀ (alg_ne_zero hϖ), zpow_natCast, map_mul, map_pow]
  ring

lemma Sm.pow (hϖ : Irreducible ϖ) {k : ℤ} {a : Q} (ha : Sm Q ϖ k a) (r : ℕ) :
    Sm Q ϖ (k * r) (a ^ r) := by
  induction r with
  | zero => simpa using (Sm.one (ϖ := ϖ) (Q := Q))
  | succ r ih =>
    have := ih.mul hϖ ha
    rw [pow_succ]
    convert this using 1
    push_cast; ring

lemma sm_zero_iff {q : Q} : Sm Q ϖ 0 q ↔ q ∈ Set.range (algebraMap W Q) := by
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨c, by simp⟩
  · rintro ⟨c, rfl⟩; exact Sm.alg c

lemma sm_one_of_mem (hϖ : Irreducible ϖ) {w : W} (hw : w ∈ IsLocalRing.maximalIdeal W) :
    Sm Q ϖ 1 (algebraMap W Q w) := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
    Ideal.mem_span_singleton'] at hw
  obtain ⟨c, rfl⟩ := hw
  exact ⟨c, by rw [zpow_one, map_mul]; ring⟩

lemma sm_one_of_not_isUnit (hϖ : Irreducible ϖ) {w : W} (hw : ¬ IsUnit w) :
    Sm Q ϖ 1 (algebraMap W Q w) :=
  sm_one_of_mem hϖ ((IsLocalRing.mem_maximalIdeal _).mpr hw)

lemma big_of_not_mem (hϖ : Irreducible ϖ) {q : Q} (hq : q ∉ Set.range (algebraMap W Q)) :
    q ≠ 0 ∧ Sm Q ϖ 1 q⁻¹ := by
  have hq0 : q ≠ 0 := by rintro rfl; exact hq ⟨0, by simp⟩
  refine ⟨hq0, ?_⟩
  rcases ValuationRing.isInteger_or_isInteger W q with ⟨w, hw⟩ | ⟨w, hw⟩
  · exact absurd ⟨w, hw⟩ hq
  · refine hw ▸ sm_one_of_not_isUnit hϖ ?_
    rintro ⟨u, rfl⟩
    apply hq
    refine ⟨((u⁻¹ : Wˣ) : W), ?_⟩
    have h1 : algebraMap W Q (u : W) * algebraMap W Q ((u⁻¹ : Wˣ) : W) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [hw] at h1
    field_simp at h1
    exact h1

lemma sm_exists (hϖ : Irreducible ϖ) (q : Q) : ∃ k : ℤ, Sm Q ϖ k q := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) q
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hϖ
  refine ⟨-(n : ℤ), a * ((u : W)), ?_⟩
  have hbQ : algebraMap W Q b ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective W Q)).mpr hb0
  have hu' : algebraMap W Q b * algebraMap W Q (u : W) = algebraMap W Q ϖ ^ n := by
    rw [← map_mul, hu, map_pow]
  rw [zpow_neg, zpow_natCast, ← hu', map_mul]
  have hU : algebraMap W Q (u : W) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W Q)).mpr u.ne_zero
  field_simp

lemma one_add_of_sm (hϖ : Irreducible ϖ) {t : Q} (ht : Sm Q ϖ 1 t) :
    1 + t ≠ 0 ∧ Sm Q ϖ 0 (1 + t)⁻¹ := by
  obtain ⟨c, rfl⟩ := ht
  have hm : -(ϖ * c) ∈ nonunits W := by
    rw [← IsLocalRing.mem_maximalIdeal, Ideal.neg_mem_iff]
    exact Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit)
  obtain ⟨u, hu⟩ := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hm
  have he : (1 : Q) + algebraMap W Q ϖ ^ (1 : ℤ) * algebraMap W Q c = algebraMap W Q (u : W) := by
    rw [hu, zpow_one, sub_neg_eq_add, map_add, map_one, map_mul]
  have hU : algebraMap W Q (u : W) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective W Q)).mpr u.ne_zero
  refine ⟨he ▸ hU, ?_⟩
  rw [he]
  refine ⟨((u⁻¹ : Wˣ) : W), ?_⟩
  have h1 : algebraMap W Q (u : W) * algebraMap W Q ((u⁻¹ : Wˣ) : W) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [zpow_zero, one_mul]
  exact (eq_inv_of_mul_eq_one_right h1).symm

lemma sm_natCast (hϖ : Irreducible ϖ) {p : ℕ} (hp : ¬ IsUnit (p : W)) : Sm Q ϖ 1 (p : Q) := by
  have := sm_one_of_not_isUnit (Q := Q) hϖ hp
  rwa [map_natCast] at this

lemma exists_sm_target (hϖ : Irreducible ϖ) {p : ℕ} (hp : (p : Q) ≠ 0) (N : ℕ) :
    ∃ n : ℕ, ∀ q : Q, Sm Q ϖ n q → ∃ c : W, q = (p : Q) ^ N * algebraMap W Q c := by
  have hpW : ((p : W) ^ N) ≠ 0 := by
    refine pow_ne_zero _ ?_
    intro h
    apply hp
    rw [← map_natCast (algebraMap W Q), h, map_zero]
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hpW hϖ
  refine ⟨n, fun q ⟨c, hc⟩ => ⟨(u : W) * c, ?_⟩⟩
  rw [hc, zpow_natCast, ← map_pow, ← hu, ← map_natCast (algebraMap W Q), ← map_pow, ← map_mul,
    ← map_mul, mul_assoc]

lemma sm_of_density (hϖ : Irreducible ϖ) {p : ℕ} (hp : ¬ IsUnit (p : W)) {y x : Q} {N : ℕ}
    {c : W} (h : y = x + (p : Q) ^ N * algebraMap W Q c) : Sm Q ϖ N (y - x) := by
  have h1 := ((sm_natCast (Q := Q) hϖ hp).pow hϖ N).mul hϖ (Sm.alg c)
  rw [h, add_sub_cancel_left]
  simpa using h1

lemma big_one_add_pow (hϖ : Irreducible ϖ) {q : Q} (h0 : q ≠ 0) (h : Sm Q ϖ 1 q⁻¹) {r : ℕ}
    (hr : 1 ≤ r) : 1 + q ^ r ≠ 0 ∧ Sm Q ϖ r (1 + q ^ r)⁻¹ := by
  have ht : Sm Q ϖ r (q⁻¹ ^ r) := by simpa using h.pow hϖ r
  have ht1 : Sm Q ϖ 1 (q⁻¹ ^ r) := ht.mono hϖ (by exact_mod_cast hr)
  obtain ⟨h1, h2⟩ := one_add_of_sm hϖ ht1
  have hid : 1 + q ^ r = q ^ r * (1 + q⁻¹ ^ r) := by
    rw [mul_add, mul_one, ← mul_pow, mul_inv_cancel₀ h0, one_pow]; ring
  have hqr : q ^ r ≠ 0 := pow_ne_zero _ h0
  refine ⟨hid ▸ mul_ne_zero hqr h1, ?_⟩
  have := ht.mul hϖ h2
  rw [add_zero] at this
  convert this using 1
  rw [hid, mul_inv, inv_pow]

lemma small_one_add_pow (hϖ : Irreducible ϖ) {q : Q} (h : Sm Q ϖ 1 q) {r : ℕ} (hr : 1 ≤ r) :
    1 + q ^ r ≠ 0 ∧ Sm Q ϖ r (q ^ r * (1 + q ^ r)⁻¹) := by
  have ht : Sm Q ϖ r (q ^ r) := by simpa using h.pow hϖ r
  obtain ⟨h1, h2⟩ := one_add_of_sm hϖ (ht.mono hϖ (by exact_mod_cast hr))
  refine ⟨h1, ?_⟩
  simpa using ht.mul hϖ h2

lemma Sm.of_toNat (hϖ : Irreducible ϖ) {k : ℤ} {a : Q} (ha : Sm Q ϖ (k.toNat : ℤ) a) :
    Sm Q ϖ k a :=
  ha.mono hϖ (Int.self_le_toNat k)

end PI.WADVR
