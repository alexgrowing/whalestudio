import Mathlib
import ReciprocityTheory.GaloisValuations.Global

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField

namespace GlobalTheory.CycInertial

variable {K : Type} [Field K] {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

theorem val_le_one (w : Valuation K Γ) {z : K} {n : ℕ} (hn : n ≠ 0) (hz : z ^ n = 1)
    (r : Algebra.adjoin ℤ ({z} : Set K)) : w (r : K) ≤ 1 := by
  have hz1 : w z ≤ 1 := by
    by_contra h
    push_neg at h
    have h2 : w z ^ n = 1 := by rw [← map_pow, hz, map_one]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [pow_succ] at h2
    have h3 := mul_le_mul' (one_le_pow₀ h.le : 1 ≤ w z ^ m) (le_refl (w z))
    rw [one_mul, h2] at h3
    exact absurd h (not_lt.mpr h3)
  obtain ⟨r, hr⟩ := r
  show w r ≤ 1
  induction hr using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact hz1
  | algebraMap m =>
    rw [algebraMap_int_eq, eq_intCast]
    exact (Valuation.mem_integer_iff w _).mp (intCast_mem _ m)
  | add x y _ _ ihx ihy => exact (w.map_add x y).trans (max_le ihx ihy)
  | mul x y _ _ ihx ihy => rw [map_mul]; exact mul_le_one' ihx ihy

noncomputable def gen (z : K) : Algebra.adjoin ℤ ({z} : Set K) :=
  ⟨z, Algebra.subset_adjoin rfl⟩

@[simp] theorem coe_gen (z : K) : (gen z : K) = z := rfl

theorem exists_int (z : K) (r : Algebra.adjoin ℤ ({z} : Set K)) :
    ∃ (m : ℤ) (s : Algebra.adjoin ℤ ({z} : Set K)), r = m + (gen z - 1) * s := by
  obtain ⟨r, hr⟩ := r
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact ⟨1, 1, Subtype.ext (by simp)⟩
  | algebraMap m => exact ⟨m, 0, Subtype.ext (by simp)⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨m₁, s₁, h₁⟩ := ihx
    obtain ⟨m₂, s₂, h₂⟩ := ihy
    refine ⟨m₁ + m₂, s₁ + s₂, Subtype.ext ?_⟩
    have e₁ := congrArg Subtype.val h₁
    have e₂ := congrArg Subtype.val h₂
    push_cast [coe_gen, Subtype.coe_mk] at e₁ e₂ ⊢
    rw [e₁, e₂]; ring
  | mul x y hx hy ihx ihy =>
    obtain ⟨m₁, s₁, h₁⟩ := ihx
    obtain ⟨m₂, s₂, h₂⟩ := ihy
    refine ⟨m₁ * m₂, (m₁ : Algebra.adjoin ℤ ({z} : Set K)) * s₂ + s₁ * m₂ + (gen z - 1) * s₁ * s₂,
      Subtype.ext ?_⟩
    have e₁ := congrArg Subtype.val h₁
    have e₂ := congrArg Subtype.val h₂
    push_cast [coe_gen, Subtype.coe_mk] at e₁ e₂ ⊢
    rw [e₁, e₂]; ring

theorem val_sub_one_lt (w : Valuation K Γ) {l k : ℕ} (hl : l.Prime) (hw : w (l : K) < 1)
    {z : K} (hz : z ^ (l ^ k) = 1) : w (z - 1) < 1 := by
  have hn : l ^ k ≠ 0 := pow_ne_zero _ hl.ne_zero
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hl (gen z - 1) 1 k
  have e := congrArg Subtype.val hr
  push_cast [coe_gen] at e
  have key : (z - 1) ^ (l ^ k) = -((l : K) * (z - 1) * (r : K)) := by
    linear_combination -e + hz
  have h₁ : w (z - 1) ≤ 1 := by simpa using val_le_one w hn hz (gen z - 1)
  have h₂ : w (r : K) ≤ 1 := val_le_one w hn hz r
  have h₃ : w (z - 1) ^ (l ^ k) < 1 := by
    rw [← map_pow, key, Valuation.map_neg, map_mul, map_mul]
    calc w (l : K) * w (z - 1) * w (r : K) ≤ w (l : K) * 1 * 1 :=
          mul_le_mul' (mul_le_mul' le_rfl h₁) h₂
      _ < 1 := by simpa using hw
  by_contra h
  push_neg at h
  exact absurd h₃ (not_lt.mpr (one_le_pow₀ h))

theorem sub_one_dvd [CharZero K] {l k : ℕ} [Fact l.Prime] {z : K}
    (hz : IsPrimitiveRoot z (l ^ (k + 1))) :
    gen z - 1 ∣ (l : Algebra.adjoin ℤ ({z} : Set K)) := by
  have hl := (Fact.out : l.Prime)
  have hζ : IsPrimitiveRoot (z ^ l ^ k) l := by
    have := hz.pow_of_dvd (pow_ne_zero k hl.ne_zero) (pow_dvd_pow l k.le_succ)
    rwa [pow_succ, Nat.mul_div_cancel_left _ (pow_pos hl.pos k)] at this
  have hsum := hζ.geom_sum_eq_zero hl.one_lt
  have key : (l : Algebra.adjoin ℤ ({z} : Set K)) =
      ∑ i ∈ Finset.range l, (1 - (gen z ^ l ^ k) ^ i) := by
    apply Subtype.ext
    push_cast [coe_gen]
    rw [Finset.sum_sub_distrib, hsum]
    simp
  rw [key]
  refine Finset.dvd_sum fun i _ => ?_
  rw [← neg_sub ((gen z ^ l ^ k) ^ i) 1, dvd_neg, ← pow_mul]
  exact sub_one_dvd_pow_sub_one _ _

theorem val_eq_one [CharZero K] (w : Valuation K Γ) {l k : ℕ} [Fact l.Prime] (hw : w (l : K) < 1)
    {z : K} (hz : IsPrimitiveRoot z (l ^ (k + 1))) (u : Algebra.adjoin ℤ ({z} : Set K))
    (hu : ¬ gen z - 1 ∣ u) : w (u : K) = 1 := by
  have hl := (Fact.out : l.Prime)
  have hn : l ^ (k + 1) ≠ 0 := pow_ne_zero _ hl.ne_zero
  obtain ⟨m, s, rfl⟩ := exists_int z u
  have hm : ¬ (l : ℤ) ∣ m := by
    rintro ⟨c, rfl⟩
    apply hu
    obtain ⟨t, ht⟩ := sub_one_dvd hz
    exact ⟨t * c + s, by push_cast; rw [ht]; ring⟩
  have hint : ∀ a : ℤ, w (a : K) ≤ 1 := fun a => by
    simpa using val_le_one w hn hz.pow_eq_one (a : Algebra.adjoin ℤ ({z} : Set K))
  have hwm : w (m : K) = 1 := by
    refine le_antisymm (hint m) ?_
    by_contra h
    push_neg at h
    obtain ⟨a, b, hab⟩ :=
      (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hl).irreducible).mpr hm
    have e : ((a * l + b * m : ℤ) : K) = 1 := by rw [hab]; simp
    push_cast at e
    have h₀ := w.map_add ((a : K) * l) ((b : K) * m)
    rw [e, map_one, map_mul, map_mul] at h₀
    have h₁ : w (a : K) * w (l : K) < 1 :=
      lt_of_le_of_lt (by simpa using mul_le_mul' (hint a) (le_refl (w (l : K)))) hw
    have h₂ : w (b : K) * w (m : K) < 1 :=
      lt_of_le_of_lt (by simpa using mul_le_mul' (hint b) (le_refl (w (m : K)))) h
    exact absurd h₀ (not_le.mpr (max_lt h₁ h₂))
  have hzs : w ((z - 1) * s) < 1 := by
    rw [map_mul]
    calc w (z - 1) * w (s : K) ≤ w (z - 1) * 1 :=
          mul_le_mul' le_rfl (val_le_one w hn hz.pow_eq_one s)
      _ < 1 := by rw [mul_one]; exact val_sub_one_lt w hl hw hz.pow_eq_one
  push_cast [coe_gen]
  rw [Valuation.map_add_eq_of_lt_left _ (by rw [hwm]; exact hzs), hwm]

theorem exists_shape [CharZero K] (w : Valuation K Γ) {l k : ℕ} [Fact l.Prime] (hw : w (l : K) < 1)
    {z : K} (hz : IsPrimitiveRoot z (l ^ (k + 1))) (r s : Algebra.adjoin ℤ ({z} : Set K))
    (hs : s ≠ 0) :
    (∃ r' u : Algebra.adjoin ℤ ({z} : Set K), ¬ gen z - 1 ∣ u ∧ (r : K) / s = r' / u) ∨
    (∃ u s' : Algebra.adjoin ℤ ({z} : Set K), ¬ gen z - 1 ∣ u ∧ s' ≠ 0 ∧
      (r : K) / s = u / ((z - 1) * s')) := by
  have hl := (Fact.out : l.Prime)
  have hn : l ^ (k + 1) ≠ 0 := pow_ne_zero _ hl.ne_zero
  have : IsNoetherianRing (Algebra.adjoin ℤ ({z} : Set K)) :=
    isNoetherianRing_of_fg ⟨{z}, by simp⟩
  have hz1 : w (z - 1) < 1 := val_sub_one_lt w hl hw hz.pow_eq_one
  have hz0 : z - 1 ≠ 0 := fun h =>
    hz.ne_one (Nat.one_lt_pow (Nat.succ_ne_zero k) hl.one_lt) (sub_eq_zero.mp h)
  have hnz : gen z - 1 ≠ 0 := fun h => hz0 (by simpa using congrArg Subtype.val h)
  have hnu : ¬ IsUnit (gen z - 1) := by
    intro h
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp h
    have e := congrArg (fun t : Algebra.adjoin ℤ ({z} : Set K) => w (t : K)) hy
    push_cast [coe_gen] at e
    rw [map_mul, map_one] at e
    have h₁ : w (z - 1) * w (y : K) < 1 :=
      (mul_le_mul' (le_refl (w (z - 1))) (val_le_one w hn hz.pow_eq_one y)).trans_lt
        (by rwa [mul_one])
    exact absurd e h₁.ne
  obtain ⟨b, s₀, hs₀, hseq⟩ := WfDvdMonoid.max_power_factor' hs hnu
  have hs₀' : s₀ ≠ 0 := by rintro rfl; exact hs₀ (dvd_zero _)
  have hs₀K : (s₀ : K) ≠ 0 := by exact_mod_cast hs₀'
  by_cases hr : r = 0
  · left
    refine ⟨0, 1, fun h => hnu (isUnit_iff_dvd_one.mpr h), ?_⟩
    subst hr
    simp
  obtain ⟨a, r₀, hr₀, hreq⟩ := WfDvdMonoid.max_power_factor' hr hnu
  rcases le_or_gt b a with hab | hab
  · left
    obtain ⟨c, rfl⟩ : ∃ c, a = b + c := ⟨a - b, by omega⟩
    refine ⟨(gen z - 1) ^ c * r₀, s₀, hs₀, ?_⟩
    rw [hreq, hseq]
    push_cast [coe_gen]
    rw [div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hz0) hs₀K) hs₀K]
    ring
  · right
    obtain ⟨c, rfl⟩ : ∃ c, b = a + c + 1 := ⟨b - a - 1, by omega⟩
    refine ⟨r₀, (gen z - 1) ^ c * s₀, hr₀, mul_ne_zero (pow_ne_zero _ hnz) hs₀', ?_⟩
    rw [hreq, hseq]
    push_cast [coe_gen]
    rw [div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hz0) hs₀K)
      (mul_ne_zero hz0 (mul_ne_zero (pow_ne_zero _ hz0) hs₀K))]
    ring

theorem not_le_one [CharZero K] (w : Valuation K Γ) {l k : ℕ} [Fact l.Prime] (hw : w (l : K) < 1)
    {z : K} (hz : IsPrimitiveRoot z (l ^ (k + 1))) (u s : Algebra.adjoin ℤ ({z} : Set K))
    (hu : ¬ gen z - 1 ∣ u) (hs : s ≠ 0) : ¬ w ((u : K) / ((z - 1) * s)) ≤ 1 := by
  intro h
  have hl := (Fact.out : l.Prime)
  have hn : l ^ (k + 1) ≠ 0 := pow_ne_zero _ hl.ne_zero
  have hz0 : z - 1 ≠ 0 := fun h =>
    hz.ne_one (Nat.one_lt_pow (Nat.succ_ne_zero k) hl.one_lt) (sub_eq_zero.mp h)
  have hsK : (s : K) ≠ 0 := by exact_mod_cast hs
  have hd0 : (z - 1) * (s : K) ≠ 0 := mul_ne_zero hz0 hsK
  have hd : w ((z - 1) * s) < 1 := by
    rw [map_mul]
    calc w (z - 1) * w (s : K) ≤ w (z - 1) * 1 :=
          mul_le_mul' le_rfl (val_le_one w hn hz.pow_eq_one s)
      _ < 1 := by rw [mul_one]; exact val_sub_one_lt w hl hw hz.pow_eq_one
  have e : (u : K) = u / ((z - 1) * s) * ((z - 1) * s) := (div_mul_cancel₀ _ hd0).symm
  have e' := congrArg w e
  rw [map_mul, val_eq_one w hw hz u hu] at e'
  have h₁ : w ((u : K) / ((z - 1) * s)) * w ((z - 1) * s) < 1 :=
    lt_of_le_of_lt (by simpa using mul_le_mul' h (le_refl (w ((z - 1) * s)))) hd
  exact absurd e' (ne_of_gt h₁)

private theorem ringHom_adjoin_primitiveRoot_eq_add_mul_sub_one {z : K} {n : ℕ} [NeZero n] (hz : IsPrimitiveRoot z n)
    (τ : K →+* K) (r : Algebra.adjoin ℤ ({z} : Set K)) :
    ∃ t : Algebra.adjoin ℤ ({z} : Set K), τ r = r + (z - 1) * t := by
  obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one (ξ := τ z) (by rw [← map_pow, hz.pow_eq_one, map_one])
  obtain ⟨c, hc⟩ := sub_one_dvd_pow_sub_one (gen z) i
  have ec := congrArg Subtype.val hc
  push_cast [coe_gen] at ec
  obtain ⟨r, hr⟩ := r
  show ∃ t : Algebra.adjoin ℤ ({z} : Set K), τ r = r + (z - 1) * t
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx]
    refine ⟨c - 1, ?_⟩
    push_cast
    rw [← hi]
    linear_combination ec
  | algebraMap m => exact ⟨0, by simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨t₁, h₁⟩ := ihx
    obtain ⟨t₂, h₂⟩ := ihy
    exact ⟨t₁ + t₂, by push_cast; rw [map_add, h₁, h₂]; ring⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨t₁, h₁⟩ := ihx
    obtain ⟨t₂, h₂⟩ := ihy
    refine ⟨t₁ * ⟨y, hy⟩ + ⟨x, hx⟩ * t₂ + (gen z - 1) * t₁ * t₂, ?_⟩
    push_cast [coe_gen, Subtype.coe_mk]
    rw [map_mul, h₁, h₂]
    ring

private theorem inv_lt_one_of_one_lt' {a : Γ} (h : 1 < a) : a⁻¹ < 1 := by
  have ha : a ≠ 0 := by
    rintro rfl
    exact absurd h (not_lt.mpr zero_le)
  by_contra h'
  push_neg at h'
  have h₁ := mul_le_mul' (le_refl a) h'
  rw [mul_one, mul_inv_cancel₀ ha] at h₁
  exact absurd h (not_lt.mpr h₁)

theorem core [CharZero K] (w : Valuation K Γ) {l k : ℕ} [Fact l.Prime] (hw : w (l : K) < 1)
    {z : K} (hz : IsPrimitiveRoot z (l ^ (k + 1)))
    (hfrac : ∀ x : K, ∃ r s : Algebra.adjoin ℤ ({z} : Set K), s ≠ 0 ∧ x = r / s) (τ : K →+* K) :
    (∀ x, w x ≤ 1 → w (τ x - x) < 1) ∧ (∀ x, w (τ x) ≤ 1 ↔ w x ≤ 1) := by
  have hl := (Fact.out : l.Prime)
  have hn : l ^ (k + 1) ≠ 0 := pow_ne_zero _ hl.ne_zero
  have : NeZero (l ^ (k + 1)) := ⟨hn⟩
  have hz1 := val_sub_one_lt w hl hw hz.pow_eq_one
  have small : ∀ t : Algebra.adjoin ℤ ({z} : Set K), w ((z - 1) * t) < 1 := fun t => by
    rw [map_mul]
    exact (mul_le_mul' le_rfl (val_le_one w hn hz.pow_eq_one t)).trans_lt (by rwa [mul_one])
  have part1 : ∀ x, w x ≤ 1 → w (τ x - x) < 1 := by
    intro x hx
    obtain ⟨r, s, hs, rfl⟩ := hfrac x
    rcases exists_shape w hw hz r s hs with ⟨r', u, hu, he⟩ | ⟨u, s', hu, hs', he⟩
    · rw [he] at hx ⊢
      have hu1 := val_eq_one w hw hz u hu
      have hu0 : (u : K) ≠ 0 := fun h => by simp [h] at hu1
      obtain ⟨t₁, h₁⟩ := ringHom_adjoin_primitiveRoot_eq_add_mul_sub_one hz τ r'
      obtain ⟨t₂, h₂⟩ := ringHom_adjoin_primitiveRoot_eq_add_mul_sub_one hz τ u
      have hτu : w (τ u) = 1 := by
        rw [h₂, Valuation.map_add_eq_of_lt_left _ (by rw [hu1]; exact small t₂), hu1]
      have hτu0 : τ (u : K) ≠ 0 := fun h => by simp [h] at hτu
      have e : τ ((r' : K) / u) - r' / u =
          (z - 1) * ((t₁ * u - r' * t₂ : Algebra.adjoin ℤ ({z} : Set K)) : K) / (τ u * u) := by
        rw [map_div₀, div_sub_div _ _ hτu0 hu0]
        push_cast
        rw [h₁, h₂]
        ring
      rw [e, map_div₀, Valuation.map_mul w (τ _) _, hτu, hu1, mul_one, div_one]
      exact small _
    · exfalso
      rw [he] at hx
      exact not_le_one w hw hz u s' hu hs' hx
  refine ⟨part1, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · by_contra hx
    push_neg at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hy : w x⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt' hx
    have hτy : w (τ x⁻¹) < 1 := by
      have e : τ x⁻¹ = (τ x⁻¹ - x⁻¹) + x⁻¹ := by ring
      rw [e]
      exact (w.map_add _ _).trans_lt (max_lt (part1 _ hy.le) hy)
    rw [map_inv₀, map_inv₀] at hτy
    have hτx0 : w (τ x) ≠ 0 := by
      rw [Valuation.ne_zero_iff, map_ne_zero]
      exact hx0
    have h₁ := mul_le_mul' h (le_refl (w (τ x))⁻¹)
    rw [mul_inv_cancel₀ hτx0, one_mul] at h₁
    exact absurd hτy (not_lt.mpr h₁)
  · have e : τ x = (τ x - x) + x := by ring
    rw [e]
    exact (w.map_add _ _).trans (max_le (part1 x h).le h)

theorem frac (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ζ : Ω) (x : IntermediateField.adjoin ℚ {ζ}) :
    ∃ r s : Algebra.adjoin ℤ ({IntermediateField.AdjoinSimple.gen ℚ ζ} :
      Set (IntermediateField.adjoin ℚ {ζ})), s ≠ 0 ∧ x = r / s := by
  have : CharZero Ω := algebraRat.charZero (R := Ω)
  have hcoe : ∀ P : Polynomial ℤ,
      ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ ζ) P :
        IntermediateField.adjoin ℚ {ζ}) : Ω) = Polynomial.aeval ζ P := by
    intro P
    have h := Polynomial.aeval_algHom_apply
      (algebraMap (IntermediateField.adjoin ℚ {ζ}) Ω).toIntAlgHom
      (IntermediateField.AdjoinSimple.gen ℚ ζ) P
    simpa using h.symm
  obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff (F := ℚ) (x : Ω)).mp x.2
  obtain ⟨bp, hbp, hP⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) p
  obtain ⟨bq, hbq, hQ⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) q
  have hbp0 : (bp : Ω) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hbp
  have hbq0 : (bq : Ω) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hbq
  have eP : Polynomial.aeval ζ (IsLocalization.integerNormalization (nonZeroDivisors ℤ) p) =
      bp * Polynomial.aeval ζ p := by
    rw [← Polynomial.aeval_map_algebraMap (A := ℚ), hP]
    simp [zsmul_eq_mul]
  have eQ : Polynomial.aeval ζ (IsLocalization.integerNormalization (nonZeroDivisors ℤ) q) =
      bq * Polynomial.aeval ζ q := by
    rw [← Polynomial.aeval_map_algebraMap (A := ℚ), hQ]
    simp [zsmul_eq_mul]
  by_cases hB : Polynomial.aeval ζ q = 0
  · refine ⟨0, 1, one_ne_zero, Subtype.ext ?_⟩
    simp [hpq, hB]
  refine ⟨(bq : Algebra.adjoin ℤ ({IntermediateField.AdjoinSimple.gen ℚ ζ} :
      Set (IntermediateField.adjoin ℚ {ζ}))) *
      ⟨Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ ζ)
        (IsLocalization.integerNormalization (nonZeroDivisors ℤ) p),
        Polynomial.aeval_mem_adjoin_singleton ℤ _⟩,
    (bp : Algebra.adjoin ℤ ({IntermediateField.AdjoinSimple.gen ℚ ζ} :
      Set (IntermediateField.adjoin ℚ {ζ}))) *
      ⟨Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ ζ)
        (IsLocalization.integerNormalization (nonZeroDivisors ℤ) q),
        Polynomial.aeval_mem_adjoin_singleton ℤ _⟩, ?_, ?_⟩
  · intro h
    have h' := congrArg (fun t : Algebra.adjoin ℤ ({IntermediateField.AdjoinSimple.gen ℚ ζ} :
      Set (IntermediateField.adjoin ℚ {ζ})) => ((t : IntermediateField.adjoin ℚ {ζ}) : Ω)) h
    push_cast [Subtype.coe_mk, hcoe] at h'
    rw [eQ] at h'
    exact mul_ne_zero hbp0 (mul_ne_zero hbq0 hB) h'
  · apply Subtype.ext
    push_cast [Subtype.coe_mk, hcoe]
    rw [eP, eQ, hpq]
    field_simp

theorem main : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l k : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ k) → ∀ τ : (IntermediateField.adjoin ℚ {ζ}) ≃ₐ[ℚ] (IntermediateField.adjoin ℚ {ζ}), (∀ x : IntermediateField.adjoin ℚ {ζ}, A.valuation (x : Ω) ≤ 1 → A.valuation ((τ x : Ω) - (x : Ω)) < 1) ∧ (∀ x : IntermediateField.adjoin ℚ {ζ}, A.valuation ((τ x : IntermediateField.adjoin ℚ {ζ}) : Ω) ≤ 1 ↔ A.valuation (x : Ω) ≤ 1) := by
  intro Ω _ _ l k _ A hA ζ hζ τ
  rcases k with _ | k
  · rw [pow_zero, IsPrimitiveRoot.one_right_iff] at hζ
    subst hζ
    have hτ : ∀ x : IntermediateField.adjoin ℚ {(1 : Ω)}, τ x = x := by
      intro x
      have hx : (x : Ω) ∈ (⊥ : IntermediateField ℚ Ω) := by
        rw [← IntermediateField.adjoin_simple_eq_bot_iff.mpr (one_mem _)]
        exact x.2
      obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hx
      have e : x = algebraMap ℚ _ q := Subtype.ext (by simpa using hq.symm)
      rw [e, AlgEquiv.commutes]
    exact ⟨fun x _ => by simp [hτ x], fun x => by simp [hτ x]⟩
  · have : CharZero (IntermediateField.adjoin ℚ {ζ}) :=
      algebraRat.charZero (R := IntermediateField.adjoin ℚ {ζ})
    have hg : IsPrimitiveRoot (IntermediateField.AdjoinSimple.gen ℚ ζ) (l ^ (k + 1)) :=
      IsPrimitiveRoot.of_map_of_injective (f := algebraMap (IntermediateField.adjoin ℚ {ζ}) Ω)
        (by simpa using hζ) (algebraMap (IntermediateField.adjoin ℚ {ζ}) Ω).injective
    have hw : (A.valuation.comap (algebraMap (IntermediateField.adjoin ℚ {ζ}) Ω))
        (l : IntermediateField.adjoin ℚ {ζ}) < 1 := by
      simpa [Valuation.comap_apply] using hA
    obtain ⟨h₁, h₂⟩ := core (A.valuation.comap (algebraMap (IntermediateField.adjoin ℚ {ζ}) Ω))
      hw hg (frac Ω ζ) τ.toRingHom
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · simpa [Valuation.comap_apply] using h₁ x (by simpa [Valuation.comap_apply] using hx)
    · simpa [Valuation.comap_apply] using h₂ x

end GlobalTheory.CycInertial
