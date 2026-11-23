import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt

set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA PowerSeries

namespace GlobalTheory.PDA.Gen

variable {B : Type} [CommRing B]

def IsExpType (f : PowerSeries B) : Prop :=
  ∀ m n, coeff m f * coeff n f = ((m + n).choose m : B) * coeff (m + n) f

theorem isExpType_one : IsExpType (1 : PowerSeries B) := by
  intro m n
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h1 : m ≠ 0 := hm.ne'
    have h2 : m + n ≠ 0 := by omega
    simp [coeff_one, h1, h2]

theorem isExpType_mul {f g : PowerSeries B} (hf : IsExpType f) (hg : IsExpType g) :
    IsExpType (f * g) := by
  intro m n
  simp only [coeff_mul, Finset.sum_mul_sum]
  have hV : ((m + n).choose m : B) * ∑ z ∈ Finset.HasAntidiagonal.antidiagonal (m + n), coeff z.1 f * coeff z.2 g
      = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, ∑ z ∈ Finset.HasAntidiagonal.antidiagonal (m + n),
          ((z.1.choose x.1 * z.2.choose x.2 : ℕ) : B) * (coeff z.1 f * coeff z.2 g) := by
    rw [Finset.mul_sum, Finset.sum_comm' (t' := Finset.HasAntidiagonal.antidiagonal (m + n)) (s' := fun _ ↦ Finset.HasAntidiagonal.antidiagonal m)
      (fun _ _ ↦ Iff.rfl)]
    refine Finset.sum_congr rfl fun z hz ↦ ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hz
    rw [← Finset.sum_mul, ← Nat.cast_sum, ← hz, Nat.add_choose_eq]
  rw [hV]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have key : ∀ y ∈ Finset.HasAntidiagonal.antidiagonal n, coeff x.1 f * coeff x.2 g * (coeff y.1 f * coeff y.2 g) =
      (((x.1 + y.1).choose x.1 * (x.2 + y.2).choose x.2 : ℕ) : B) *
        (coeff (x.1 + y.1) f * coeff (x.2 + y.2) g) := by
    intro y _
    calc coeff x.1 f * coeff x.2 g * (coeff y.1 f * coeff y.2 g)
        = (coeff x.1 f * coeff y.1 f) * (coeff x.2 g * coeff y.2 g) := by ring
      _ = _ := by rw [hf, hg]; push_cast; ring
  refine Finset.sum_bij_ne_zero (fun y _ _ ↦ (x.1 + y.1, x.2 + y.2)) ?_ ?_ ?_ ?_
  · intro y hy _
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hy ⊢
    omega
  · intro y₁ hy₁ _ y₂ hy₂ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (by omega) (by omega)
  · intro z hz hz0
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hz
    have h1 : x.1 ≤ z.1 := by
      by_contra h
      apply hz0
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
    have h2 : x.2 ≤ z.2 := by
      by_contra h
      apply hz0
      rw [Nat.choose_eq_zero_of_lt (n := z.2) (by omega)]
      simp
    have hy : (z.1 - x.1, z.2 - x.2) ∈ Finset.HasAntidiagonal.antidiagonal n := by
      rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega
    have he : (x.1 + (z.1 - x.1), x.2 + (z.2 - x.2)) = z := Prod.ext (by simp; omega) (by simp; omega)
    refine ⟨(z.1 - x.1, z.2 - x.2), hy, ?_, he⟩
    rw [key _ hy, Nat.add_sub_cancel' h1, Nat.add_sub_cancel' h2]
    exact hz0
  · intro y hy _
    exact key y hy

def ser (g : ℕ → B) (a : B) : PowerSeries B := mk fun n ↦ a ^ n * g n

theorem ser_zero {g : ℕ → B} (h0 : g 0 = 1) : ser g 0 = 1 := by
  ext n
  rcases n with _ | n <;> simp [ser, coeff_one, h0]

theorem ser_add {g : ℕ → B} (hm : ∀ m n, g m * g n = ((m + n).choose m : B) * g (m + n)) (a b : B) :
    ser g (a + b) = ser g a * ser g b := by
  ext n
  rw [coeff_mul]
  simp only [ser, coeff_mk]
  rw [(Commute.all a b).add_pow', Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
  have := hm k.1 k.2
  rw [hk] at this
  rw [show a ^ k.1 * g k.1 * (b ^ k.2 * g k.2) = a ^ k.1 * b ^ k.2 * (g k.1 * g k.2) by ring, this, nsmul_eq_mul]
  ring

theorem ser_smul {g : ℕ → B} (a b : B) : ser g (a * b) = rescale a (ser g b) := by
  ext n
  simp [ser, coeff_rescale, mul_pow]
  ring

theorem isExpType_ser {g : ℕ → B} (hm : ∀ m n, g m * g n = ((m + n).choose m : B) * g (m + n)) (a : B) :
    IsExpType (ser g a) := by
  intro m n
  simp only [ser, coeff_mk]
  calc a ^ m * g m * (a ^ n * g n) = a ^ (m + n) * (g m * g n) := by ring
    _ = _ := by rw [hm]; ring

theorem coeff_zero_mul' (p q : PowerSeries B) : coeff 0 (p * q) = coeff 0 p * coeff 0 q := by
  simp [coeff_mul]

theorem coeff_one_mul' (p q : PowerSeries B) :
    coeff 1 (p * q) = coeff 1 p * coeff 0 q + coeff 0 p * coeff 1 q := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_succ]
  simp [add_comm]

theorem coeff_mul_mem {J : Ideal B} {p q : PowerSeries B} (hp : ∀ n, n ≠ 0 → coeff n p ∈ J)
    (hq : ∀ n, n ≠ 0 → coeff n q ∈ J) (n : ℕ) (hn : n ≠ 0) : coeff n (p * q) ∈ J := by
  rw [coeff_mul]
  refine Ideal.sum_mem _ fun k hk ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hk
  by_cases h : k.1 = 0
  · exact J.mul_mem_left _ (hq _ (by omega))
  · exact J.mul_mem_right _ (hp _ h)

section Gen

variable {ι : Type} (x : ι → B) (g : ι → ℕ → B)

def E (c : ι →₀ B) : PowerSeries B := c.prod fun i a ↦ ser (g i) a

def L (c : ι →₀ B) : B := c.sum fun i a ↦ a * x i

def gam (n : ℕ) (y : B) : B := by
  classical exact if h : ∃ c, L x c = y then coeff n (E g h.choose) else 0

variable {x g}

theorem L_add (c c' : ι →₀ B) : L x (c + c') = L x c + L x c' :=
  Finsupp.sum_add_index' (fun _ ↦ zero_mul _) (fun _ _ _ ↦ add_mul _ _ _)

theorem L_sub (c c' : ι →₀ B) : L x (c - c') = L x c - L x c' :=
  Finsupp.sum_sub_index (fun _ _ _ ↦ sub_mul _ _ _)

theorem L_smul (a : B) (c : ι →₀ B) : L x (a • c) = a * L x c := by
  unfold L
  rw [Finsupp.sum_smul_index (fun _ ↦ zero_mul _), Finsupp.mul_sum]
  simp only [mul_assoc]

theorem L_single (i : ι) (a : B) : L x (Finsupp.single i a) = a * x i :=
  Finsupp.sum_single_index (zero_mul _)

theorem L_zero : L x (0 : ι →₀ B) = 0 := Finsupp.sum_zero_index

theorem E_zero : E g (0 : ι →₀ B) = 1 := Finsupp.prod_zero_index

theorem E_add (h0 : ∀ i, g i 0 = 1) (hm : ∀ i m n, g i m * g i n = ((m + n).choose m : B) * g i (m + n))
    (c c' : ι →₀ B) : E g (c + c') = E g c * E g c' :=
  Finsupp.prod_add_index' (fun i ↦ ser_zero (h0 i)) (fun i a b ↦ ser_add (hm i) a b)

theorem E_single (h0 : ∀ i, g i 0 = 1) (i : ι) (a : B) : E g (Finsupp.single i a) = ser (g i) a :=
  Finsupp.prod_single_index (ser_zero (h0 i))

theorem E_smul (h0 : ∀ i, g i 0 = 1)
    (hm : ∀ i m n, g i m * g i n = ((m + n).choose m : B) * g i (m + n)) (a : B) (c : ι →₀ B) : E g (a • c) = rescale a (E g c) := by
  induction c using Finsupp.induction with
  | zero => rw [smul_zero, E_zero, map_one]
  | single_add i b f _ _ ih =>
    rw [smul_add, Finsupp.smul_single, smul_eq_mul, E_add h0 hm, E_add h0 hm, E_single h0, E_single h0, ih,
      ser_smul, map_mul]

theorem mem_span_iff {y : B} : y ∈ Ideal.span (Set.range x) ↔ ∃ c, L x c = y := by
  simp only [Ideal.span, Finsupp.mem_span_range_iff_exists_finsupp, smul_eq_mul, L]

theorem E_props (h0 : ∀ i, g i 0 = 1) (h1 : ∀ i, g i 1 = x i)
    (hJ : ∀ i n, n ≠ 0 → g i n ∈ Ideal.span (Set.range x))
    (hm : ∀ i m n, g i m * g i n = ((m + n).choose m : B) * g i (m + n)) (c : ι →₀ B) :
    coeff 0 (E g c) = 1 ∧ coeff 1 (E g c) = L x c ∧
      (∀ n, n ≠ 0 → coeff n (E g c) ∈ Ideal.span (Set.range x)) ∧ IsExpType (E g c) := by
  induction c using Finsupp.induction with
  | zero =>
    rw [E_zero, L_zero]
    refine ⟨by simp, by simp [coeff_one], fun n hn ↦ by simp [coeff_one, hn], isExpType_one⟩
  | single_add i a f _ _ ih =>
    obtain ⟨ih0, ih1, ihJ, ihE⟩ := ih
    rw [E_add h0 hm, E_single h0, L_add, L_single]
    have s0 : coeff 0 (ser (g i) a) = 1 := by simp [ser, h0]
    have s1 : coeff 1 (ser (g i) a) = a * x i := by simp [ser, h1]
    refine ⟨by rw [coeff_zero_mul', s0, ih0, one_mul], by rw [coeff_one_mul', s0, s1, ih0, ih1]; ring,
      coeff_mul_mem (fun n hn ↦ by simp only [ser, coeff_mk]; exact Ideal.mul_mem_left _ _ (hJ i n hn)) ihJ,
      isExpType_mul (isExpType_ser (hm i) a) ihE⟩

variable (x g) in
theorem E_eq (h0 : ∀ i, g i 0 = 1) (hm : ∀ i m n, g i m * g i n = ((m + n).choose m : B) * g i (m + n))
    (hE : ∀ c : ι →₀ B, L x c = 0 → E g c = 1) {c c' : ι →₀ B} (h : L x c = L x c') :
    E g c = E g c' := by
  calc E g c = E g ((c - c') + c') := by rw [sub_add_cancel]
    _ = E g c' := by rw [E_add h0 hm, hE _ (by rw [L_sub, h, sub_self]), one_mul]

theorem gam_L (h0 : ∀ i, g i 0 = 1) (hm : ∀ i m n, g i m * g i n = ((m + n).choose m : B) * g i (m + n))
    (hE : ∀ c : ι →₀ B, L x c = 0 → E g c = 1) (n : ℕ) (c : ι →₀ B) :
    gam x g n (L x c) = coeff n (E g c) := by
  have h : ∃ c', L x c' = L x c := ⟨c, rfl⟩
  unfold gam
  rw [dif_pos h, E_eq x g h0 hm hE h.choose_spec]

end Gen

end GlobalTheory.PDA.Gen

namespace GlobalTheory.PDA

open Gen in

theorem exists_isPreDividedPowers_of_generators₂ : ∀ (B ι : Type) [CommRing B] (x : ι → B) (g : ι → ℕ → B), (∀ i, g i 0 = 1) →
    (∀ i, g i 1 = x i) → (∀ i n, n ≠ 0 → g i n ∈ Ideal.span (Set.range x)) →
    (∀ i m n, g i m * g i n = ((m + n).choose m : B) * g i (m + n)) →
    (∀ c : ι →₀ B, (c.sum fun i a ↦ a * x i) = 0 → (c.prod fun i a ↦ PowerSeries.mk fun n ↦ a ^ n * g i n) = 1) →
    ∃ γ : ℕ → B → B, IsPreDP (Ideal.span (Set.range x)) γ ∧ ∀ i n, γ n (x i) = g i n := by
  intro B ι _ x g h0 h1 hJ hm hE'
  have hE : ∀ c : ι →₀ B, L x c = 0 → E g c = 1 := hE'
  have P := E_props h0 h1 hJ hm
  have G := gam_L h0 hm hE
  refine ⟨gam x g, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n y hy
    unfold gam
    rw [dif_neg fun h ↦ hy (mem_span_iff.2 h)]
  · intro y hy
    obtain ⟨c, rfl⟩ := mem_span_iff.1 hy
    rw [G]; exact (P c).1
  · intro y hy
    obtain ⟨c, rfl⟩ := mem_span_iff.1 hy
    rw [G]; exact (P c).2.1
  · intro n hn y hy
    obtain ⟨c, rfl⟩ := mem_span_iff.1 hy
    rw [G]; exact (P c).2.2.1 n hn
  · intro n y hy z hz
    obtain ⟨c, rfl⟩ := mem_span_iff.1 hy
    obtain ⟨c', rfl⟩ := mem_span_iff.1 hz
    rw [← L_add, G, E_add h0 hm, coeff_mul]
    simp only [G]
  · intro n a y hy
    obtain ⟨c, rfl⟩ := mem_span_iff.1 hy
    rw [← L_smul, G, G, E_smul h0 hm, coeff_rescale]
  · intro m n y hy
    obtain ⟨c, rfl⟩ := mem_span_iff.1 hy
    rw [G, G, G]; exact (P c).2.2.2 m n
  · intro i n
    have hx : x i = L x (Finsupp.single i 1) := by rw [L_single, one_mul]
    rw [hx, G, E_single h0]
    simp [ser]

end GlobalTheory.PDA
