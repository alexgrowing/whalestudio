import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt

set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

open PowerSeries Finset

variable {B : Type} [CommRing B]

def ser (g : ℕ → B) (a : B) : B⟦X⟧ := PowerSeries.mk fun n ↦ a ^ n * g n

theorem ser_zero {g : ℕ → B} (h0 : g 0 = 1) : ser g 0 = 1 := by
  ext n
  rcases n with _ | n <;> simp [ser, h0, coeff_one]

theorem ser_add {g : ℕ → B} (hmul : ∀ m n, g m * g n = ((m + n).choose m : B) * g (m + n)) (a b : B) :
    ser g (a + b) = ser g a * ser g b := by
  ext n
  simp only [ser, coeff_mul, coeff_mk, (Commute.all a b).add_pow', Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have e := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have := hmul p.1 p.2
  rw [e] at this
  rw [nsmul_eq_mul]
  linear_combination (-(a ^ p.1 * b ^ p.2)) * this

theorem ser_mul (g : ℕ → B) (a b : B) : ser g (a * b) = rescale a (ser g b) := by
  ext n
  simp only [ser, coeff_rescale, coeff_mk, mul_pow, mul_assoc]

def IsExp (f : B⟦X⟧) : Prop := ∀ m n, coeff m f * coeff n f = ((m + n).choose m : B) * coeff (m + n) f

theorem IsExp.mul {f g : B⟦X⟧} (hf : IsExp f) (hg : IsExp g) : IsExp (f * g) := by
  intro m n
  simp only [coeff_mul]
  have e : ((m + n).choose m : B) * ∑ p ∈ HasAntidiagonal.antidiagonal (m + n), coeff p.1 f * coeff p.2 g =
      ∑ i ∈ HasAntidiagonal.antidiagonal m, ∑ p ∈ HasAntidiagonal.antidiagonal (m + n),
        (p.1.choose i.1 : B) * (p.2.choose i.2 : B) * (coeff p.1 f * coeff p.2 g) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, Nat.add_choose_eq, ← Finset.sum_mul]
    push_cast
    rfl
  rw [e, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.HasAntidiagonal.mem_antidiagonal.1 hi
  rw [Finset.mul_sum]
  refine Finset.sum_of_injOn (fun k : ℕ × ℕ ↦ (i.1 + k.1, i.2 + k.2)) ?_ ?_ ?_ ?_
  · intro k _ l _ h
    simp only [Prod.mk.injEq, add_right_inj] at h
    exact Prod.ext h.1 h.2
  · intro k hk
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 hk
    exact Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp only; omega)
  · intro p hp hn
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h1 : p.1 < i.1
    · simp [Nat.choose_eq_zero_of_lt h1]
    by_cases h2 : p.2 < i.2
    · simp [Nat.choose_eq_zero_of_lt h2]
    refine absurd ⟨(p.1 - i.1, p.2 - i.2), Finset.mem_coe.2 (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp only; omega)), ?_⟩ hn
    exact Prod.ext (by simp only; omega) (by simp only; omega)
  · intro k _
    have a := hf i.1 k.1
    have b := hg i.2 k.2
    simp only
    linear_combination (coeff i.2 g * coeff k.2 g) * a + (((i.1 + k.1).choose i.1 : B) * coeff (i.1 + k.1) f) * b

theorem pre_of_gens (B ι : Type) [CommRing B] (x : ι → B) (g : ι → ℕ → B) (h0 : ∀ i, g i 0 = 1)
    (h1 : ∀ i, g i 1 = x i) (hm : ∀ i n, n ≠ 0 → g i n ∈ Ideal.span (Set.range x))
    (hmul : ∀ i m n, g i m * g i n = ((m + n).choose m : B) * g i (m + n))
    (hrel : ∀ c : ι →₀ B, (c.sum fun i a ↦ a * x i) = 0 →
      (c.prod fun i a ↦ PowerSeries.mk fun n ↦ a ^ n * g i n) = 1) :
    ∃ γ : ℕ → B → B, IsPreDP (Ideal.span (Set.range x)) γ ∧ ∀ i n, γ n (x i) = g i n := by
  classical
  let Φ : (ι →₀ B) → B⟦X⟧ := fun c ↦ c.prod fun i a ↦ ser (g i) a
  let l : (ι →₀ B) →ₗ[B] B := Finsupp.linearCombination B x
  have hl : ∀ c, l c = c.sum fun i a ↦ a * x i := fun c ↦ rfl
  have Φadd : ∀ c c', Φ (c + c') = Φ c * Φ c' := fun c c' ↦
    Finsupp.prod_add_index' (fun i ↦ ser_zero (h0 i)) fun i ↦ ser_add (hmul i)
  have Φ0 : Φ 0 = 1 := Finsupp.prod_zero_index
  have Φs : ∀ i a, Φ (Finsupp.single i a) = ser (g i) a := fun i a ↦
    Finsupp.prod_single_index (ser_zero (h0 i))
  have Φwd : ∀ c c', l c = l c' → Φ c = Φ c' := fun c c' h ↦ by
    have : Φ (c - c') = 1 := hrel _ (by rw [← hl, map_sub, h, sub_self])
    rw [← sub_add_cancel c c', Φadd, this, one_mul]
  have hJ : ∀ y, y ∈ Ideal.span (Set.range x) ↔ ∃ c, l c = y := fun y ↦
    Finsupp.mem_span_range_iff_exists_finsupp
  have Φsm : ∀ a c, Φ (a • c) = rescale a (Φ c) := fun a c ↦ by
    induction c using Finsupp.induction_linear with
    | zero => rw [smul_zero, Φ0, map_one]
    | add c c' h h' => rw [smul_add, Φadd, Φadd, h, h', map_mul]
    | single i b => rw [Finsupp.smul_single, Φs, Φs, smul_eq_mul, ser_mul]
  have key : ∀ c, coeff 0 (Φ c) = 1 ∧ coeff 1 (Φ c) = l c ∧
      (∀ n, n ≠ 0 → coeff n (Φ c) ∈ Ideal.span (Set.range x)) ∧ IsExp (Φ c) := fun c ↦ by
    induction c using Finsupp.induction_linear with
    | zero =>
      rw [Φ0]
      refine ⟨by simp, by simp, fun n hn ↦ by simp [coeff_one, hn], fun m n ↦ ?_⟩
      rcases m with _ | m <;> rcases n with _ | n <;> simp [coeff_one]
    | add c c' h h' =>
      rw [Φadd]
      refine ⟨by rw [coeff_mul]; simp [h.1, h'.1, -coeff_zero_eq_constantCoeff], ?_, fun n hn ↦ ?_,
        h.2.2.2.mul h'.2.2.2⟩
      · rw [coeff_mul, Finset.Nat.antidiagonal_succ]
        simp [h.1, h'.1, h.2.1, h'.2.1, -coeff_zero_eq_constantCoeff, add_comm]
      · rw [coeff_mul]
        refine Ideal.sum_mem _ fun p hp ↦ ?_
        have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
        by_cases h1 : p.1 = 0
        · exact Ideal.mul_mem_left _ _ (h'.2.2.1 _ (by omega))
        · exact Ideal.mul_mem_right _ _ (h.2.2.1 _ h1)
    | single i b =>
      rw [Φs]
      refine ⟨by simp [ser, h0], by simp [ser, h1, l], fun n hn ↦ ?_, fun m n ↦ ?_⟩
      · rw [ser, coeff_mk]; exact Ideal.mul_mem_left _ _ (hm i n hn)
      · simp only [ser, coeff_mk, pow_add]
        linear_combination (b ^ m * b ^ n) * hmul i m n
  let γ : ℕ → B → B := fun n y ↦ if h : ∃ c, l c = y then coeff n (Φ h.choose) else 0
  have hγ : ∀ n c, γ n (l c) = coeff n (Φ c) := fun n c ↦ by
    have h : ∃ c', l c' = l c := ⟨c, rfl⟩
    simp only [γ, dif_pos h, Φwd _ _ h.choose_spec]
  refine ⟨γ, ⟨fun n y hy ↦ dif_neg fun h ↦ hy ((hJ y).2 h), ?_, ?_, ?_, ?_, ?_, ?_⟩, fun i n ↦ ?_⟩
  · intro y hy
    obtain ⟨c, rfl⟩ := (hJ y).1 hy
    rw [hγ, (key c).1]
  · intro y hy
    obtain ⟨c, rfl⟩ := (hJ y).1 hy
    rw [hγ, (key c).2.1]
  · intro n hn y hy
    obtain ⟨c, rfl⟩ := (hJ y).1 hy
    rw [hγ]; exact (key c).2.2.1 n hn
  · intro n y hy z hz
    obtain ⟨c, rfl⟩ := (hJ y).1 hy
    obtain ⟨c', rfl⟩ := (hJ z).1 hz
    simp only [← map_add, hγ, Φadd, coeff_mul]
  · intro n a y hy
    obtain ⟨c, rfl⟩ := (hJ y).1 hy
    rw [← smul_eq_mul, ← map_smul, hγ, hγ, Φsm, coeff_rescale]
  · intro m n y hy
    obtain ⟨c, rfl⟩ := (hJ y).1 hy
    simp only [hγ]
    exact (key c).2.2.2 m n
  · have : x i = l (Finsupp.single i 1) := by simp [l]
    rw [this, hγ, Φs]; simp [ser]

end FubiniStudyChowHeightFormula₂.Adr
