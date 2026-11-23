import Mathlib

open NumberField

namespace GlobalTheory.SmallIntegerVanishing

theorem eq_zero_of_small (E : Type) [Field E] [NumberField E] (x : RingOfIntegers E)
    (h : ∀ w : InfinitePlace E, w (x : E) < 1) : x = 0 := by
  classical
  by_contra hx
  have hnn : ∀ (w : InfinitePlace E) (y : E), 0 ≤ w y := fun w y => w.1.nonneg y
  have hne : Algebra.norm ℤ x ≠ 0 := by
    rwa [Ne, Algebra.norm_eq_zero_iff]
  have h1 : (1 : ℝ) ≤ ((|Algebra.norm ℚ (x : E)| : ℚ) : ℝ) := by
    rw [← Algebra.coe_norm_int]
    have : (1 : ℤ) ≤ |Algebra.norm ℤ x| := Int.one_le_abs hne
    exact_mod_cast this
  rw [← NumberField.InfinitePlace.prod_eq_abs_norm] at h1
  obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w0)] at h1
  have hle : ∏ w ∈ Finset.univ.erase w0, w (x : E) ^ w.mult ≤ 1 :=
    Finset.prod_le_one (fun w _ => pow_nonneg (hnn w _) _) fun w _ => pow_le_one₀ (hnn w _) (h w).le
  have hlt : w0 (x : E) ^ w0.mult < 1 :=
    pow_lt_one₀ (hnn w0 _) (h w0) NumberField.InfinitePlace.mult_ne_zero
  have h3 : w0 (x : E) ^ w0.mult * ∏ w ∈ Finset.univ.erase w0, w (x : E) ^ w.mult ≤ w0 (x : E) ^ w0.mult :=
    mul_le_of_le_one_right (pow_nonneg (hnn w0 _) _) hle
  linarith

theorem exists_denominator (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (RingOfIntegers E) (Fin j → E)) (hΛ : Λ.FG) :
    ∃ d : RingOfIntegers E, d ≠ 0 ∧ ∀ y ∈ Λ, ∀ a, ∃ x : RingOfIntegers E,
      (x : E) = (d : E) * y a := by
  classical
  obtain ⟨S, hS⟩ := hΛ
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    (S.biUnion fun g => Finset.univ.image fun a => g a)
  refine ⟨(y : RingOfIntegers E), by exact_mod_cast hy0, ?_⟩
  intro v hv
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem g hg =>
    intro a
    have hint := hy (g a) (Finset.mem_biUnion.mpr ⟨g, hg, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩)
    refine ⟨⟨y • g a, hint⟩, ?_⟩
    simp [zsmul_eq_mul]
  | zero =>
    intro a
    exact ⟨0, by simp⟩
  | add u w _ _ hu hw =>
    intro a
    obtain ⟨x1, h1⟩ := hu a
    obtain ⟨x2, h2⟩ := hw a
    refine ⟨x1 + x2, ?_⟩
    calc ((x1 + x2 : RingOfIntegers E) : E) = (x1 : E) + (x2 : E) := rfl
      _ = _ := by rw [h1, h2, Pi.add_apply, mul_add]
  | smul r u _ hu =>
    intro a
    obtain ⟨x1, h1⟩ := hu a
    refine ⟨r * x1, ?_⟩
    calc ((r * x1 : RingOfIntegers E) : E) = (r : E) * (x1 : E) := rfl
      _ = (r : E) * (((y : RingOfIntegers E) : E) * u a) := by rw [h1]
      _ = ((y : RingOfIntegers E) : E) * (r • u) a := by
        rw [Pi.smul_apply, Algebra.smul_def]
        show _ = _ * ((r : E) * u a)
        ring

theorem main (E : Type) [Field E] [NumberField E] (j : ℕ)
    (Λ : Submodule (RingOfIntegers E) (Fin j → E)) (hΛ : Λ.FG) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ Λ,
      (∀ (w : InfinitePlace E) (a : Fin j), w (y a) < δ) → y = 0 := by
  classical
  obtain ⟨d, hd0, hd⟩ := exists_denominator E j Λ hΛ
  have hdE : (d : E) ≠ 0 := by exact_mod_cast hd0
  have hnn : ∀ (w : InfinitePlace E) (z : E), 0 ≤ w z := fun w z => w.1.nonneg z
  set M : ℝ := ∑ w : InfinitePlace E, w (d : E) with hM
  have hwM : ∀ w : InfinitePlace E, w (d : E) ≤ M := fun w =>
    Finset.single_le_sum (f := fun w : InfinitePlace E => w (d : E)) (fun w _ => hnn w _) (Finset.mem_univ w)
  have hMpos : 0 < M := by
    obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace E))
    exact lt_of_lt_of_le (NumberField.InfinitePlace.pos_iff.mpr hdE) (hwM w0)
  refine ⟨1 / M, by positivity, fun y hy hsmall => ?_⟩
  funext a
  obtain ⟨x, hx⟩ := hd y hy a
  have hx0 : x = 0 := eq_zero_of_small E x fun w => by
    rw [hx, map_mul]
    calc w (d : E) * w (y a) ≤ M * w (y a) := mul_le_mul_of_nonneg_right (hwM w) (hnn w _)
      _ < M * (1 / M) := mul_lt_mul_of_pos_left (hsmall w a) hMpos
      _ = 1 := by field_simp
  have hza : (d : E) * y a = 0 := by rw [← hx, hx0]; rfl
  simpa [hdE] using hza

end GlobalTheory.SmallIntegerVanishing
