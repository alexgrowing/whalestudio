import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact

namespace GlobalTheory.WeightPart

variable {S ι : Type} [Ring S] [Fintype ι] {ε : ι → S} {w : ι → ℤ}

def dg (ε : ι → S) (w : ι → ℤ) (x : S) : S := ∑ a, ∑ b, if w a = w b then ε a * x * ε b else 0

theorem ext_sand (he : CompleteOrthogonalIdempotents ε) {x y : S} (h : ∀ a b, ε a * x * ε b = ε a * y * ε b) : x = y := by
  have e : ∀ z : S, z = ∑ a, ∑ b, ε a * z * ε b := fun z => by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, he.complete, mul_one, one_mul]
  rw [e x, e y]
  simp only [h]

theorem sand_mul (he : CompleteOrthogonalIdempotents ε) (x y : S) (a b : ι) :
    ε a * (x * y) * ε b = ∑ c, (ε a * x * ε c) * (ε c * y * ε b) := by
  have e : ∀ c, (ε a * x * ε c) * (ε c * y * ε b) = ε a * x * ε c * (y * ε b) := fun c => by
    rw [mul_assoc (ε c) y, ← mul_assoc _ (ε c) (y * ε b), mul_assoc _ (ε c) (ε c), (he.idem c).eq]
  simp only [e]
  rw [← Finset.sum_mul, ← Finset.mul_sum, he.complete]
  simp only [mul_one, mul_assoc]

theorem sand_dg (he : CompleteOrthogonalIdempotents ε) (x : S) (a b : ι) :
    ε a * dg ε w x * ε b = if w a = w b then ε a * x * ε b else 0 := by
  classical
  rw [dg, Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single a, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_eq_single b]
  · split_ifs
    · rw [← mul_assoc, ← mul_assoc, (he.idem a).eq, mul_assoc _ (ε b), (he.idem b).eq]
    · simp
  · intro c _ hc
    split_ifs
    · rw [mul_assoc, mul_assoc _ (ε c), he.ortho hc, mul_zero, mul_zero]
    · simp
  · simp
  · intro c _ hc
    rw [Finset.mul_sum, Finset.sum_eq_zero, zero_mul]
    intro d _
    split_ifs
    · rw [← mul_assoc, ← mul_assoc, he.ortho hc.symm, zero_mul, zero_mul]
    · simp
  · simp

theorem dg_mul_dg (he : CompleteOrthogonalIdempotents ε) {x y : S} (h : x * y = 1)
    (hx : ∀ a b, w a < w b → ε a * x * ε b = 0) (hy : ∀ a b, w a < w b → ε a * y * ε b = 0) :
    dg ε w x * dg ε w y = 1 := by
  refine ext_sand he fun a b => ?_
  by_cases hab : w a = w b
  · rw [← h, sand_mul he, sand_mul he]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sand_dg he, sand_dg he]
    rcases lt_trichotomy (w a) (w c) with h1 | h1 | h1
    · rw [if_neg h1.ne, hx a c h1, zero_mul, zero_mul]
    · rw [if_pos h1, if_pos (h1 ▸ hab)]
    · rw [if_neg h1.ne', hy c b (hab ▸ h1), zero_mul, mul_zero]
  · rw [mul_one, he.ortho (fun e => hab (congrArg w e)), sand_mul he]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [sand_dg he, sand_dg he]
    by_cases h1 : w a = w c
    · rw [if_neg (show ¬ w c = w b from h1 ▸ hab), mul_zero]
    · rw [if_neg h1, zero_mul]

theorem exists_weightPart : ∀ {S ι : Type} [Ring S] [Fintype ι] (st : S →+ S) (ε : ι → S) (w : ι → ℤ) (τ : ι → ι), (∀ x y, st (x * y) = st y * st x) → (∀ x, st (st x) = x) → CompleteOrthogonalIdempotents ε → (∀ a, st (ε a) = ε (τ a)) → (∀ a, w (τ a) = -w a) → (∀ a, τ (τ a) = a) → ∀ x y : S, x * y = 1 → y * x = 1 → st x = y → (∀ a b, w a < w b → ε a * x * ε b = 0) → (∀ a b, w a < w b → ε a * y * ε b = 0) → ∃ m m' : S, m * m' = 1 ∧ m' * m = 1 ∧ st m = m' ∧ (∀ a b, w a ≠ w b → ε a * m * ε b = 0) ∧ (∀ a b, w a ≠ w b → ε a * m' * ε b = 0) ∧ x * m' - 1 ∈ raise ε w 0 ∧ ∀ S₀ : Subring S, (∀ a, ε a ∈ S₀) → x ∈ S₀ → y ∈ S₀ → m ∈ S₀ ∧ m' ∈ S₀ := by
  intro S ι _ _ st ε w τ hst hss he hε hw hτ x y hxy hyx hs hx hy
  have hm : ∀ z a b, w a ≠ w b → ε a * dg ε w z * ε b = 0 := fun z a b h => by rw [sand_dg he, if_neg h]
  have h1 := dg_mul_dg he hxy hx hy
  refine ⟨dg ε w x, dg ε w y, h1, dg_mul_dg he hyx hy hx, ?_, hm x, hm y, ?_, ?_⟩
  · have key : ∀ z a b, ε a * st z * ε b = st (ε (τ b) * z * ε (τ a)) := fun z a b => by
      rw [hst, hst, hε, hε, hτ, hτ, mul_assoc]
    refine ext_sand he fun a b => ?_
    rw [key, sand_dg he, sand_dg he, ← hs, key, hw, hw]
    by_cases h : w a = w b
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun e => h (neg_inj.1 e).symm), map_zero]
  · intro a b hab
    have hab' : w a ≤ w b := by simpa using hab
    rw [← h1, ← sub_mul, sand_mul he]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases h : w c = w b
    · rw [mul_sub, sub_mul, sand_dg he]
      split_ifs with h2
      · rw [sub_self, zero_mul]
      · rw [hx a c (lt_of_le_of_ne (h ▸ hab') h2), sub_self, zero_mul]
    · rw [hm y c b h, mul_zero]
  · intro S₀ h0 hx0 hy0
    have : ∀ z ∈ S₀, dg ε w z ∈ S₀ := fun z hz =>
      sum_mem fun a _ => sum_mem fun b _ => by
        split_ifs
        · exact mul_mem (mul_mem (h0 a) hz) (h0 b)
        · exact zero_mem _
    exact ⟨this x hx0, this y hy0⟩

end GlobalTheory.WeightPart
