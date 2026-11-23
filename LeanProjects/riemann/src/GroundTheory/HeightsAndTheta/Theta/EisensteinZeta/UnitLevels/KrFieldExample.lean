import Mathlib

open NumberField

namespace GroundTheory.Heights₂.Theta

noncomputable section

section Places

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def IsUnramifiedAtFinitePlaces : Prop :=
  ∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → P.ramificationIdx (𝓞 F) = 1

def IsInertIn (p : Ideal (𝓞 F)) : Prop :=
  p.IsPrime ∧ p ≠ ⊥ ∧ (p.map (algebraMap (𝓞 F) (𝓞 E))).IsPrime

def IsSplitIn (p : Ideal (𝓞 F)) : Prop :=
  p.IsPrime ∧ p ≠ ⊥ ∧ (p.primesOver (𝓞 E)).ncard = 2

end Places

section Example

open Complex

def sqrtNeg3 : ℂ := I * (Real.sqrt 3 : ℝ)

def sqrtNeg7 : ℂ := I * (Real.sqrt 7 : ℝ)

def sqrtNegEleven : ℂ := I * (Real.sqrt 11 : ℝ)

def exE : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {sqrtNeg3, sqrtNeg7, sqrtNegEleven}

def exF : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {((Real.sqrt 21 : ℝ) : ℂ), ((Real.sqrt 33 : ℝ) : ℂ)}

lemma isIntegral_of_sq {x : ℂ} {a : ℚ} (h : x ^ 2 = (a : ℂ)) : IsIntegral ℚ x := by
  refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
  rw [h]
  exact isIntegral_algebraMap (R := ℚ) (A := ℂ) (x := a)

lemma sqrtNeg_sq (n : ℕ) : (I * (Real.sqrt n : ℝ) : ℂ) ^ 2 = ((-n : ℚ) : ℂ) := by
  rw [mul_pow, I_sq, ← ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  push_cast; ring

lemma sqrt_sq_nat (n : ℕ) : ((Real.sqrt n : ℝ) : ℂ) ^ 2 = ((n : ℚ) : ℂ) := by
  rw [← ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  push_cast; ring

instance : FiniteDimensional ℚ exE := by
  unfold exE
  refine IntermediateField.finiteDimensional_adjoin ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · have h := sqrtNeg_sq 3
    simp only [Nat.cast_ofNat] at h
    exact isIntegral_of_sq h
  · have h := sqrtNeg_sq 7
    simp only [Nat.cast_ofNat] at h
    exact isIntegral_of_sq h
  · have h := sqrtNeg_sq 11
    simp only [Nat.cast_ofNat] at h
    exact isIntegral_of_sq h

instance : FiniteDimensional ℚ exF := by
  unfold exF
  refine IntermediateField.finiteDimensional_adjoin ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · have h := sqrt_sq_nat 21
    simp only [Nat.cast_ofNat] at h
    exact isIntegral_of_sq h
  · have h := sqrt_sq_nat 33
    simp only [Nat.cast_ofNat] at h
    exact isIntegral_of_sq h

instance : NumberField exE where

instance : NumberField exF where

lemma sqrt_mul_nat (m n : ℕ) :
    ((Real.sqrt ((m * n : ℕ) : ℝ) : ℝ) : ℂ) =
      -((I * (Real.sqrt m : ℝ)) * (I * (Real.sqrt n : ℝ))) := by
  have h : (I * (Real.sqrt m : ℝ)) * (I * (Real.sqrt n : ℝ)) =
      I ^ 2 * ((Real.sqrt m * Real.sqrt n : ℝ) : ℂ) := by
    push_cast; ring
  rw [h, I_sq, ← Real.sqrt_mul (Nat.cast_nonneg m)]
  push_cast; ring

lemma exF_le_exE : exF ≤ exE := by
  unfold exF
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have h3 : sqrtNeg3 ∈ exE := IntermediateField.subset_adjoin _ _ (by simp)
  have h7 : sqrtNeg7 ∈ exE := IntermediateField.subset_adjoin _ _ (by simp)
  have h11 : sqrtNegEleven ∈ exE := IntermediateField.subset_adjoin _ _ (by simp)
  rcases hx with rfl | rfl
  · have e := sqrt_mul_nat 3 7
    norm_num at e
    rw [SetLike.mem_coe, e]
    exact neg_mem (mul_mem h3 h7)
  · have e := sqrt_mul_nat 3 11
    norm_num at e
    rw [SetLike.mem_coe, e]
    exact neg_mem (mul_mem h3 h11)

instance : Algebra exF exE := (IntermediateField.inclusion exF_le_exE).toRingHom.toAlgebra

end Example

end

end GroundTheory.Heights₂.Theta
