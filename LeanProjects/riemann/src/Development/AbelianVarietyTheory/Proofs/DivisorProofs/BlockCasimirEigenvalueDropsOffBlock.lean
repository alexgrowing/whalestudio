import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR
variable {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]

theorem casDrop_term (F : ι → ι → Module.End ℂ M) (hF : IsGl F) (a b j k : ι) :
    F a b * F b a * F j k = F j k * (F a b * F b a) + (F a b * (if a = j then F b k else 0) - F a b * (if k = b then F j a else 0))
      + ((if b = j then F a k else 0) * F b a - (if k = a then F j b else 0) * F b a) := by
  have h1 := hF b a j k
  have h2 := hF a b j k
  have e1 : F b a * F j k = F j k * F b a + ((if a = j then F b k else 0) - (if k = b then F j a else 0)) := by
    rw [← h1]; abel
  have e2 : F a b * F j k = F j k * F a b + ((if b = j then F a k else 0) - (if k = a then F j b else 0)) := by
    rw [← h2]; abel
  calc F a b * F b a * F j k = F a b * (F b a * F j k) := mul_assoc _ _ _
    _ = F a b * F j k * F b a + F a b * ((if a = j then F b k else 0) - (if k = b then F j a else 0)) := by
        rw [e1, mul_add, mul_assoc]
    _ = _ := by rw [e2]; simp only [add_mul, sub_mul, mul_sub, mul_assoc]; abel

theorem cas_mul_off (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (hF : IsGl F) (j k : ι) (hj : s j = false)
    (hk : s k = true) :
    cas s F * F j k = F j k * cas s F + (2 : ℂ) • (∑ b, if s b = false then F j b * F b k else 0)
      - (2 : ℂ) • (∑ b, if s b = true then F j b * F b k else 0)
      + (((Finset.univ.filter fun a => s a = true).card : ℂ) - ((Finset.univ.filter fun a => s a = false).card : ℂ)) • F j k := by
  have hjk : j ≠ k := by intro h; rw [h, hk] at hj; exact Bool.noConfusion hj
  have sw : ∀ a, F a k * F j a = F j a * F a k - F j k := by
    intro a
    have h := hF a k j a
    rw [if_neg (Ne.symm hjk), if_pos rfl] at h
    calc F a k * F j a = (F a k * F j a - F j a * F a k) + F j a * F a k := by abel
      _ = _ := by rw [h]; abel
  have cnt : ∀ c : Bool, (∑ a, if s a = c then F a k * F j a else 0)
      = (∑ a, if s a = c then F j a * F a k else 0) - ((Finset.univ.filter fun a => s a = c).card : ℂ) • F j k := by
    intro c
    have : (∑ a, if s a = c then F a k * F j a else 0)
        = ∑ a, ((if s a = c then F j a * F a k else 0) - (if s a = c then F j k else 0)) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases h : s a = c
      · simp only [if_pos h, sw]
      · simp [h]
    rw [this, Finset.sum_sub_distrib]
    congr 1
    rw [← Finset.sum_filter, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have S1 : ∑ a, ∑ b, (if s a = s b then F a b * (if a = j then F b k else 0) else 0)
      = ∑ b, if s b = false then F j b * F b k else 0 := by
    rw [Finset.sum_eq_single j]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [hj]; by_cases h : s b <;> simp [h]
    · intro a _ ha; simp [ha]
    · simp
  have S2 : ∑ a, ∑ b, (if s a = s b then F a b * (if k = b then F j a else 0) else 0)
      = ∑ a, if s a = true then F a k * F j a else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single k]
    · rw [hk]; simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  have S3 : ∑ a, ∑ b, (if s a = s b then (if b = j then F a k else 0) * F b a else 0)
      = ∑ a, if s a = false then F a k * F j a else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single j]
    · rw [hj]; simp
    · intro b _ hb; simp [hb]
    · simp
  have S4 : ∑ a, ∑ b, (if s a = s b then (if k = a then F j b else 0) * F b a else 0)
      = ∑ b, if s b = true then F j b * F b k else 0 := by
    rw [Finset.sum_eq_single k]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [hk]; by_cases h : s b <;> simp [h]
    · intro a _ ha; simp [Ne.symm ha]
    · simp
  have expand : ∀ a b, (if s a = s b then F a b * F b a else 0) * F j k
      = (if s a = s b then F j k * (F a b * F b a) else 0)
        + ((if s a = s b then F a b * (if a = j then F b k else 0) else 0)
          - (if s a = s b then F a b * (if k = b then F j a else 0) else 0))
        + ((if s a = s b then (if b = j then F a k else 0) * F b a else 0)
          - (if s a = s b then (if k = a then F j b else 0) * F b a else 0)) := by
    intro a b
    by_cases h : s a = s b
    · simp only [if_pos h]; exact casDrop_term F hF a b j k
    · simp [h]
  unfold cas
  simp only [Finset.sum_mul, expand, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [S1, S2, S3, S4, cnt, cnt]
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  simp only [two_smul, sub_smul]
  abel

end GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem cas_drop : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M), ∀ (α β x ω : ℂ) (y : ι → M), IsGl F → (∀ a b, qop F α β a b = 0) →
    (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = x • y a) → (∀ a, cas s F (y a) = ω • y a) →
    ∀ j, s j = false → cas s F (∑ b, F j b (y b)) = (ω - 4 * x + 2 * α + ((Finset.univ.filter fun a => s a = true).card : ℂ)
      - ((Finset.univ.filter fun a => s a = false).card : ℂ)) • ∑ b, F j b (y b) := by
  intro ι M _ _ _ _ s F α β x ω y hF hq hy0 hyA hω j hj
  set r : ℂ := ((Finset.univ.filter fun a => s a = true).card : ℂ)
  set r' : ℂ := ((Finset.univ.filter fun a => s a = false).card : ℂ)
  set T : ι → Module.End ℂ M := fun b => ∑ c, if s c = true then F j c * F c b else 0 with hT

  have quad : ∀ b, s b = true → (∑ c, if s c = false then F j c * F c b else 0) = α • F j b - T b := by
    intro b hb
    have hjb : j ≠ b := by intro h; rw [h, hb] at hj; exact Bool.noConfusion hj
    have h := hq j b
    simp only [qop, if_neg hjb, sub_zero] at h
    have split : (∑ c, F j c * F c b) = (∑ c, if s c = false then F j c * F c b else 0) + T b := by
      rw [hT, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      cases s c <;> simp
    rw [split] at h
    calc (∑ c, if s c = false then F j c * F c b else 0) = ((∑ c, if s c = false then F j c * F c b else 0) + T b - α • F j b)
          + α • F j b - T b := by abel
      _ = α • F j b - T b := by rw [h]; abel

  have term : ∀ b, cas s F (F j b (y b)) = (ω + 2 * α + r - r') • F j b (y b) - (4 : ℂ) • T b (y b) := by
    intro b
    cases hb : s b
    · simp [hT, hy0 b hb]
    · have h := cas_mul_off s F hF j b hj hb
      rw [quad b hb] at h
      have h' := congrArg (fun L : Module.End ℂ M => L (y b)) h
      simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply] at h'
      rw [h', hω b, map_smul]
      module
  have sumT : (∑ b, T b (y b)) = x • ∑ b, F j b (y b) := by
    have : ∀ b, T b (y b) = ∑ c, if s c = true then F j c (F c b (y b)) else 0 := by
      intro b
      simp only [hT, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs <;> rfl
    simp only [this]
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    cases hc : s c
    · simp [hy0 c hc]
    · simp only [if_true]
      rw [← map_sum, hyA c hc, map_smul]
  rw [map_sum]
  simp only [term]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum, sumT, smul_smul, ← sub_smul]
  congr 1
  ring

end GlobalTheory.HoweR
