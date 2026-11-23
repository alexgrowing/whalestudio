import Mathlib

open Polynomial

attribute [local instance 100] LieRing.ofAssociativeRing

namespace GlobalTheory.AugmentationNilpotent

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem isNilpotent_of_trace_pow [CharZero K] [FiniteDimensional K V] (x : Module.End K V)
    (h : ∀ n : ℕ, LinearMap.trace K V (x ^ (n + 1)) = 0) : IsNilpotent x := by
  have hp : ∀ a : K[X], LinearMap.trace K V (aeval x (a * X)) = 0 := by
    intro a
    induction a using Polynomial.induction_on' with
    | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq, add_zero]
    | monomial n c =>
      rw [monomial_mul_X, aeval_monomial, ← Algebra.smul_def, map_smul, h, smul_zero]
  obtain ⟨q, hq, hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd x.charpoly
    x.charpoly_monic.ne_zero 0
  set k := rootMultiplicity 0 x.charpoly
  rw [C_0, sub_zero] at hq hnd
  have hc : IsCoprime ((X : K[X]) ^ (k + 1)) q :=
    ((irreducible_X.coprime_iff_not_dvd).2 hnd).pow_left
  obtain ⟨a, b, hab⟩ := hc
  have h0 : aeval x (X ^ k * q) = 0 := by rw [← hq]; exact x.aeval_self_charpoly
  have hidem : IsIdempotentElem (aeval x (a * X ^ (k + 1))) := by
    unfold IsIdempotentElem
    rw [← map_mul]
    have : a * X ^ (k + 1) * (a * X ^ (k + 1)) = a * X ^ (k + 1) - (a * b * X) * (X ^ k * q) := by
      linear_combination (a * X ^ (k + 1)) * hab
    rw [this, map_sub, map_mul _ (a * b * X), h0, mul_zero, sub_zero]
  have he : aeval x (a * X ^ (k + 1)) = 0 := by
    apply (LinearMap.IsIdempotentElem.trace_eq_zero_iff hidem).1
    rw [pow_succ, ← mul_assoc]
    exact hp _
  refine ⟨k, ?_⟩
  have : (X : K[X]) ^ k = X ^ k * (a * X ^ (k + 1)) + b * (X ^ k * q) := by
    linear_combination (-X ^ k) * hab
  have h2 := congrArg (aeval x) this
  rw [map_add, map_mul _ (X ^ k), he, map_mul _ b, h0, map_pow, aeval_X] at h2
  simpa using h2

variable {Γ : Type} [Group Γ] (ρ : Representation K Γ V) (H : Subgroup Γ)

def aug : Submodule K (Module.End K V) := Submodule.span K {x | ∃ s ∈ H, x = ρ s - 1}

theorem sub_one_mem {s : Γ} (hs : s ∈ H) : ρ s - 1 ∈ aug ρ H := Submodule.subset_span ⟨s, hs, rfl⟩

theorem aug_mul {x y : Module.End K V} (hx : x ∈ aug ρ H) (hy : y ∈ aug ρ H) :
    x * y ∈ aug ρ H := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    have : (ρ s - 1) * (ρ t - 1) = (ρ (s * t) - 1) - (ρ s - 1) - (ρ t - 1) := by
      rw [map_mul]; noncomm_ring
    rw [this]
    exact sub_mem (sub_mem (sub_one_mem ρ H (mul_mem hs ht)) (sub_one_mem ρ H hs))
      (sub_one_mem ρ H ht)
  | zero_left => simp
  | zero_right => simp
  | add_left x y z _ _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
  | add_right x y z _ _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | smul_left r x y _ _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h
  | smul_right r x y _ _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h

def augLie : LieSubalgebra K (Module.End K V) :=
  { aug ρ H with
    lie_mem' := fun {x y} hx hy => by
      rw [LieRing.of_associative_ring_bracket]
      exact (aug ρ H).sub_mem (aug_mul ρ H hx hy) (aug_mul ρ H hy hx) }

end GlobalTheory.AugmentationNilpotent
