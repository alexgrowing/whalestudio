import Mathlib
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory

section Corner

variable {A : Type} [CommRing A] {Λ : Type} [Ring Λ] [Algebra A Λ]

noncomputable def leftIdealMulAlgHom (A : Type) [CommRing A] {Λ : Type} [Ring Λ] [Algebra A Λ]
    (e : Λ) : Λ →ₐ[A] Module.End A (LinearMap.range (LinearMap.mulRight A e)) where
  toFun l := (LinearMap.mulLeft A l).restrict (by
    rintro _ ⟨y, rfl⟩
    exact ⟨l * y, by simp [mul_assoc]⟩)
  map_one' := by ext p; simp [LinearMap.restrict_apply]
  map_mul' x y := by ext p; simp [LinearMap.restrict_apply, mul_assoc]
  map_zero' := by ext p; simp [LinearMap.restrict_apply]
  map_add' x y := by ext p; simp [LinearMap.restrict_apply, add_mul]
  commutes' c := by ext p; simp [LinearMap.restrict_apply, Algebra.smul_def]

theorem leftIdealMulAlgHom_apply_coe (e l : Λ) (p : LinearMap.range (LinearMap.mulRight A e)) :
    ((leftIdealMulAlgHom A e l p : LinearMap.range (LinearMap.mulRight A e)) : Λ) = l * p := rfl

theorem leftIdealMulAlgHom_injective (e : Λ)
    (h : ∃ (N : ℕ) (a b : Fin N → Λ), ∑ i, a i * e * b i = 1) :
    Function.Injective (leftIdealMulAlgHom A e) := by
  obtain ⟨N, a, b, hab⟩ := h
  rw [injective_iff_map_eq_zero]
  intro l hl
  have h0 : ∀ y : Λ, l * (y * e) = 0 := by
    intro y
    have := leftIdealMulAlgHom_apply_coe (A := A) e l ⟨y * e, y, rfl⟩
    rw [hl] at this
    simpa using this.symm
  calc l = l * ∑ i, a i * e * b i := by rw [hab, mul_one]
    _ = ∑ i, l * (a i * e) * b i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by simp only [mul_assoc]
    _ = 0 := by simp [h0]

theorem exists_mul_eq_mulLeftRight_of_corner (e : Λ)
    (hc : ∀ y : Λ, ∃ c : A, e * y * e = c • e) (t : Λ ⊗[A] Λᵐᵒᵖ) :
    ∃ l : Λ, ∀ y : Λ, AlgHom.mulLeftRight A Λ t (y * e) * e = l * (y * e) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, fun y => by simp⟩
  | tmul a b =>
    obtain ⟨c, hc⟩ := hc b.unop
    refine ⟨c • a, fun y => ?_⟩
    rw [AlgHom.mulLeftRight_apply]
    calc a * (y * e) * b.unop * e = a * y * (e * b.unop * e) := by simp only [mul_assoc]
      _ = c • a * (y * e) := by rw [hc]; simp [mul_assoc]
  | add s t hs ht =>
    obtain ⟨l, hl⟩ := hs
    obtain ⟨m, hm⟩ := ht
    exact ⟨l + m, fun y => by rw [map_add, LinearMap.add_apply, add_mul, hl, hm, add_mul]⟩

theorem leftIdealMulAlgHom_surjective [IsAzumaya A Λ] (e : Λ) (he : IsIdempotentElem e)
    (hc : ∀ y : Λ, ∃ c : A, e * y * e = c • e) :
    Function.Surjective (leftIdealMulAlgHom A e) := by
  intro f
  obtain ⟨t, ht⟩ := (IsAzumaya.bij (R := A) (A := Λ)).2
    ((LinearMap.range (LinearMap.mulRight A e)).subtype ∘ₗ f ∘ₗ
      (LinearMap.mulRight A e).rangeRestrict)
  obtain ⟨l, hl⟩ := exists_mul_eq_mulLeftRight_of_corner e hc t
  refine ⟨l, ?_⟩
  ext ⟨_, y, rfl⟩
  rw [leftIdealMulAlgHom_apply_coe]
  change l * (y * e) = _
  rw [← hl y, ht]
  have h1 : (LinearMap.mulRight A e).rangeRestrict (y * e)
      = ⟨LinearMap.mulRight A e y, y, rfl⟩ := by
    ext; simp [mul_assoc, he.eq]
  simp only [LinearMap.comp_apply, h1, Submodule.subtype_apply]
  obtain ⟨z, hz⟩ := (f ⟨LinearMap.mulRight A e y, y, rfl⟩).2
  rw [← hz]
  simp [mul_assoc, he.eq]

end Corner

theorem azumaya_algEquiv_matrix_of_idempotent :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ]
      [Module.Free A Λ] (n : ℕ), Module.finrank A Λ = n ^ 2 → ∀ e : Λ, IsIdempotentElem e →
      (∀ y : Λ, ∃ c : A, e * y * e = c • e) →
      (∃ (N : ℕ) (a b : Fin N → Λ), ∑ i, a i * e * b i = 1) →
      Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  intro A _ _ Λ _ _ _ _ n hn e he hc hs
  let P := LinearMap.range (LinearMap.mulRight A e)
  let φ : Λ ≃ₐ[A] Module.End A P := AlgEquiv.ofBijective (leftIdealMulAlgHom A e)
    ⟨leftIdealMulAlgHom_injective e hs, leftIdealMulAlgHom_surjective e he hc⟩
  haveI : Module.Projective A P :=
    Module.Projective.of_split P.subtype (LinearMap.mulRight A e).rangeRestrict (by
      ext ⟨_, y, rfl⟩
      simp [mul_assoc, he.eq])
  haveI : Module.Finite A P := Module.Finite.range _
  haveI : Module.Free A P := Module.free_of_flat_of_isLocalRing
  have hr : Module.finrank A P = n := by
    have h1 := φ.toLinearEquiv.finrank_eq
    rw [hn, Module.finrank_linearMap, ← sq] at h1
    exact (Nat.pow_left_injective two_ne_zero h1).symm
  exact ⟨φ.trans (LinearMap.toMatrixAlgEquiv (Module.finBasisOfFinrankEq A P hr))⟩

end GlobalTheory
