import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_mod_f_of_surj (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A)
    (hsurj : ∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f})
    (x : A' ⊗[A] A') :
    ∃ (c : A) (v : A' ⊗[A] A'), x = algebraMap A (A' ⊗[A] A') c + algebraMap A (A' ⊗[A] A') f * v := by
  set P : A' ⊗[A] A' → Prop := fun x => ∃ (c : A) (v : A' ⊗[A] A'),
    x = algebraMap A (A' ⊗[A] A') c + algebraMap A (A' ⊗[A] A') f * v with hP
  have hadd : ∀ x y, P x → P y → P (x + y) := by
    rintro x y ⟨c₁, v₁, rfl⟩ ⟨c₂, v₂, rfl⟩
    exact ⟨c₁ + c₂, v₁ + v₂, by rw [map_add]; ring⟩
  have hmul : ∀ x y, P x → P y → P (x * y) := by
    rintro x y ⟨c₁, v₁, rfl⟩ ⟨c₂, v₂, rfl⟩
    refine ⟨c₁ * c₂, algebraMap A (A' ⊗[A] A') c₁ * v₂ + v₁ * algebraMap A (A' ⊗[A] A') c₂
      + algebraMap A (A' ⊗[A] A') f * v₁ * v₂, ?_⟩
    rw [map_mul]; ring
  have himg : ∀ (g : A' →ₐ[A] A' ⊗[A] A') (a' : A'), P (g a') := by
    intro g a'
    obtain ⟨a, ha⟩ := hsurj a'
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp ha
    refine ⟨a, g y, ?_⟩
    have : a' = algebraMap A A' a + y * algebraMap A A' f := by rw [hy]; ring
    rw [this, map_add, map_mul, AlgHom.commutes, AlgHom.commutes]; ring
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a b =>
    have h : a ⊗ₜ[A] b = (Algebra.TensorProduct.includeLeft (S := A) a) *
        (Algebra.TensorProduct.includeRight b) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [h]
    exact hmul _ _ (himg _ _) (himg _ _)
  | add x y hx hy => exact hadd _ _ hx hy

theorem etale_diag_complement (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A) :
    (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) →
    (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) →
    ∃ e u : A' ⊗[A] A', (∀ a : A', (a ⊗ₜ[A] (1 : A') - (1 : A') ⊗ₜ[A] a) * e = 0) ∧
      algebraMap A (A' ⊗[A] A') f * u = 1 - e := by
  intro hsurj hinj
  obtain ⟨t, ht, ht1⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := A) (S := A')).1
    inferInstance
  obtain ⟨c, v, hcv⟩ := tensor_mod_f_of_surj A A' f hsurj (1 - t)
  have h0 : algebraMap A A' c + algebraMap A A' f * Algebra.TensorProduct.lmul' A v = 0 := by
    have := congrArg (Algebra.TensorProduct.lmul' A (S := A')) hcv
    rw [map_sub, map_one, ht1, sub_self, map_add, map_mul, AlgHom.commutes, AlgHom.commutes] at this
    exact this.symm
  have hc : algebraMap A A' c ∈ Ideal.span {algebraMap A A' f} := by
    rw [Ideal.mem_span_singleton']
    exact ⟨-Algebra.TensorProduct.lmul' A v, by linear_combination -h0⟩
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp (hinj c hc)
  refine ⟨t, algebraMap A (A' ⊗[A] A') c' + v, ?_, ?_⟩
  · intro a
    rw [← neg_sub, neg_mul, ht a, neg_zero]
  · rw [hcv, ← hc', map_mul]; ring

end GlobalTheory
