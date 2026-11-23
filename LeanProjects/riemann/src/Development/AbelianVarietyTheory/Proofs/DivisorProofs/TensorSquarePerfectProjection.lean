import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

theorem tensorSquare_perfectProjection (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (A : Type) [CommRing A] [Algebra k A] (π : A →ₐ[k] A) :
    ((∀ a : A, IsNilpotent (a - π a)) ∧ ∀ a : A, ∃ b : A, π a = π b ^ p) → ((∀ a : A ⊗[k] A, IsNilpotent (a - Algebra.TensorProduct.map π π a)) ∧ ∀ a : A ⊗[k] A, ∃ b : A ⊗[k] A, Algebra.TensorProduct.map π π a = Algebra.TensorProduct.map π π b ^ p) := by
  rintro ⟨h1, h2⟩
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hpA : ((p : ℕ) : A ⊗[k] A) = 0 := by
    rw [← map_natCast (algebraMap k (A ⊗[k] A)) p, CharP.cast_eq_zero, map_zero]
  refine ⟨fun a => ?_, fun a => ?_⟩
  · rw [← mem_nilradical]
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [Algebra.TensorProduct.map_tmul]
      have e : a ⊗ₜ[k] b - π a ⊗ₜ[k] π b = (a - π a) ⊗ₜ[k] b + π a ⊗ₜ[k] (b - π b) := by
        rw [TensorProduct.sub_tmul, TensorProduct.tmul_sub]; abel
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · have : (a - π a) ⊗ₜ[k] b = Algebra.TensorProduct.includeLeft (S := k) (B := A) (a - π a) * ((1 : A) ⊗ₜ[k] b) := by
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        rw [this]
        exact Ideal.mul_mem_right _ _ (mem_nilradical.2 ((h1 a).map _))
      · have : π a ⊗ₜ[k] (b - π b) = ((π a) ⊗ₜ[k] (1 : A)) * Algebra.TensorProduct.includeRight (R := k) (A := A) (b - π b) := by
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        rw [this]
        exact Ideal.mul_mem_left _ _ (mem_nilradical.2 ((h1 b).map _))
    | add x y hx hy =>
      rw [map_add, add_sub_add_comm]
      exact Ideal.add_mem _ hx hy
  · induction a using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp [hp0]⟩
    | tmul a b =>
      obtain ⟨a', ha⟩ := h2 a
      obtain ⟨b', hb⟩ := h2 b
      refine ⟨a' ⊗ₜ[k] b', ?_⟩
      simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_pow, ha, hb]
    | add x y hx hy =>
      obtain ⟨u, hu⟩ := hx
      obtain ⟨v, hv⟩ := hy
      refine ⟨u + v, ?_⟩
      rw [map_add, map_add, hu, hv, ← frobRing_apply hpA, ← frobRing_apply hpA, ← frobRing_apply hpA, map_add]

end GlobalTheory
