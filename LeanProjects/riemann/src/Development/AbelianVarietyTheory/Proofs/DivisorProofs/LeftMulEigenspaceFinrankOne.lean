import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory.RegEigen

theorem eig_leftMulMatrix_finrank : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (R Λ : Type) [CommRing R] [CommRing Λ] [Algebra R Λ] (n : ℕ) (b : Module.Basis (Fin n) R Λ) (φ : R →+* O) (τ : Λ →+* O), τ.comp (algebraMap R Λ) = φ → Module.finrank C (eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ) = 1 := by
  intro C _ O _ _ R Λ _ _ _ n b φ τ hτ
  set ψ : R →+* C := (algebraMap O C).comp φ with hψ
  let f : (Fin n → C) → Λ → C := fun w x => ∑ i, ψ (b.repr x i) * w i
  have f_add : ∀ w x y, f w (x + y) = f w x + f w y := by
    intro w x y; simp [f, map_add, add_mul, Finset.sum_add_distrib]
  have f_smul : ∀ w (r : R) x, f w (r • x) = ψ r * f w x := by
    intro w r x; simp [f, map_mul, Finset.mul_sum, mul_assoc]
  have f_basis : ∀ w j, f w (b j) = w j := by
    intro w j; simp [f, Finsupp.single_apply]
  have f_sum : ∀ w (g : Fin n → Λ), f w (∑ i, g i) = ∑ i, f w (g i) := by
    intro w g
    exact map_sum (AddMonoidHom.mk' (f w) (f_add w)) g Finset.univ
  have mem : ∀ w, w ∈ eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ ↔
      ∀ a i, f w (a * b i) = algebraMap O C (τ a) * w i := by
    intro w
    simp only [eig, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, funext_iff]
    refine forall_congr' fun a => forall_congr' fun i => ?_
    simp [f, Matrix.mulVec, dotProduct, Algebra.leftMulMatrix_eq_repr_mul, hψ]
  have hτ' : ∀ r, τ (algebraMap R Λ r) = φ r := fun r => by rw [← hτ]; rfl
  set w0 : Fin n → C := fun i => algebraMap O C (τ (b i)) with hw0
  have f_w0 : ∀ x, f w0 x = algebraMap O C (τ x) := by
    intro x
    conv_rhs => rw [← b.sum_repr x]
    simp [f, hw0, map_sum, Algebra.smul_def, hτ', hψ]
  have f_mul : ∀ w, (∀ a i, f w (a * b i) = algebraMap O C (τ a) * w i) →
      ∀ a x, f w (a * x) = algebraMap O C (τ a) * f w x := by
    intro w h a x
    conv_lhs => rw [← b.sum_repr x, Finset.mul_sum]
    rw [f_sum]
    simp_rw [mul_smul_comm, f_smul, h a]
    simp only [f, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have cmHalfIntegralGenerator_mem_algebraicClosure : w0 ∈ eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ := by
    rw [mem]; intro a i; rw [f_w0]; simp [hw0]
  have w0_ne : w0 ≠ 0 := by
    intro h0
    have := f_w0 1
    rw [h0] at this
    simp [f] at this
  have heq : eig C (fun a : Λ => ((Algebra.leftMulMatrix b a).transpose).map φ) τ = Submodule.span C {w0} := by
    apply le_antisymm
    · intro w hw
      rw [Submodule.mem_span_singleton]
      refine ⟨f w 1, funext fun i => ?_⟩
      have h := f_mul w ((mem w).1 hw) (b i) 1
      rw [mul_one, f_basis] at h
      simp [hw0, h, mul_comm]
    · rw [Submodule.span_le, Set.singleton_subset_iff]; exact cmHalfIntegralGenerator_mem_algebraicClosure
  rw [heq, finrank_span_singleton w0_ne]

end GlobalTheory.RegEigen
