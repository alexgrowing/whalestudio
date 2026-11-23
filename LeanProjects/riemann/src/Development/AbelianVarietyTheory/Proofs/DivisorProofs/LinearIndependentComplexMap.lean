import Mathlib
open Matrix

namespace GlobalTheory

theorem linearIndependent_real_map_of_fieldEmb {E : Type} [Field E] {r n : ℕ} (τ : E →+* ℂ)
    (e : Fin n → Matrix (Fin r) (Fin r) E) (he : LinearIndependent E e) :
    LinearIndependent ℝ (fun i => (e i).map τ) := by
  letI : Algebra E ℂ := τ.toAlgebra
  have h1 : LinearIndependent ℂ (fun i => (1 : ℂ) ⊗ₜ[E] e i) :=
    Module.Flat.linearIndependent_one_tmul he
  let j := (matrixEquivTensor (Fin r) E ℂ).symm
  have hc : ∀ (c : ℂ) (x : TensorProduct E ℂ (Matrix (Fin r) (Fin r) E)),
      j (c • x) = c • j x := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a M =>
      rw [TensorProduct.smul_tmul', smul_eq_mul]
      simp only [j, matrixEquivTensor_apply_symm, mul_smul]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  have h2 : LinearIndependent ℂ (j.toRingEquiv.toAddEquiv.toAddMonoidHom ∘
      fun i => (1 : ℂ) ⊗ₜ[E] e i) :=
    h1.map_of_injective_injective id _ (fun _ h => h)
      (fun m hm => by simpa using hm) (fun c x => hc c x)
  have h3 : (j.toRingEquiv.toAddEquiv.toAddMonoidHom ∘ fun i => (1 : ℂ) ⊗ₜ[E] e i) =
      fun i => (e i).map τ := by
    funext i
    simp only [Function.comp_apply]
    show j ((1 : ℂ) ⊗ₜ[E] e i) = _
    simp only [j, matrixEquivTensor_apply_symm, one_smul]
    rfl
  rw [h3] at h2
  exact h2.restrict_scalars' ℝ

end GlobalTheory
