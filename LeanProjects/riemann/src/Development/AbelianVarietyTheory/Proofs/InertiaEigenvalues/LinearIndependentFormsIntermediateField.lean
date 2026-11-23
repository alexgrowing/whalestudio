import Mathlib
open Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem rows_algebraMap_linearIndependent {L0 L : Type} [Field L0] [Field L] [Algebra L0 L]
    {m n : ℕ} (v : Fin m → Fin n → L0) (hv : LinearIndependent L0 v) :
    LinearIndependent L (fun a b => algebraMap L0 L (v a b)) := by
  have h1 : LinearIndependent L (fun a => (1 : L) ⊗ₜ[L0] v a) :=
    Module.Flat.linearIndependent_one_tmul hv
  have h2 := h1.map' (TensorProduct.piScalarRight L0 L L (Fin n)).toLinearMap (LinearEquiv.ker _)
  have he : (fun a b => algebraMap L0 L (v a b)) =
      (TensorProduct.piScalarRight L0 L L (Fin n)).toLinearMap ∘ fun a => (1 : L) ⊗ₜ[L0] v a := by
    funext a b
    simp [TensorProduct.piScalarRight_apply, Algebra.smul_def]
  rw [he]
  exact h2

theorem ksForm_tensor_linearIndependent : ∀ (Ks L0 L WL : Type) [Field Ks] [Field L0] [Field L] [Algebra Ks L0] [Algebra L0 L] [Algebra Ks L]
    [IsScalarTower Ks L0 L] [AddCommGroup WL] [Module L WL] [Module Ks WL] [IsScalarTower Ks L WL]
    (WK : Submodule Ks WL) (n : ℕ) (bs : Fin n → WL), (∀ a, bs a ∈ WK) → Submodule.span Ks (Set.range bs) = WK →
    LinearIndependent L bs → ∀ (ι : L0 ⊗[Ks] WK →ₗ[Ks] WL), (∀ (c : L0) (f : WK), ι (c ⊗ₜ[Ks] f) = algebraMap L0 L c • (f : WL)) →
    ∀ (m : ℕ) (x : Fin m → L0 ⊗[Ks] WK), LinearIndependent L0 x → LinearIndependent L (fun a => ι (x a)) := by
  intro Ks L0 L WL _ _ _ _ _ _ _ _ _ _ _ WK n bs hmem hspan hL ι hι m x hx
  subst hspan
  have hK : LinearIndependent Ks bs := hL.restrict_scalars' Ks
  let bK := Module.Basis.span hK
  let B0 := Algebra.TensorProduct.basis L0 bK
  let M : Fin m → Fin n → L0 := fun a => B0.equivFun (x a)
  have hMli : LinearIndependent L0 M := hx.map' B0.equivFun.toLinearMap B0.equivFun.ker
  have hML := rows_algebraMap_linearIndependent (L := L) M hMli
  have hιs : ∀ (c : L0) (y : L0 ⊗[Ks] (Submodule.span Ks (Set.range bs))),
      ι (c • y) = algebraMap L0 L c • ι y := by
    intro c y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul d f => rw [TensorProduct.smul_tmul', hι, hι, smul_eq_mul, map_mul, mul_smul]
    | add y z hy hz => rw [smul_add, map_add, map_add, hy, hz, smul_add]
  have hx_eq : ∀ a, ι (x a) = ∑ b, algebraMap L0 L (M a b) • bs b := by
    intro a
    conv_lhs => rw [← B0.sum_equivFun (x a)]
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hιs, Algebra.TensorProduct.basis_apply, hι]
    simp [bK, Module.Basis.span_apply, M]
  rw [Fintype.linearIndependent_iff] at hL hML ⊢
  intro g hg
  apply hML g
  funext b
  simp_rw [hx_eq, Finset.smul_sum, smul_smul] at hg
  rw [Finset.sum_comm] at hg
  simp_rw [← Finset.sum_smul] at hg
  have := hL _ hg b
  simpa [Finset.sum_apply] using this

end GlobalTheory
