import Mathlib

open scoped TensorProduct

noncomputable section

namespace UpperTheory.Lit.HoweDuality

section One

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def Stable (Op : Set (Module.End ℂ M)) (P : Submodule ℂ M) : Prop := ∀ g ∈ Op, ∀ x ∈ P, g x ∈ P

def Gen (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (s : M) : Prop :=
  ∀ P : Submodule ℂ M, Rel ≤ P → Stable Op P → s ∈ P → P = ⊤

def Rad (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) : Prop :=
  ∃ s, Gen Op Rel s ∧ ∀ k ∈ K, ∃ e ∈ Algebra.adjoin ℂ Op, e s = s ∧ e k ∈ Rel

def RadFin (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) : Prop :=
  ∃ s, Gen Op Rel s ∧ ∀ S : Finset M, (∀ k ∈ S, k ∈ K) → ∃ e ∈ Algebra.adjoin ℂ Op, e s = s ∧ ∀ k ∈ S, e k ∈ Rel

example : Rad (∅ : Set (Module.End ℂ ℂ)) ⊥ ⊥ :=
  ⟨1, fun P _ _ h => (Submodule.eq_top_iff'.2 fun x => by simpa using P.smul_mem x h),
    fun k hk => ⟨1, one_mem _, rfl, hk⟩⟩

end One

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀]
  {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

def intersection_update_fsHerm_neg_one (i : ι) (r : M₀ × ∀ j, M j) : M i →ₗ[ℂ] M₀ ⊗[ℂ] (⨂[ℂ] j, M j) :=
  TensorProduct.mk ℂ M₀ _ r.1 ∘ₗ (PiTensorProduct.tprod ℂ (s := M)).toLinearMap r.2 i

omit [Fintype ι] in
theorem position_apply (i : ι) (r : M₀ × ∀ j, M j) (x : M i) :
    intersection_update_fsHerm_neg_one i r x = r.1 ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update r.2 i x) := rfl

def factorOp (i : ι) (g : Module.End ℂ (M i)) : Module.End ℂ (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)) :=
  TensorProduct.map LinearMap.id
    (PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i g))

variable (M₀) in

def part (i : ι) (K : Submodule ℂ (M i)) : Submodule ℂ (M₀ ⊗[ℂ] (⨂[ℂ] j, M j)) :=
  ⨆ r : M₀ × ∀ j, M j, K.map (intersection_update_fsHerm_neg_one i r)

end Tensor

end UpperTheory.Lit.HoweDuality

end
