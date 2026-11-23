import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MiracleFlatness.FromQuotTensorToQuotTensor

universe u v

open TensorProduct

namespace PI.UnitaryGroupMassFormula.MF

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

noncomputable def mulMap (𝔞 : Ideal A) : B ⊗[A] 𝔞 →ₗ[B] B :=
  (AlgebraTensorModule.rid A B B).toLinearMap ∘ₗ AlgebraTensorModule.lTensor B B 𝔞.subtype

@[simp] lemma mulMap_tmul (𝔞 : Ideal A) (b : B) (a : 𝔞) : mulMap 𝔞 (b ⊗ₜ a) = (a : A) • b := by
  simp [mulMap]

variable (x : A)

noncomputable def mulX (𝔞 𝔟 : Ideal A) (h1 : ∀ b ∈ 𝔟, x * b ∈ 𝔞) : 𝔟 →ₗ[A] 𝔞 :=
  (LinearMap.mulLeft A x).restrict (p := 𝔟) (q := 𝔞) h1

@[simp] lemma mulX_apply (𝔞 𝔟 : Ideal A) (h1 : ∀ b ∈ 𝔟, x * b ∈ 𝔞) (b : 𝔟) :
    ((mulX x 𝔞 𝔟 h1 b : 𝔞) : A) = x * b := rfl

noncomputable def projQ (𝔞 : Ideal A) : 𝔞 →ₗ[A] (𝔞.map (Ideal.Quotient.mk (Ideal.span {x}))) where
  toFun a := ⟨Ideal.Quotient.mk _ a, Ideal.mem_map_of_mem _ a.2⟩
  map_add' a b := by ext; simp
  map_smul' c a := by
    ext
    simp [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]

end PI.UnitaryGroupMassFormula.MF
