import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.IrreducibleTensorCharacter

def firstLast {n β : ℕ} (h : β ≤ n) : Fin β ⊕ Fin (n - β) ≃ Fin n :=
  stdSum (Nat.add_sub_cancel' h)

section

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def CentralExponentBoundOver : Prop :=
  ∀ (n β : ℕ) (_ : 1 ≤ β) (hβn : β ≤ n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π₀ : Representation ℂ (GL (Fin n) k) V),
    π₀.IsIrreducible → IsUnitarisable π₀ → IsSmooth π₀ →
    ∀ (S : Type) [AddCommGroup S] [Module ℂ S] (s : Representation ℂ (GL (Fin β) k) S)
      (S' : Type) [AddCommGroup S'] [Module ℂ S'] (s' : Representation ℂ (GL (Fin (n - β)) k) S'),
      (extTensor s s').IsIrreducible →
      IsSubquotient (extTensor s s') (jac₂ (firstLast hβn) π₀) →
      ∀ (ω : kˣ →* ℂˣ) (c : ℝ), HasCentralChar s ω →
        (∀ z : kˣ, ‖(ω z : ℂ)‖ = nabs k z ^ (-((β : ℝ) * c))) →
        c ≤ ((n : ℝ) - (β : ℝ)) / 2

end

def CentralExponentBound : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    CentralExponentBoundOver k

section Sharp

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def tensorChar {G H : Type} [Group G] [Group H] (χ : G →* ℂˣ) (ψ : H →* ℂˣ) :
    (ofChar (χ.comp (MonoidHom.fst G H) * ψ.comp (MonoidHom.snd G H))).IntertwiningMap
      (extTensor (ofChar χ) (ofChar ψ)) where
  toLinearMap := (TensorProduct.lid ℂ ℂ).symm.toLinearMap
  isIntertwining' g := by
    ext
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.lid_symm_apply, extTensor_tmul,
      ofChar_apply, mul_one, MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
    apply (TensorProduct.lid ℂ ℂ).injective
    simp

end Sharp

end GlobalTheory.IndefiniteRowSideFullHecke.IrreducibleTensorCharacter
