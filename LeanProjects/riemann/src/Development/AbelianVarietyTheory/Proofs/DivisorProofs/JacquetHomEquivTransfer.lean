import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped TensorProduct

namespace GlobalTheory.JacTransport

theorem homLeOne_jacU_of_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (e : (Σ i : Fin 3, Fin (blk3 m i)) ≃ Fin n) (P Q P₁ : Type) [AddCommGroup P] [Module ℂ P]
    [AddCommGroup Q] [Module ℂ Q] [AddCommGroup P₁] [Module ℂ P₁] (π : Representation ℂ (GL (Fin n) k) P)
    (π' : Representation ℂ (GL (Fin n) k) Q) (σ₁ : Representation ℂ (GL (Fin m) k) P₁) (ξ₁ ξ₂ : kˣ →* ℂˣ),
    Nonempty (π.Equiv π') →
    HomLeOne (jac e π') (twist (leviTgt σ₁ ξ₁ ξ₂) (deltaHalf k fun i : Fin 3 => Fin (blk3 m i))⁻¹) →
    HomLeOne (jacU e π) (leviTgt σ₁ ξ₁ ξ₂) := by
  intro k _ _ _ _ n m e P Q P₁ _ _ _ _ _ _ π π' σ₁ ξ₁ ξ₂ ⟨φ⟩ h
  let f := jacMap e φ.toIntertwiningMap
  let g := jacMap e φ.symm.toIntertwiningMap
  have hgf : ∀ x, g (f x) = x := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      show Submodule.Quotient.mk (φ.symm (φ v)) = Submodule.Quotient.mk v
      congr 1
      exact φ.toLinearEquiv.symm_apply_apply v
  have hfg : ∀ x, f (g x) = x := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      show Submodule.Quotient.mk (φ (φ.symm v)) = Submodule.Quotient.mk v
      congr 1
      exact φ.toLinearEquiv.apply_symm_apply v
  let L : Jacquet π (unipRad k e) ≃ₗ[ℂ] Jacquet π' (unipRad k e) :=
    { f.toLinearMap with invFun := g, left_inv := hgf, right_inv := hfg }
  let Φ : (jac e π).Equiv (jac e π') := Representation.Equiv.mk L fun x => f.isIntertwining' x
  have h1 := HomLeOne.of_equiv Φ h
  intro μ μ'
  exact h1 (twistMap μ _) (twistMap μ' _)

end GlobalTheory.JacTransport
