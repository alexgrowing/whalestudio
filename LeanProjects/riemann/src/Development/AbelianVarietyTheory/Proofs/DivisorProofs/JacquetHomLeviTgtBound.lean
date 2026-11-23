import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IndLineGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def evalOne {n m : ℕ} (e : (Σ i : Fin 3, Fin (blk3 m i)) ≃ Fin n) {P P₁ : Type} [AddCommGroup P] [Module ℂ P]
    [AddCommGroup P₁] [Module ℂ P₁] {π : Representation ℂ (GL (Fin n) k) P}
    {σ₁ : Representation ℂ (GL (Fin m) k) P₁} {ξ₁ ξ₂ : kˣ →* ℂˣ} {A : P →ₗ[ℂ] (GL (Fin n) k → P₁)}
    (hA : IsGLIndMap e π σ₁ ξ₁ ξ₂ A) : (jacU e π).IntertwiningMap (leviTgt σ₁ ξ₁ ξ₂) where
  toLinearMap := (twKer π (unipRad k e) 1).liftQ ((LinearMap.proj (1 : GL (Fin n) k)).comp A) (by
    refine Submodule.span_le.2 ?_
    rintro w ⟨u, v, rfl⟩
    have h1 := hA.right (u : GL (Fin n) k) v 1
    have h2 := hA.unip (u : GL (Fin n) k) u.2 v 1
    simp only [one_mul, mul_one] at h1 h2
    simp [h1, h2])
  isIntertwining' l := by
    refine LinearMap.ext fun q => Submodule.Quotient.induction_on _ q fun x => ?_
    have h1 := hA.right (leviEmb k e l) x 1
    have h2 := hA.levi l x 1
    simp only [one_mul, mul_one] at h1 h2
    change A (π (leviEmb k e l) x) 1 = leviTgt σ₁ ξ₁ ξ₂ l (A x 1)
    rw [h1, h2, leviTgt_apply]

theorem evalOne_mk {n m : ℕ} (e : (Σ i : Fin 3, Fin (blk3 m i)) ≃ Fin n) {P P₁ : Type} [AddCommGroup P] [Module ℂ P]
    [AddCommGroup P₁] [Module ℂ P₁] {π : Representation ℂ (GL (Fin n) k) P}
    {σ₁ : Representation ℂ (GL (Fin m) k) P₁} {ξ₁ ξ₂ : kˣ →* ℂˣ} {A : P →ₗ[ℂ] (GL (Fin n) k → P₁)}
    (hA : IsGLIndMap e π σ₁ ξ₁ ξ₂ A) (x : P) :
    (evalOne e hA).toLinearMap (Submodule.Quotient.mk x) = A x 1 := rfl

theorem isGLIndMap_proportional (n m : ℕ) (e : (Σ i : Fin 3, Fin (blk3 m i)) ≃ Fin n) (P P₁ : Type)
    [AddCommGroup P] [Module ℂ P] [AddCommGroup P₁] [Module ℂ P₁] (π : Representation ℂ (GL (Fin n) k) P)
    (σ₁ : Representation ℂ (GL (Fin m) k) P₁) (ξ₁ ξ₂ : kˣ →* ℂˣ)
    (hJ : HomLeOne (jacU e π) (leviTgt σ₁ ξ₁ ξ₂))
    (A A' : P →ₗ[ℂ] (GL (Fin n) k → P₁)) (hA : IsGLIndMap e π σ₁ ξ₁ ξ₂ A)
    (hA' : IsGLIndMap e π σ₁ ξ₁ ξ₂ A') : A = 0 ∨ ∃ c : ℂ, A' = c • A := by
  have key : ∀ (B : P →ₗ[ℂ] (GL (Fin n) k → P₁)) (hB : IsGLIndMap e π σ₁ ξ₁ ξ₂ B) x h,
      B x h = (evalOne e hB).toLinearMap (Submodule.Quotient.mk (π h x)) := by
    intro B hB x h
    rw [evalOne_mk, hB.right, one_mul]
  rcases hJ (evalOne e hA) (evalOne e hA') with h0 | ⟨c, hc⟩
  · left
    refine LinearMap.ext fun x => funext fun h => ?_
    rw [key A hA, h0]
    rfl
  · right
    refine ⟨c, LinearMap.ext fun x => funext fun h => ?_⟩
    rw [key A' hA', hc, LinearMap.smul_apply, LinearMap.smul_apply, Pi.smul_apply, key A hA]

theorem glIndMap_proportional_of_jacquet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (e : (Σ i : Fin 3, Fin (blk3 m i)) ≃ Fin n) (P P₁ : Type) [AddCommGroup P] [Module ℂ P]
    [AddCommGroup P₁] [Module ℂ P₁] (π : Representation ℂ (GL (Fin n) k) P)
    (σ₁ : Representation ℂ (GL (Fin m) k) P₁) (ξ₁ ξ₂ : kˣ →* ℂˣ),
    HomLeOne (jacU e π) (leviTgt σ₁ ξ₁ ξ₂) →
    ∀ A A' : P →ₗ[ℂ] (GL (Fin n) k → P₁), IsGLIndMap e π σ₁ ξ₁ ξ₂ A → IsGLIndMap e π σ₁ ξ₁ ξ₂ A' →
      A = 0 ∨ ∃ c : ℂ, A' = c • A := fun k _ _ _ _ => isGLIndMap_proportional

end GlobalTheory.IndLineGL
