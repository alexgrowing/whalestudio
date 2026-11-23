import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentationRestrictionIntertwinerExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCastRfl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictionSubmoduleFunctionalInjectiveStatement
open scoped TensorProduct
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL GlobalTheory.LocTypeGood
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representation_restriction_intertwiner_exists : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) (e : (Σ i : Fin 3, Fin (blk3 m i)) ≃ Fin n)
    (V V₁ X G₁ : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup X] [Module ℂ X] [Group G₁]
    (I : Representation ℂ (GL (Fin n) k) V) (I₁ : Representation ℂ (GL (Fin m) k) V₁) (π : Representation ℂ (GL (Fin n) k) X)
    (ι : GL (Fin m) k →* G₁), IsSmooth I → Function.Injective ι →
    ∀ (ξ : kˣ × kˣ → ℂ) (l : List ((kˣ × kˣ) × ℂ)), (∀ p ∈ l, ξ p.1 ≠ p.2) →
    ∀ A : V₁ →ₗ[ℂ] Jacquet I (unipRad k e),
      (∀ h w, A (I₁ h w) = jacU e I (midIncl k m h) (A w)) →
      (∀ w, (l.map fun p => jacU e I (torusPt k m p.1.1 p.1.2) - p.2 • (1 : Module.End ℂ (Jacquet I (unipRad k e)))).prod w ∈
        LinearMap.range A) →
    ∀ (M : Submodule ℂ X) (Λ : X →ₗ[ℂ] (G₁ → ℂ)), M ≤ imgSpan I π → (∀ g, ∀ φ ∈ M, π g φ ∈ M) →
      (∀ φ ∈ M, ∀ u ∈ unipRad k e, Λ (π u φ) = Λ φ) →
      (∀ φ ∈ M, ∀ h, Λ (π (leviEmb k e (midIncl k m h)) φ) = rightReg ℂ G₁ ℂ (ι h) (Λ φ)) →
      (∀ φ ∈ M, ∀ t₁ t₂, Λ (π (leviEmb k e (torusPt k m t₁ t₂)) φ) = ξ (t₁, t₂) • Λ φ) →
      ∀ φ ∈ M, Λ φ ∈ imgSpan I₁ ((rightReg ℂ G₁ ℂ).comp ι) := by
  first | exact @GlobalTheory.LocTypeExt.eigenMap_mem_imgSpan | exact GlobalTheory.LocTypeExt.eigenMap_mem_imgSpan | (intros; apply GlobalTheory.LocTypeExt.eigenMap_mem_imgSpan <;> assumption)
