import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapOrb

theorem pullLat_mul_eq_mulLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)) (h g : GLw n w) (a : B.Aˣ), (∀ y, ψ ((a : B.A) * y) = h.val *ᵥ ψ y) → pullLat w B ψ (h * g) = GlobalTheory.UnitLemma.mulLat K.O (a : B.A) (pullLat w B ψ g) := by
  intro E _ _ _ w K B n ψ h g a ha
  have hinv : ∀ z, ψ (((a⁻¹ : B.Aˣ) : B.A) * z) = (h⁻¹ : GLw n w).val *ᵥ ψ z := by
    intro z
    have h1 := ha (((a⁻¹ : B.Aˣ) : B.A) * z)
    rw [← mul_assoc, Units.mul_inv, one_mul] at h1
    rw [h1, Matrix.mulVec_mulVec]
    have : ((h⁻¹ : GLw n w).val * h.val) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [this, Matrix.one_mulVec]
  have key : ∀ y, y ∈ pullLat w B ψ (h * g) ↔ ((a⁻¹ : B.Aˣ) : B.A) * y ∈ pullLat w B ψ g := by
    intro y
    show (∀ (c : K.O) (i : Fin n), (((h * g)⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E) ↔
      (∀ (c : K.O) (i : Fin n), ((g⁻¹ : GLw n w).val *ᵥ ψ (c • (((a⁻¹ : B.Aˣ) : B.A) * y))) i ∈
        w.adicCompletionIntegers E)
    have e1 : ∀ c : K.O, ψ (c • (((a⁻¹ : B.Aˣ) : B.A) * y)) = (h⁻¹ : GLw n w).val *ᵥ ψ (c • y) := by
      intro c
      rw [← hinv, Algebra.mul_smul_comm]
    have e2 : ((h * g)⁻¹ : GLw n w).val = (g⁻¹ : GLw n w).val * (h⁻¹ : GLw n w).val := by
      rw [_root_.mul_inv_rev, Units.val_mul]
    simp only [e1, e2, Matrix.mulVec_mulVec]
  ext y
  constructor
  · intro hy
    refine ⟨((a⁻¹ : B.Aˣ) : B.A) * y, (key y).1 hy, ?_⟩
    show (a : B.A) * (((a⁻¹ : B.Aˣ) : B.A) * y) = y
    rw [← mul_assoc, Units.mul_inv, one_mul]
  · rintro ⟨z, hz, rfl⟩
    rw [key]
    show ((a⁻¹ : B.Aˣ) : B.A) * ((a : B.A) * z) ∈ pullLat w B ψ g
    rw [← mul_assoc, Units.inv_mul, one_mul]
    exact hz

end GlobalTheory.KapOrb
