import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem isMat_calculus : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (Λ : Type) [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (e e' e'' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)), (∀ X X' Y Y', IsMat e e' X Y → IsMat e' e'' X' Y' → IsMat e e'' (X' * X) (Y' * Y)) ∧ (∀ X Y Y', IsMat e e' X Y → IsMat e e' X Y' → Y = Y') ∧ ∀ c : Ainf p O, IsMat e e (c • (1 : Matrix (Fin h) (Fin h) (Ainf p O))) ((inA c : RL p O Λ) • (1 : Matrix (Fin N) (Fin N) (RL p O Λ))) := by
  intro p _ O _ _ _ Λ _ _ N h e e' e''
  refine ⟨?_, ?_, ?_⟩
  · intro X X' Y Y' h1 h2 w
    rw [← Matrix.mulVec_mulVec, h1 w, h2 (Y *ᵥ w), Matrix.mulVec_mulVec]
  · intro X Y Y' h1 h2
    have key : ∀ w, Y *ᵥ w = Y' *ᵥ w := fun w => e'.injective ((h1 w).symm.trans (h2 w))
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    simpa using this
  · intro c w
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      ← map_smul, algebraMap_smul]

end GlobalTheory.DetInv
