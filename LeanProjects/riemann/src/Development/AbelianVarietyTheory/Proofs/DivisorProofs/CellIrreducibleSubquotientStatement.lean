import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellIrreducibleSubquotient
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_functor_hom_le_one_of_irreducible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.ThK.KP → ∀ (a a' m : ℕ) (α₀ β₀ : kˣ →* ℂˣ), IsSmoothChar α₀ → IsSmoothChar β₀ →
    ∀ (P₁ : Type) [AddCommGroup P₁] [Module ℂ P₁] (σ₁ : Representation ℂ (GL (Fin m) k) P₁), σ₁.IsIrreducible →
    ∀ (ξ₁ ξ₂ : kˣ →* ℂˣ) (b : SizeMatrix (Two (Fin a) (Fin a')) fun j : Fin 3 => Fin (blk3 m j))
      (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin a) (Fin a') i) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (blk3 m j)),
      (cellMid k α₀ β₀ b.1).IsIrreducible →
      HomLeOne (cellFunctor f g (detPair k a a' α₀ β₀))
        (twist (leviTgt σ₁ ξ₁ ξ₂) (deltaHalf k fun i : Fin 3 => Fin (blk3 m i))⁻¹) := by
  first | exact @GlobalTheory.IndLineGL.homLeOne_cellFunctor_leviTgt | exact GlobalTheory.IndLineGL.homLeOne_cellFunctor_leviTgt | (intros; apply GlobalTheory.IndLineGL.homLeOne_cellFunctor_leviTgt <;> assumption)
