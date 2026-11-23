import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorTorusCharacter
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_functor_torus_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' m : ℕ) (α₀ β₀ : kˣ →* ℂˣ) (b : SizeMatrix (Two (Fin a) (Fin a')) fun j : Fin 3 => Fin (blk3 m j))
    (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Two (Fin a) (Fin a') i) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (blk3 m j))
    (t₁ t₂ : kˣ) y,
    cellFunctor f g (detPair k a a' α₀ β₀) (torusPt k m t₁ t₂) y = (cellChar k a a' α₀ β₀ b.1 t₁ t₂ : ℂ) • y := by
  first | exact @GlobalTheory.IndLineGL.CellTorus.cellFunctor_torusPt | exact GlobalTheory.IndLineGL.CellTorus.cellFunctor_torusPt | (intros; apply GlobalTheory.IndLineGL.CellTorus.cellFunctor_torusPt <;> assumption)
