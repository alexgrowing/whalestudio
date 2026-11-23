import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTranslatesLevelAndScalarMod
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jTranslates_level_and_scalar_mod : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ m : ℕ, 0 < m → (∀ g ∈ ({!![(m : ℤ), 0; 0, 1], !![1, 0; 0, (m : ℤ)], !![1, 1; 0, (m : ℤ)]} : Set (Matrix (Fin 2) (Fin 2) ℤ)), Lev X m (X.sl (toGQ g) X.jK)) ∧ ∀ γ : SL(2, ℤ), (∀ g ∈ ({!![(m : ℤ), 0; 0, 1], !![1, 0; 0, (m : ℤ)], !![1, 1; 0, (m : ℤ)]} : Set (Matrix (Fin 2) (Fin 2) ℤ)), X.sl (ofSL γ) (X.sl (toGQ g) X.jK) = X.sl (toGQ g) X.jK) → (en γ 0 1 : ZMod m) = 0 ∧ (en γ 1 0 : ZMod m) = 0 ∧ (en γ 0 0 : ZMod m) = en γ 1 1 := by
  first | exact @GlobalTheory.KZ.ES.Scal.lev_and_scalar | exact GlobalTheory.KZ.ES.Scal.lev_and_scalar | (intros; apply GlobalTheory.KZ.ES.Scal.lev_and_scalar <;> assumption)
