import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvertibleUnitaryAdelicMatrixOfRationalUnitary
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isInvertibleUnitaryAdelicMatrix_of_rational_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E), γ.det ≠ 0 → (∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G x y) → IsUA (IsCMField.complexConj E) G (ratM (maximalRealSubfield E) γ) := by
  first | exact @GlobalTheory.RatUnit.isUA_ratM | exact GlobalTheory.RatUnit.isUA_ratM | (intros; apply GlobalTheory.RatUnit.isUA_ratM <;> assumption)
