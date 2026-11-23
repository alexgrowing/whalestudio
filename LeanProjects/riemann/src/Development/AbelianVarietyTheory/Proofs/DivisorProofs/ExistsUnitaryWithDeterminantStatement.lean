import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryWithDeterminant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_with_determinant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (u : E), 0 < r → (∀ a b, IsCMField.complexConj E (G a b) = G b a) → G.det ≠ 0 → u * IsCMField.complexConj E u = 1 → ∃ γ : GL (Fin r) E, (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) ∧ (γ : Matrix (Fin r) (Fin r) E).det = u := by
  first | exact @GlobalTheory.UnitDet.main | exact GlobalTheory.UnitDet.main | (intros; apply GlobalTheory.UnitDet.main <;> assumption)
