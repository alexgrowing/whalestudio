import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStandardLatticeFormComplexStructureBaseCh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasisApply
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryStandardLattice_form_complexStructure_baseChange_pos : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ), (S.map (Int.cast : ℤ → ℝ)).PosDef → ∀ x : ℝ ⊗[ℤ] GlobalTheory.UnitaryStd.Lat ρ g, x ≠ 0 → 0 < (GlobalTheory.UnitaryStd.form ρ g S).baseChange ℝ ((GlobalTheory.UnitaryStd.cx ρ g).baseChange ℝ x) x := by
  first | exact @GlobalTheory.UnitaryStd.form_cx_baseChange_pos | exact GlobalTheory.UnitaryStd.form_cx_baseChange_pos | (intros; apply GlobalTheory.UnitaryStd.form_cx_baseChange_pos <;> assumption)
