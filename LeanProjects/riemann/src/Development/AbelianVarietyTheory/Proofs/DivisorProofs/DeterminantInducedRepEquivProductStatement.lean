import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantInducedRepEquivProduct
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellFunctorTorusCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedCharIntertwiningUnif
open scoped TensorProduct
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_induced_rep_equiv_product : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ),
    Nonempty ((GlobalTheory.ThK.MidJac.detInd a a' χ₁ χ₂).Equiv (prod₂ (detRep (Fin a) χ₁) (detRep (Fin a') χ₂))) := by
  first | exact @GlobalTheory.DetIndProd.detInd_equiv_prod₂ | exact GlobalTheory.DetIndProd.detInd_equiv_prod₂ | (intros; apply GlobalTheory.DetIndProd.detInd_equiv_prod₂ <;> assumption)
