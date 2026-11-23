import Mathlib
import Formalism.LocalToGlobal.HilbertRowConditions.RowPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports
import Formalism.LocalToGlobal.GlobalTheory.BlockActions.SymmetricLevelClausesHold
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIntegralPendingObjectSymmetricFormsLevel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

namespace GlobalTheory.RedPt0

theorem formsMap_of_symmetricComparison_lowerMap_finiteChar : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf), Formalism.L2.Rows.LowerMapTieS Tf → Formalism.L2.Ker.BeOnTie D u → (∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U, (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧ ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ)) → Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u := by
  intro D u Ch chOf Tf hL hB hC
  obtain ⟨P, h4⟩ := GlobalTheory.RedPt0Pend.exists_integralPendingObject_symmetricFormsLevel D u Ch chOf Tf hL hB hC
  exact Formalism.MainNotions.product_first_zeroth_parts.classMap_estimate_of_partial P h4 (Formalism.L2.GlobalTheoryTheory.Br.symmetric_level_clauses_hold D u Ch chOf Tf hL hB)

end GlobalTheory.RedPt0
