import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantInducedIrreducibleAdmissible
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_induced_irreducible_admissible : GlobalTheory.ThK.KP → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x x' : ℕ) (α β : kˣ →* ℂˣ), GlobalTheory.KSplit.IsSmU α → GlobalTheory.KSplit.IsSmU β →
    (GlobalTheory.ThK.MidJac.detInd x x' α β).IsIrreducible ∧ GlobalTheory.PRep.IsAdmissible (GlobalTheory.ThK.MidJac.detInd x x' α β) := by
  first | exact @GlobalTheory.ThK.MidJac.detInd_irreducible_admissible | exact GlobalTheory.ThK.MidJac.detInd_irreducible_admissible | (intros; apply GlobalTheory.ThK.MidJac.detInd_irreducible_admissible <;> assumption)
