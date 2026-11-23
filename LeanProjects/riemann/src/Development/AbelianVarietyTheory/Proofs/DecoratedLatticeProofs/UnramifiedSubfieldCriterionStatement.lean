import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedSubfieldCriterion
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_subfield_criterion : ∀ (l : ℕ) [Fact l.Prime] (F : Subfield ℂ_[l]) (N : ℕ), 0 < N → (∀ x ∈ F, ‖x‖ < 1 → ‖x‖ ≤ ‖(l : ℂ_[l])‖) → (∀ x ∈ F, ‖x‖ ≤ 1 → ‖x ^ (l ^ N) - x‖ < 1) → F ≤ MaximalUnramifiedExtension l := by
  first | exact @GlobalTheory.SubKur.le_Kur | exact GlobalTheory.SubKur.le_Kur | (intros; apply GlobalTheory.SubKur.le_Kur <;> assumption)
